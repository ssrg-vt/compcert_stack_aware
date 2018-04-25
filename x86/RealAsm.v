Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import List.
Require Import ZArith.
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.
Require Import RawAsm.

Section WITHMEMORYMODEL.

  Existing Instance mem_accessors_default.
  Context `{memory_model_ops: Mem.MemoryModelOps}.
  Context `{external_calls_ops : !ExternalCallsOps mem}.
  Context `{enable_builtins: !EnableBuiltins mem}.

Section WITHGE.
  Variable ge : Genv.t Asm.fundef unit.

  Definition exec_instr f i rs (m: mem) :=
    let sz := Ptrofs.repr (Asm.instr_size i) in 
    match i with
    | Pallocframe fi ofs_ra =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.sub (Ptrofs.repr (align (frame_size fi) 8)) (Ptrofs.repr (size_chunk Mptr)))) in
      Next (nextinstr (rs #RAX <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr))) #RSP <- sp) sz) m
    | Pfreeframe fsz ofs_ra =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.sub (Ptrofs.repr (align (Z.max 0 fsz) 8)) (Ptrofs.repr (size_chunk Mptr))) in
      Next (nextinstr (rs#RSP <- sp) sz) m
    | Pload_parent_pointer rd z =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.repr (align (Z.max 0 z) 8)) in
      Next (nextinstr (rs#rd <- sp) sz) m
    | Pcall_s id sg =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))) in
      match maybe_storev Mptr m sp (Val.offset_ptr rs#PC sz) with
      | None => Stuck
      | Some m2 =>
        Next (rs#RA <- (Val.offset_ptr rs#PC sz)
                #PC <- (Genv.symbol_address ge id Ptrofs.zero)
                #RSP <- sp) m2
      end
    | Pcall_r r sg =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))) in
      match maybe_storev Mptr m sp (Val.offset_ptr rs#PC sz) with
      | None => Stuck
      | Some m2 =>
        Next (rs#RA <- (Val.offset_ptr rs#PC sz)
                #PC <- (rs r)
                #RSP <- sp) m2
      end
    | Pret =>
      match Mem.loadv Mptr m rs#RSP with
      | None => Stuck
      | Some ra =>
        let sp := Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)) in
        Next (rs #RSP <- sp
                 #PC <- ra
                 #RA <- Vundef) m
      end
    | _ => Asm.exec_instr nil ge f i rs m
    end.
  
  Inductive step  : state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
        exec_instr f i rs m = Next rs' m' ->
        step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
        eval_builtin_args ge rs (rs RSP) m args vargs ->
        external_call ef ge vargs m t vres m' ->
        forall BUILTIN_ENABLED: builtin_enabled ef,
          rs' = nextinstr_nf
                  (set_res res vres
                           (undef_regs (map preg_of (destroyed_by_builtin ef)) rs))
                  (Ptrofs.repr (Asm.instr_size (Pbuiltin ef args res))) ->
          step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
        rs PC = Vptr b Ptrofs.zero ->
        Genv.find_funct_ptr ge b = Some (External ef) ->
        extcall_arguments (rs # RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)))) m (ef_sig ef) args ->
        forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
          ra (LOADRA: Mem.loadv Mptr m (rs RSP) = Some ra)
          (SP_NOT_VUNDEF: rs RSP <> Vundef)
          (RA_NOT_VUNDEF: ra <> Vundef), 
          external_call ef ge args m t res m' ->
          rs' = (set_pair (loc_external_result (ef_sig ef)) res
                          (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil)
                                      (undef_regs (map preg_of destroyed_at_call) rs)))
                  #PC <- ra
                  #RA <- Vundef
                  #RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr))) ->
          step (State rs m) t (State rs' m').

End WITHGE.

  Inductive initial_state_gen (prog: Asm.program) (rs: regset) m: state -> Prop :=
  | initial_state_gen_intro:
      forall m1 bstack m2 m3 m4
        (MALLOC: Mem.alloc (Mem.push_new_stage m) 0 (Mem.stack_limit) = (m1,bstack))
        (MDROP: Mem.drop_perm m1 bstack 0 (Mem.stack_limit) Writable = Some m2)
        (MRSB: Mem.record_stack_blocks m2 (make_singleton_frame_adt' bstack frame_info_mono 0) = Some m3)
        (STORE_RETADDR: maybe_storev Mptr m3 (Vptr bstack (Ptrofs.repr (Mem.stack_limit - size_chunk Mptr))) Vnullptr = Some m4),
        let ge := Genv.globalenv prog in
        let rs0 :=
            rs # PC <- (Genv.symbol_address ge prog.(prog_main) Ptrofs.zero)
               #RA <- Vnullptr
               #RSP <- (Val.offset_ptr (Vptr bstack (Ptrofs.repr (Mem.stack_limit))) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr)))) in
        initial_state_gen prog rs m (State rs0 m4).

  Inductive initial_state (prog: Asm.program) (rs: regset) (s: state): Prop :=
  | initial_state_intro: forall m,
      Genv.init_mem prog = Some m ->
      initial_state_gen prog rs m s ->
      initial_state prog rs s.

  Definition semantics_gen prog rs m :=
    Semantics step (initial_state_gen prog rs m) final_state (Genv.globalenv prog).

  Definition semantics prog rs :=
    Semantics step (initial_state prog rs) final_state (Genv.globalenv prog).

End WITHMEMORYMODEL.
