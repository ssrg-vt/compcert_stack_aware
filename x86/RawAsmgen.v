Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import List.
Require Import ZArith.
(* Require Memimpl. *)
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.
Require Import AsmFacts.

Section WITHMEMORYMODEL.
  
  Context `{memory_model: Mem.MemoryModel }.
  Existing Instance inject_perm_upto_writable.

  Program Definition frame_info_mono: frame_info :=
    {|
      frame_size := Mem.stack_limit;
      frame_perm := fun o => Public;
      frame_link := nil;
    |}.

  Inductive mono_initial_state {F V} (prog: program F V): state -> Prop :=
  |mis_intro:
     forall rs m m1 bstack m2 m3,
       initial_state prog (State rs m) ->
       Mem.alloc m 0 (Mem.stack_limit) = (m1,bstack) ->
       Mem.drop_perm m1 bstack 0 (Mem.stack_limit) Writable = Some m2 ->
       Mem.record_stack_blocks m2 (bstack::nil,Some frame_info_mono,0) m3 ->
       mono_initial_state prog (State rs m3).

  Existing Instance mem_accessors_default.

  Context `{external_calls_ops : !ExternalCallsOps mem }.
  Context `{!EnableBuiltins mem}.
  Existing Instance symbols_inject_instance.
  Context `{external_calls_props : !ExternalCallsProps mem
                                    (memory_model_ops := memory_model_ops)
                                    }.

  Definition current_offset (v: val) :=
    match v with
      Vptr stk ofs => Ptrofs.unsigned ofs
    | _ => Mem.stack_limit
    end.

  Definition offset_after_alloc (p: Z) fi :=
    (p - align (Z.max 0 (frame_size fi)) 8).

   Definition exec_instr {F V} (ge: Genv.t F V) f i' rs (m: mem) :=
    match i' with
    | (i,isz) =>
      match i with
      | Pallocframe fi ofs_ra ofs_link =>
        let curofs := current_offset (rs RSP) in
        let sp := Vptr (Genv.genv_next ge) (Ptrofs.repr (offset_after_alloc curofs fi)) in
        match Mem.storev Mptr m (Val.offset_ptr sp ofs_link) rs#RSP with
        | None => Stuck
        | Some m2 =>
          match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_ra) rs#RA with
          | None => Stuck
          | Some m3 =>
            Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp) (Ptrofs.repr (si_size isz))) m3
          end
        end
      | Pfreeframe sz ofs_ra ofs_link =>
        match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
        | None => Stuck
        | Some ra =>
          match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_link) with
          | None => Stuck
          | Some sp =>
            Next (nextinstr (rs#RSP <- sp #RA <- ra) (Ptrofs.repr (si_size isz))) m
          end
        end
      | _ => Asm.exec_instr ge f i' rs m
      end
    end.

  Inductive step (ge: Genv.t Asm.fundef unit) : state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
        exec_instr ge f i rs m = Next rs' m' ->
        step ge (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m' sz,
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res,sz) ->
        eval_builtin_args ge rs (rs RSP) m args vargs ->
        external_call ef ge vargs m t vres m' ->
        forall BUILTIN_ENABLED: builtin_enabled ef,
          rs' = nextinstr_nf
                  (set_res res vres
                           (undef_regs (map preg_of (destroyed_by_builtin ef)) rs))
                  (Ptrofs.repr (si_size sz)) ->
          step ge (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
        rs PC = Vptr b Ptrofs.zero ->
        Genv.find_funct_ptr ge b = Some (External ef) ->
        extcall_arguments rs m (ef_sig ef) args ->
        forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
          (RA_TYPE: Val.has_type (rs RA) Tptr)
          (SP_NOT_VUNDEF: rs RSP <> Vundef)
          (RA_NOT_VUNDEF: rs RA <> Vundef), 
          external_call ef ge args m t res m' ->
          rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) (undef_regs (map preg_of destroyed_at_call) rs))) #PC <- (rs RA) #RA <- Vundef ->
          step ge (State rs m) t (State rs' m').


  Definition mono_semantics (p: Asm.program) :=
    Semantics step (mono_initial_state p) final_state (Genv.globalenv p).
  
  
End WITHMEMORYMODEL.

