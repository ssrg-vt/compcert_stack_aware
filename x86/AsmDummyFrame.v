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
Require Import AsmFacts.


Section WITHEXTERNALCALLS.
Context `{external_calls_prf: ExternalCalls}.

Variable init_sp: val.


Existing Instance mem_accessors_default.

Section RELSEM.


  Notation "'do' X <- A ; B" := (match A with Some X => B | None => Stuck end)
                                  (at level 200, X ident, A at level 100, B at level 200).

  Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => Stuck end)
                                     (at level 200, X ident, Y ident, A at level 100, B at level 200).

  Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => Stuck end)
                                         (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200).

  Notation " 'check' A ; B" := (if A then B else Stuck)
                                 (at level 200, A at level 100, B at level 200).



  Definition exec_instr {F V} (ge: Genv.t F V) (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
    match i with
      Pfreeframe sz ofs_ra =>
      do ra <- Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_ra);
        match rs#RSP with
        | Vptr stk ofs =>
          check (check_top_frame m (Some stk) sz);
            do m' <- Mem.free m stk 0 sz;
            check (check_init_sp_in_stack init_sp m');
            do m' <- Mem.record_stack_blocks m (Build_frame_adt nil 0 (list_norepet_nil _) (Zle_refl _));
            Next (nextinstr (rs#RSP <-
                               (match parent_pointer m with
                                | None => init_sp
                                | Some (sp,_) => Vptr sp Ptrofs.zero
                                end) #RA <- ra)) m'
        | _ => Stuck
        end
    | _ => Asm.exec_instr init_sp ge f i rs m
    end.

  Inductive step (ge: genv) : state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
        exec_instr ge f i rs m = Next rs' m' ->
        step ge (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m' m'',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
        eval_builtin_args ge rs (rs RSP) m args vargs ->
        external_call ef ge vargs (Mem.push_new_stage m) t vres m' ->
        Mem.unrecord_stack_block m' = Some m'' ->
        forall BUILTIN_ENABLED: builtin_enabled ef,
          no_rsp_builtin_preg res ->
          rs' = nextinstr_nf
                  (set_res res vres
                           (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
          step ge (State rs m) t (State rs' m'')
  | exec_step_external:
      forall b ef args res rs m t rs' m' m'',
        rs PC = Vptr b Ptrofs.zero ->
        Genv.find_funct_ptr ge b = Some (External ef) ->
        extcall_arguments rs m (ef_sig ef) args ->
        forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
          (RA_TYPE: Val.has_type (rs RA) Tptr)
          (SP_NOT_VUNDEF: rs RSP <> Vundef)
          (RA_NOT_VUNDEF: rs RA <> Vundef),
          external_call ef ge args m t res m' ->
          Mem.unrecord_stack_block m' = Some m'' ->
          no_rsp_pair (loc_external_result (ef_sig ef)) ->
          rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) (undef_regs (map preg_of destroyed_at_call) rs))) #PC <- (rs RA) #RA <- Vundef ->
          step ge (State rs m) t (State rs' m'').

End RELSEM.

Definition semantics (p: Asm.program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

End WITHEXTERNALCALLS.