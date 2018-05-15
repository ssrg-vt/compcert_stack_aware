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

Section WITHMEMORYMODEL.

  Existing Instance mem_accessors_default.
  Context `{memory_model_ops: Mem.MemoryModelOps}.
  Context `{external_calls_ops : !ExternalCallsOps mem}.
  Context `{enable_builtins: !EnableBuiltins mem}.

Section WITHGE.
  Variable ge : Genv.t Asm.fundef unit.

  Definition exec_instr f i rs (m: mem) :=
    let isz := Ptrofs.repr (Asm.instr_size i) in
    match i with
    | Pallocframe sz pubrange ofs_ra =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (align sz 8))) in
      match Mem.storev Mptr m (Val.offset_ptr sp ofs_ra) rs#RA with
      | None => Stuck
      | Some m2 =>
        Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp) isz) m2
      end
    | Pfreeframe sz ofs_ra =>
      match Mem.loadbytesv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
      | None => Stuck
      | Some ra =>
        let sp := Val.offset_ptr (rs RSP) (Ptrofs.repr (align (Z.max 0 sz) 8)) in
        Next (nextinstr (rs#RSP <- sp #RA <- ra) isz) m
      end
    | Pload_parent_pointer rd z =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.repr (align (Z.max 0 z) 8)) in
      Next (nextinstr (rs#rd <- sp) isz) m
    | Pcall ros sg =>
      let addr := eval_ros ge ros rs in
      match Genv.find_funct ge addr with
        | Some _ =>
          Next (rs#RA <- (Val.offset_ptr rs#PC isz) #PC <- addr) m
        | _ => Stuck
      end
    | Pret =>
      if check_ra_after_call ge (rs#RA) then Next (rs#PC <- (rs#RA) #RA <- Vundef) m else Stuck
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
      forall b ef args res rs m t rs' m2 m',
        rs PC = Vptr b Ptrofs.zero ->
        Genv.find_funct_ptr ge b = Some (External ef) ->
        forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
          (RA_TYPE: Val.has_type (rs RA) Tptr)
          (SP_NOT_VUNDEF: rs RSP <> Vundef)
          (RA_NOT_VUNDEF: rs RA <> Vundef)
          (SZRA: Mem.storev Mptr m (Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))))
                            (rs RA) = Some m2)
          (ARGS: extcall_arguments rs m2 (ef_sig ef) args),
          external_call ef ge args m2 t res m' ->
          ra_after_call ge (rs#RA) ->
          rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) (undef_regs (map preg_of destroyed_at_call) rs))) #PC <- (rs RA) #RA <- Vundef ->
          step (State rs m) t (State rs' m').

End WITHGE.

Lemma align_Mptr_pos:
  0 <= align (size_chunk Mptr) 8.
Proof.
  etransitivity. 2: apply align_le. generalize (size_chunk_pos Mptr); omega. omega.
Qed.

Program Definition frame_info_mono: frame_info :=
  {|
    frame_size := Mem.stack_limit + align (size_chunk Mptr) 8;
    frame_perm := fun o => Public;
    (* frame_size_pos := proj1 Mem.stack_limit_range; *)
  |}.
Next Obligation.
  generalize Mem.stack_limit_range align_Mptr_pos; omega.
Qed.
  
  Inductive initial_state_gen (prog: Asm.program) (rs: regset) m: state -> Prop :=
  | initial_state_gen_intro:
      forall m1 bstack m2 m3 bmain
        (MALLOC: Mem.alloc (Mem.push_new_stage m) 0 (Mem.stack_limit + align (size_chunk Mptr) 8) = (m1,bstack))
        (MDROP: Mem.drop_perm m1 bstack 0 (Mem.stack_limit + align (size_chunk Mptr) 8) Writable = Some m2)
        (MRSB: Mem.record_stack_blocks m2 (make_singleton_frame_adt' bstack frame_info_mono 0) = Some m3),
        let ge := Genv.globalenv prog in
        Genv.find_symbol ge prog.(prog_main) = Some bmain ->
        let rs0 :=
            rs # PC <- (Vptr bmain Ptrofs.zero)
               #RA <- Vnullptr
               #RSP <- (Vptr bstack (Ptrofs.repr (Mem.stack_limit + align (size_chunk Mptr) 8))) in
        initial_state_gen prog rs m (State rs0 m3).

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

Section WITHMEMORYMODEL2.

  Existing Instance mem_accessors_default.
  Context `{external_calls_prf : ExternalCalls }.

  Lemma semantics_gen_determinate:
    forall p m rs,
      determinate (semantics_gen p rs m).
  Proof.
    Ltac Equalities :=
      match goal with
      | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
        rewrite H1 in H2; inv H2; Equalities
      | _ => idtac
      end.
    intros; constructor; simpl; intros.
    - (* determ *)
      inv H; inv H0; Equalities.
      + split. constructor. auto.
      + discriminate.
      + discriminate.
      + assert (vargs0 = vargs) by (eapply Events.eval_builtin_args_determ; eauto). subst vargs0.
        exploit Events.external_call_determ. eexact H5. eexact H11. intros [A B].
        split. auto. intros. destruct B; auto. subst. auto.
      + assert (args0 = args) by (eapply Asm.extcall_arguments_determ; eauto). subst args0.
        exploit Events.external_call_determ. eexact H3. eexact H8. intros [A B].
        split. auto. intros. destruct B; auto. subst. auto.
    - (* trace length *)
      red; intros; inv H; simpl.
      omega.
      eapply Events.external_call_trace_length; eauto.
      eapply Events.external_call_trace_length; eauto.
    - (* initial states *)
      inv H; inv H0.
      unfold ge, ge0, rs0, rs1 in *; rewrite_hyps.  auto.
    - (* final no step *)
      assert (NOTNULL: forall b ofs, Values.Vnullptr <> Values.Vptr b ofs).
      { intros; unfold Values.Vnullptr; destruct Archi.ptr64; congruence. }
      inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
    - (* final states *)
      inv H; inv H0. congruence.
  Qed.


  Lemma semantics_determinate:
    forall p rs,
      determinate (semantics p rs).
  Proof.
    intros; constructor; simpl; intros.
    - (* determ *)
      inv H; inv H0; Equalities.
      + split. constructor. auto.
      + discriminate.
      + discriminate.
      + assert (vargs0 = vargs) by (eapply Events.eval_builtin_args_determ; eauto). subst vargs0.
        exploit Events.external_call_determ. eexact H5. eexact H11. intros [A B].
        split. auto. intros. destruct B; auto. subst. auto.
      + assert (args0 = args) by (eapply Asm.extcall_arguments_determ; eauto). subst args0.
        exploit Events.external_call_determ. eexact H3. eexact H8. intros [A B].
        split. auto. intros. destruct B; auto. subst. auto.
    - (* trace length *)
      red; intros; inv H; simpl.
      omega.
      eapply Events.external_call_trace_length; eauto.
      eapply Events.external_call_trace_length; eauto.
    - (* initial states *)
      inv H; inv H0.
      rewrite_hyps.
      inv H2; inv H3.
      unfold ge, ge0, rs0, rs1 in *; rewrite_hyps.  auto.
    - (* final no step *)
      assert (NOTNULL: forall b ofs, Values.Vnullptr <> Values.Vptr b ofs).
      { intros; unfold Values.Vnullptr; destruct Archi.ptr64; congruence. }
      inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
    - (* final states *)
      inv H; inv H0. congruence.
  Qed.

  
End WITHMEMORYMODEL2.

