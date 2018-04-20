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
Require Asmgenproof0.

Section WITHMEMORYMODEL.

  Existing Instance mem_accessors_default.
  Context `{memory_model_ops: Mem.MemoryModelOps}.
  Context `{external_calls_ops : !ExternalCallsOps mem}.
  Context `{enable_builtins: !EnableBuiltins mem}.

Section WITHGE.
  Variable ge : Genv.t Asm.fundef unit.

  Definition pc_at (s: state): option ((function * instruction) + external_function) :=
    let '(State rs m) := s in
    match rs PC with
    | Vptr b o =>
      match Genv.find_funct_ptr ge b with
      | Some (Internal f) =>
        match find_instr (Ptrofs.unsigned o) (fn_code f) with
        | Some i => Some (inl (f,i))
        | None => None
        end
      | Some (External ef) => Some (inr ef)
      | None => None
      end
    | _ => None
    end.

  Definition rs_state s :=
    let '(State rs _) := s in rs.

  Definition m_state s :=
    let '(State _ m) := s in m.

  Inductive is_call (rs: regset): instruction -> Prop :=
  | is_call_s:
      forall symb b sg,
        Genv.find_symbol ge symb = Some b ->
        is_call rs (Pcall_s symb sg)
  | is_call_r:
      forall (r: ireg) b sg,
        rs r = Vptr b Ptrofs.zero ->
        is_call rs (Pcall_r r sg).

  Inductive is_alloc sz : instruction -> Prop :=
    is_alloc_intro f:
      frame_size f = sz ->
      is_alloc sz (Pallocframe f (Ptrofs.sub (Ptrofs.repr (align sz 8)) (Ptrofs.repr (size_chunk Mptr)))).

  Inductive is_free (sz: Z) : instruction -> Prop :=
    is_free_intro:
      is_free sz (Pfreeframe sz (Ptrofs.sub (Ptrofs.repr sz) (Ptrofs.repr (size_chunk Mptr)))).


  Inductive is_jmp: instruction -> Prop :=
  | is_jmp_s:
      forall symb b sg,
        Genv.find_symbol ge symb = Some b ->
        is_jmp (Pjmp_s symb sg)
  | is_jmp_r:
      forall (r: ireg) sg,
        is_jmp (Pjmp_r r sg true).

  Inductive step: state -> trace -> state -> Prop :=
  | step_call_internal:
      forall s1 s2 s3 f0 icall f ialloc
        (PC1: pc_at s1 = Some (inl (f0, icall)))
        (PC2: pc_at s2 = Some (inl (f, ialloc)))
        (CALL: is_call (rs_state s1) icall)
        (ALLOC: is_alloc (frame_size (fn_frame f)) ialloc)
        (STEP1: RawAsm.step ge s1 E0 s2)
        (STEP2: RawAsm.step ge s2 E0 s3),
        step s1 E0 s3
  | step_call_external:
      forall s1 s2 s3 f0 icall ef t
        (PC1: pc_at s1 = Some (inl (f0, icall)))
        (CALL: is_call (rs_state s1) icall)
        (PC2: pc_at s2 = Some (inr ef))
        (STEP1: RawAsm.step ge s1 E0 s2)
        (STEP2: RawAsm.step ge s2 t s3),
        step s1 t s3
  | step_free_ret:
      forall s1 s2 s3 ifree f
        (PC1: pc_at s1 = Some (inl (f, ifree)))
        (PC2: pc_at s2 = Some (inl (f, Pret)))
        (FREE: is_free (frame_size (fn_frame f)) ifree)
        (STEP1: RawAsm.step ge s1 E0 s2)
        (STEP2: RawAsm.step ge s2 E0 s3),
        step s1 E0 s3      
  | step_free_tailcall:
      forall s1 s2 s3 s4 ifree ijmp ialloc f0 f
        (PC1: pc_at s1 = Some (inl (f0, ifree)))
        (PC2: pc_at s2 = Some (inl (f0, ijmp)))
        (PC2: pc_at s3 = Some (inl (f, ialloc)))
        (FREE: is_free (frame_size (fn_frame f0)) ifree)
        (JMP: is_jmp ijmp)
        (ALLOC: is_alloc (frame_size (fn_frame f)) ialloc)
        (STEP1: RawAsm.step ge s1 E0 s2)
        (STEP2: RawAsm.step ge s2 E0 s3)
        (STEP3: RawAsm.step ge s3 E0 s4),
        step s1 E0 s4
  | step_free_external:
      forall s1 s2 s3 s4 ifree ijmp f0 ef t
        (PC1: pc_at s1 = Some (inl (f0, ifree)))
        (PC2: pc_at s2 = Some (inl (f0, ijmp)))
        (PC2: pc_at s3 = Some (inr ef))
        (FREE: is_free (frame_size (fn_frame f0)) ifree)
        (JMP: is_jmp ijmp)
        (STEP1: RawAsm.step ge s1 E0 s2)
        (STEP2: RawAsm.step ge s2 E0 s3)
        (STEP3: RawAsm.step ge s3 t s4),
        step s1 t s4
  | step_other_internal:
      forall s1 t s2 f0 i
        (PC: pc_at s1 = Some (inl (f0,i)))
        (NOFREE: forall f, ~ is_free f i)
        (NOCALL: ~ is_call (rs_state s1) i)
        (STEP: RawAsm.step ge s1 t s2),
        step s1 t s2
  .

End WITHGE.
  
  Definition semantics_gen prog rs m :=
    Semantics step (initial_state_gen prog rs m) final_state (Genv.globalenv prog).

  Definition semantics prog rs :=
    Semantics step (initial_state prog rs) final_state (Genv.globalenv prog).

End WITHMEMORYMODEL.

Section SIMU.

  Existing Instance mem_accessors_default.
  Context `{memory_model_ops: Mem.MemoryModelOps}.
  Context `{external_calls_ops : !ExternalCallsOps mem}.
  Context `{enable_builtins: !EnableBuiltins mem}.

  Variable prog: Asm.program.
  Let ge := Genv.globalenv prog.

  Lemma step_correct:
    forall s t s' 
      (STEP : step ge s t s'),
      plus RawAsm.step (Genv.globalenv prog) s t s'.
  Proof.
    intros.
    inv STEP.
    - eapply plus_two; eauto.
    - eapply plus_two; eauto.
    - eapply plus_two; eauto.
    - eapply plus_three; eauto.
    - eapply plus_three; eauto.
    - apply plus_one; auto.
  Qed.

  Lemma is_call_dec:
    forall rs i,
      is_call ge rs i \/ ~ is_call ge rs i.
  Proof.
    destruct i; try now (right; intro A; inv A).
    - destruct (Genv.find_symbol ge symb) eqn:FS.
      left; econstructor; eauto.
      right; intro A; inv A. congruence.
    - destruct (rs r) eqn:PTR; try now (right; intro A; inv A; congruence).
      destruct (Ptrofs.eq_dec i Ptrofs.zero). subst.
      left; econstructor; eauto.
      right; intro A; inv A; congruence.
  Qed.

  Lemma is_free_dec:
    forall i,
      (exists sz, is_free sz i) \/ ~ exists sz, is_free sz i.
  Proof.
    destruct i; try now (right; intro A; inv A).
    edestruct (Ptrofs.eq_dec ofs_ra). rewrite e.
    left; exists sz; econstructor; eauto.
    right; intro A; inv A. inv H. congruence.
  Qed.

  Inductive is_builtin: instruction -> Prop :=
  | is_builtin_intro ef args res: is_builtin (Pbuiltin ef args res).
  
  Lemma step_internal:
    forall s t s'
      (STEP: RawAsm.step ge s t s')
      f i
      (PCAT: pc_at ge s = Some (inl (f,i)))
      (NB: ~ is_builtin i),
      exec_instr ge f i (rs_state s) (m_state s) = Next (rs_state s') (m_state s') /\ t = E0.
  Proof.
    unfold pc_at; intros s t s'  STEP; inv STEP.
    - rewrite H, H0, H1. inversion 1; subst. simpl. eauto.
    - rewrite H, H0, H1. intros f0 i A; inv A. intro NIB; exfalso; apply NIB. constructor.
    - rewrite H, H0. inversion 1.
  Qed.

  Ltac simpl_regs_in H :=
    repeat rewrite Pregmap.gso in H by congruence;
    try rewrite Pregmap.gss in H;
    try rewrite Asmgenproof0.nextinstr_pc in H.

  Ltac simpl_regs :=
    repeat rewrite Pregmap.gso by congruence;
    try rewrite Pregmap.gss;
    try rewrite Asmgenproof0.nextinstr_pc.

  Record wf_asm_function (f: function): Prop :=
    {
      wf_asm_call_target_exists:
        forall o symb sg,
          find_instr o (fn_code f) = Some (Pcall_s symb sg) ->
          exists bf f',
            Genv.symbol_address ge symb Ptrofs.zero = Vptr bf Ptrofs.zero /\
            Genv.find_funct_ptr ge bf = Some f';
      wf_asm_alloc_only_at_beginning:
        forall o fi ora,
          find_instr o (fn_code f) = Some (Pallocframe fi ora) ->
          o = 0;
      wf_asm_alloc_at_beginning:
        forall i,
          find_instr 0 (fn_code f) = Some i ->
          is_alloc (frame_size (fn_frame f)) i;

      wf_asm_after_freeframe:
        forall i o sz,
          find_instr (Ptrofs.unsigned o) (fn_code f) = Some i ->
          is_free sz i ->
          sz = frame_size (fn_frame f) /\
          exists i' ,
            find_instr (Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (instr_size i)))) (fn_code f) = Some i' /\
            (i' = Pret \/ is_jmp ge i' );


    }.

  Hypothesis wf_asm_prog:
    forall b f,
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      wf_asm_function f.

  Ltac rewrite_hyps :=
    repeat
      match goal with
        H1 : ?a = _, H2: ?a = _ |- _ => rewrite H1 in H2; inv H2
      end.


  Lemma group_progress:
    forall rs s1
      (SAFE : safe (RawAsm.semantics prog rs) s1),
      (exists r, final_state s1 r) \/ (exists t s2, step (Genv.globalenv prog) s1 t s2).
  Proof.
    intros.
    destruct (SAFE _  (star_refl _ _ _)) as [(r & FS)|(t & s2 & STEP)].
    eauto.
    destruct (pc_at ge s1) as [[[f i]|ef]|] eqn:PCs.
    - destruct (is_call_dec (rs_state s1) i) as [CALL|NOTCALL].
      + (* it's a call instruction : the next step is going to be either an external function or a Pallocframe. *)
        simpl in STEP.
        exploit step_internal; eauto. intro IB; inv IB; inv CALL. intros (EI & T0). subst.
        destruct (SAFE _ (star_one _ _ _ _ _ STEP)) as [(r & FS)|(t & s3 & STEP2)].
        * inv FS. simpl in EI.
          inv CALL; simpl in EI; repeat destr_in EI.
          -- simpl_regs_in H. unfold Genv.symbol_address in H. repeat destr_in H.
          -- simpl_regs_in H. rewrite H in H1. inv H1.
        * simpl in STEP2.
          assert (exists b f', Genv.find_funct_ptr ge b = Some f' /\
                          rs_state s2 PC = Vptr b Ptrofs.zero).
          {
            inv CALL; simpl in EI; repeat destr_in EI.
            - unfold pc_at in PCs; repeat destr_in PCs; simpl in *; subst.
              eapply wf_asm_call_target_exists in Heqo0; eauto.
              destruct Heqo0 as (bf & f' & SA & FFP).
              inv STEP2; simpl in *; subst; simpl_regs; simpl_regs_in H0; eauto.
            - simpl_regs. rewrite H in *. simpl in Heqo. destr_in Heqo. eauto.
          }
          destruct H as (b & f' & FFP & PC2).
          inversion STEP2; subst.
          -- simpl in *. rewrite_hyps.
             right; exists E0, (State rs' m').
             eapply step_call_internal.  5: apply STEP. 5: apply STEP2. eauto.
             unfold pc_at. rewrite PC2. rewrite H0, H1. eauto. eauto.
             eapply wf_asm_alloc_at_beginning; eauto.
          -- simpl in *. rewrite_hyps.
             eapply wf_asm_alloc_at_beginning in H1; eauto. inv H1.
          -- simpl in PC2. rewrite_hyps.
             right; eexists t, (State _ m').
             eapply step_call_external.  4: apply STEP. 4: apply STEP2. eauto. eauto.
             unfold pc_at. rewrite PC2. rewrite H0. eauto. 
      + (* not a call, free ? *)
        destruct (is_free_dec i) as [(sz & ISFREE)|NISFREE].
        * inversion ISFREE; subst. clear NOTCALL.
          exploit step_internal; eauto. intro IB; inv IB. intros (EI & T0). subst.

          destruct (SAFE _ (star_one _ _ _ _ _ STEP)) as [(r & FS)|(t & s3 & STEP2)].
          -- inv FS. simpl in EI. repeat destr_in EI.
             unfold pc_at in PCs. repeat destr_in PCs.
             rewrite Asmgenproof0.nextinstr_pc in H.
             simpl_regs_in H. simpl in H. rewrite Heqv0 in H. simpl in H. inv H.
          -- unfold pc_at in PCs. repeat destr_in PCs.
             destruct (wf_asm_after_freeframe _ (wf_asm_prog _ _ Heqo) _ _ _ Heqo0 ISFREE) as (SZ & i0 & FI0 & SPECi0). subst.
             simpl in EI. repeat destr_in EI.
             assert (t = E0).
             {
               inv STEP2; auto; unfold ge in *; simpl in *; subst; rewrite_hyps.
               repeat simpl_regs_in H. rewrite Heqv in H; simpl in H; inv H.
               unfold ge in *; simpl in *; subst; rewrite_hyps.
               destruct SPECi0 as [A|A]; inv A.
               repeat simpl_regs_in H. rewrite Heqv in H; simpl in H; inv H. congruence.
             }
             subst.
             destruct SPECi0 as [RET | JMP].
             ++ subst. right.
                eexists _, _; eapply step_free_ret. 4: apply STEP. 4: apply STEP2.
                simpl. fold ge. rewrite Heqv, Heqo, Heqo0. eauto.
                unfold pc_at. destr. simpl in *; subst. 
                rewrite Asmgenproof0.nextinstr_pc.
                simpl_regs. rewrite Heqv. simpl. fold ge; rewrite Heqo. rewrite FI0. eauto.
                constructor.
             ++ destruct (SAFE _ (star_two _ _ _ _ _ _ _ STEP STEP2 eq_refl)) as [(ret & FS)|(t & s4 & STEP3)].
                ** inv FS.


                

                rewrite FI0 in H2.
                eexists _, _; eapply step_call_internal. 5: apply STEP. 5: apply STEP2.


        * simpl in STEP2.
          assert (exists b f', Genv.find_funct_ptr ge b = Some f' /\
                          rs_state s2 PC = Vptr b Ptrofs.zero).
          {
            inv CALL; simpl in EI; repeat destr_in EI.
            - unfold pc_at in PCs; repeat destr_in PCs; simpl in *; subst.
              eapply wf_asm_call_target_exists in Heqo0; eauto.
              destruct Heqo0 as (bf & f' & SA & FFP).
              inv STEP2; simpl in *; subst; simpl_regs; simpl_regs_in H0; eauto.
            - simpl_regs. rewrite H in *. simpl in Heqo. destr_in Heqo. eauto.
          }
          destruct H as (b & f' & FFP & PC2).
          inversion STEP2; subst.
          -- simpl in *. rewrite_hyps.
             right; exists E0, (State rs' m').
             eapply step_call_internal.  5: apply STEP. 5: apply STEP2. eauto.
             unfold pc_at. rewrite PC2. rewrite H0, H1. eauto. eauto.
             eapply wf_asm_alloc_at_beginning; eauto.
          -- simpl in *. rewrite_hyps.
             eapply wf_asm_alloc_at_beginning in H1; eauto. inv H1.
          -- simpl in PC2. rewrite_hyps.
             right; eexists t, (State _ m').
             eapply step_call_external.  4: apply STEP. 4: apply STEP2. eauto. eauto.
             unfold pc_at. rewrite PC2. rewrite H0. eauto. 

  Qed.

  Theorem group_correct:
    forall rs,
      backward_simulation (RawAsm.semantics prog rs) (semantics prog rs).
  Proof.
    intro rs.
    eapply backward_simulation_plus with (match_states := fun (s1 s2: Asm.state) => s1 = s2).
    - reflexivity.
    - intros; eauto.
    - simpl; intros s1 s2 I1 I2. eauto.
    - intros; subst. auto.
    - simpl; intros s1 s2 A SAFE; subst.
      edestruct SAFE; eauto. apply star_refl.
      destruct H as (t & s'' & STEP). simpl in *.
      eapply group_progress; eauto.
    - simpl; intros s2 t s2' STEP s1 EQ SAFE. subst.
      eexists; split; eauto.
      eapply step_correct; eauto.
  Qed.

End SIMU.
