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
Require Import RawAsm RealAsm.
Require Import RawAsmMergeSteps.

Section WITHMEMORYMODEL.
  
  Context `{memory_model: Mem.MemoryModel }.
  Existing Instance inject_perm_upto_writable.

  Context `{external_calls_ops : !ExternalCallsOps mem }.
  Context `{!EnableBuiltins mem}.

  Existing Instance mem_accessors_default.
  Existing Instance symbols_inject_instance.
  Context `{external_calls_props : !ExternalCallsProps mem
                                    (memory_model_ops := memory_model_ops)
                                    }.

  Variable prog: Asm.program.
  Let ge := Genv.globalenv prog.
  Definition bstack := Genv.genv_next ge.
  Section PRESERVATION.

  Variable init_stk: stack.
  Definition init_sp: val := current_sp init_stk.
  Variable binit_sp: block.
  Hypothesis init_sp_ptr: init_sp = Vptr binit_sp Ptrofs.zero.


  Lemma ptrofs_sub_sub a b:
    Ptrofs.sub (Ptrofs.sub a b) a = Ptrofs.neg b.
  Proof.
    rewrite (Ptrofs.sub_add_opp a b).
    rewrite Ptrofs.sub_add_l. rewrite Ptrofs.sub_idem.
    apply Ptrofs.add_zero_l.
  Qed.

  Inductive seq: state -> state -> Prop :=
  | seq_intro rs1 rs2 m (REQ: forall r, rs1 r = rs2 r): seq (State rs1 m) (State rs2 m).

  Lemma internal_step:
    forall s f i
      (PCAT: pc_at ge s = Some (inl (f,i)))
      (NB: ~ is_builtin i) rs' m'
      (EI: exec_instr ge f i (rs_state s) (m_state s) = Next rs' m'),
      RealAsm.step ge s E0 (State rs' m').
  Proof.
    unfold pc_at; intros s f i PCAT NB rs' m' EI.
    repeat destr_in PCAT.
    eapply RealAsm.exec_step_internal; eauto.
  Qed.

  Ltac force_rewrite_match H :=
    match goal with
      H: ?b = _ |- context [ match ?a with _ => _ end ] =>
      cut (b = a);[ let A := fresh in intro A; rewrite <- A, H | ]
    end.
  Ltac simpl_regs_in H :=
    repeat first [ rewrite Pregmap.gso in H by congruence
                 | rewrite Pregmap.gss in H
                 | rewrite Asmgenproof0.nextinstr_pc in H
                 | rewrite nextinstr_nf_pc in H
                 | rewrite Asmgenproof0.nextinstr_inv in H by congruence
                 ].

  Ltac simpl_regs :=
    repeat first [ rewrite Pregmap.gso by congruence
                 | rewrite Pregmap.gss
                 | rewrite Asmgenproof0.nextinstr_pc
                 | rewrite nextinstr_nf_pc
                 | rewrite Asmgenproof0.nextinstr_inv by congruence
                 ].

  Lemma nextinstr_eq:
    forall rs rs',
      (forall r, rs r = rs' r) ->
      forall sz r,
        nextinstr rs sz r = nextinstr rs' sz r.
  Proof.
    unfold nextinstr. intros.
    setoid_rewrite Pregmap.gsspec. destr. apply H.
  Qed.

  Lemma set_reg_eq:
    forall (rs rs': regset) r dst,
      (r <> dst -> rs r = rs' r) ->
      forall v v' (EQ: v = v'),
        (rs # dst <- v) r = (rs' # dst <- v') r.
  Proof.
    intros.
    setoid_rewrite Pregmap.gsspec. destr.
  Qed.

  Lemma undef_regs_eq:
    forall l (rs rs': regset) r,
      (~ In r l -> rs r = rs' r) ->
      undef_regs l rs r = undef_regs l rs' r.
  Proof.
    induction l; simpl; intros; eauto.
    apply IHl. intros; apply set_reg_eq. intros; apply H. intuition. auto.
  Qed.

  Lemma nextinstr_nf_eq:
    forall rs rs',
      (forall r, rs r = rs' r) ->
      forall sz r,
        nextinstr_nf rs sz r = nextinstr_nf rs' sz r.
  Proof.
    unfold nextinstr_nf. intros.
    apply nextinstr_eq.
    intros; apply undef_regs_eq. auto.
  Qed.

  Lemma set_res_eq:
    forall res rs rs',
      (forall r, rs r = rs' r) ->
      forall r vres,
        set_res res vres rs r = set_res res vres rs' r.
  Proof.
    induction res; simpl; intros; eauto.
    apply set_reg_eq; auto.
  Qed.

  Axiom frame_size_aligned:
    forall f,
      frame_size f = align (frame_size f) 8.

  
  Lemma steps_correct:
    forall s1 t s2
      (STEP : step (Genv.globalenv prog) s1 t s2)
    s1' (SEQ: seq s1 s1'),
    exists s2',
      plus RealAsm.step (Genv.globalenv prog) s1' t s2'
      /\ seq s2 s2'.
  Proof.
    intros s1 t s2 STEP s1' SEQ; inv STEP.
    - (* call -> alloc *)
      inv SEQ.
      edestruct (step_internal _ _ _ _ STEP1) as (EI1 & T1); eauto. intro IB; inv IB; inv CALL.
      edestruct (step_internal _ _ _ _ STEP2) as (EI2 & T2); eauto. intro IB; inv IB; inv ALLOC.
      inv ALLOC. simpl in EI2; repeat destr_in EI2.
      destruct s2, s3; simpl in *. subst.

      assert (call_ok: m1 = m /\ exists b rs',
                  r0 PC = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr ge b = Some (Internal f) /\
                  exec_instr ge f0 icall rs2 m = Next rs' m0 /\
                  (forall r:preg, r <> RSP -> rs' r = r0 r) /\
                  rs' RSP = Val.offset_ptr (rs2 RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))) /\
                  r0 RSP = rs1 RSP).
      {
        unfold pc_at in PC2. repeat destr_in PC2.
        split.
        inv CALL; simpl in EI1; repeat destr_in EI1; eauto.
        exists b.
        inv CALL; simpl in EI1; repeat destr_in EI1.
        - simpl_regs_in Heqv. revert Heqv.  unfold Genv.symbol_address. rewrite H0. intro A; inv A.
          unfold ge. rewrite Heqo0.
          simpl.
          force_rewrite_match Heqo.
          + eexists; repeat apply conj; eauto.
            * intros. rewrite (Pregmap.gso _ _ H2).
              simpl_regs. unfold Genv.symbol_address. unfold ge. rewrite H0. rewrite REQ.
              apply set_reg_eq. intros.
              apply set_reg_eq. auto.
              auto. auto.
          + rewrite ! REQ.
            f_equal.
            simpl_regs. 
            rewrite Val.offset_ptr_assoc.
            rewrite Ptrofs.add_commut.
            rewrite <- Ptrofs.sub_add_opp.
            rewrite H, ptrofs_sub_sub. rewrite REQ. auto.
        - simpl_regs_in Heqv. revert Heqv. rewrite H0. intro A; inv A.
          unfold ge. rewrite Heqo0.
          simpl.
          force_rewrite_match Heqo.
          + eexists; repeat apply conj; eauto.
            * intros. rewrite (Pregmap.gso _ _ H2).
              simpl_regs.
              apply set_reg_eq; auto. intros.
              apply set_reg_eq. auto. rewrite REQ. auto.
              rewrite <- REQ. auto.
          + rewrite ! REQ.
            f_equal.
            simpl_regs. 
            rewrite Val.offset_ptr_assoc.
            rewrite Ptrofs.add_commut.
            rewrite <- Ptrofs.sub_add_opp.
            rewrite H, ptrofs_sub_sub. rewrite REQ. auto.
      }
      destruct call_ok as (MEQ & b & rs' & PC3 & FFP & EIcall & SAMErs & rs'RSP & r0RSP).
      subst.
      eexists; split. eapply plus_two.
      eapply internal_step; eauto.
      rewrite <- PC1.
      unfold ge. simpl. rewrite <- REQ. auto. intro IB; inv IB; inv CALL.
      eapply internal_step; eauto.
      rewrite <- PC2. rewrite <- SAMErs by congruence.
      unfold ge. simpl. auto.
      inversion 1.
      simpl. eauto. traceEq.
      econstructor.
      apply nextinstr_eq.
      intros. apply set_reg_eq; auto.
      intros. rewrite rs'RSP.
      apply set_reg_eq; auto. intros. rewrite <- SAMErs; eauto.
      rewrite r0RSP.
      rewrite REQ.
      rewrite Val.offset_ptr_assoc. rewrite Ptrofs.add_commut.
      rewrite Ptrofs.add_neg_zero.
      admit. (* RSP should be a pointer *)
      rewrite r0RSP. rewrite rs'RSP. rewrite REQ.
      rewrite Val.offset_ptr_assoc. f_equal.
      rewrite <- Ptrofs.neg_add_distr. f_equal.
      rewrite Ptrofs.sub_add_opp.
      rewrite (Ptrofs.add_commut _ (Ptrofs.neg _)).
      rewrite <- Ptrofs.add_assoc. rewrite Ptrofs.add_neg_zero. rewrite Ptrofs.add_zero_l; auto.
    - admit.                    (* call -> external *)
    - (* free -> ret *)
      inv SEQ.
      edestruct (step_internal _ _ _ _ STEP1) as (EI1 & T1); eauto. intro IB; inv IB; inv FREE.
      edestruct (step_internal _ _ _ _ STEP2) as (EI2 & T2); eauto. intro IB; inv IB.
      inv FREE. simpl in EI1; repeat destr_in EI1.
      simpl in EI2. inv EI2.
      destruct s2, s3; simpl in *. subst.
      simpl_regs_in PC2.
      repeat destr_in PC1. simpl in PC2.
      repeat destr_in PC2.
      eexists. split.
      eapply plus_two.
      eapply internal_step. simpl.
      unfold ge. rewrite <- REQ, Heqv0, Heqo2, Heqo1. eauto.
      inversion 1.
      simpl. eauto.
      eapply internal_step. simpl. simpl_regs.
      unfold ge. rewrite <- REQ, Heqv0. simpl.
      rewrite Heqo2, Heqo3. eauto. inversion 1.
      simpl. force_rewrite_match Heqo. eauto.
      f_equal. simpl_regs.
      rewrite REQ. f_equal.
      rewrite Z.max_r by apply frame_size_pos. rewrite <- frame_size_aligned. auto.
      traceEq.
      constructor. intros.
      simpl_regs.
      apply set_reg_eq.
      intros; apply set_reg_eq.
      intros.
      repeat simpl_regs.
      intros; apply set_reg_eq.
      intros. simpl_regs. auto.
      rewrite Val.offset_ptr_assoc. f_equal. auto.
      rewrite <- Ptrofs.sub_add_l.
      rewrite Ptrofs.add_commut.
      rewrite Ptrofs.sub_add_l.
      rewrite Ptrofs.sub_idem. rewrite Ptrofs.add_zero_l. auto. auto. auto.
    - admit. (* free -> jmp -> alloc (tailcall to internal function) *)
    - admit. (* free -> jmp -> external (tailcall to external function) *)
    - (* regular instruction *)
      inv STEP0; simpl in PC; rewrite H in PC; repeat destr_in PC; inv H0.
      rewrite Heqo0 in H1; inv H1.
      inv SEQ.
      eexists; split. apply plus_one.
      eapply RealAsm.exec_step_internal. rewrite <- REQ; eauto. eauto. eauto.

      Lemma exec_instr_same_rs:
        forall f i rs m rs' m' rs2 (SEQ: seq (State rs m) (State rs2 m))
          (EI: RawAsm.exec_instr ge f i rs m = Next rs' m'),
        exists rs2',
          exec_instr ge f i rs2 m = Next rs2' m' /\ seq (State rs' m') (State rs2' m').
      Proof.
        
      Qed.

      eapply
      
  Qed.

  Theorem real_asm_correct rs:
    forward_simulation (RawAsmMergeSteps.semantics prog rs) (RealAsm.semantics prog rs).
  Proof.
    eapply forward_simulation_plus with (match_states := fun s1 s2 : Asm.state => s1 = s2).
    - reflexivity.
    - intros; eauto.
    - intros; subst; eauto.
    - simpl. intros; subst.
      eexists; split; eauto.
      
      inv H.
      + eapply plus_two; eauto.
      inv H; first [ eapply plus_one; eauto; try reflexivity
                   | eapply plus_two; eauto; try reflexivity
                   | eapply plus_three; eauto; try reflexivity ].
  Qed.

  

  Ltac simpl_regs_in H :=
    repeat rewrite Pregmap.gso in H by congruence;
    try rewrite Pregmap.gss in H.

  Ltac simpl_regs :=
    repeat rewrite Pregmap.gso by congruence;
    try rewrite Pregmap.gss.

  Definition measure (s: state) : nat :=
    match classify_state_bool s with
    | Some SKcall => 2%nat
    | Some SKret => 0%nat
    | _ => 1%nat
    end.

  Lemma instr_size_not_zero:
    forall i,
      instr_size i <> 0.
  Proof.
    intros; apply not_eq_sym; apply Z.lt_neq, instr_size_positive.
  Qed.

  Lemma eval_builtin_arg_eq_rs:
    forall (rs1 rs2: regset) (REQ: forall r, rs1 r = rs2 r) sp m args vargs,
      eval_builtin_arg ge rs1 sp m args vargs ->
      eval_builtin_arg ge rs2 sp m args vargs.
  Proof.
    induction 2; rewrite ? REQ; econstructor; eauto.
  Qed.

  Lemma eval_builtin_args_eq_rs:
    forall (rs1 rs2: regset) (REQ: forall r, rs1 r = rs2 r) sp m args vargs,
      eval_builtin_args ge rs1 sp m args vargs ->
      eval_builtin_args ge rs2 sp m args vargs.
  Proof.
    induction 2; constructor; eauto using eval_builtin_arg_eq_rs.
  Qed.

  Fixpoint in_builtin_res (b: builtin_res preg) (r:preg) :=
    match b with
    | BR b => b = r
    | BR_none => False
    | BR_splitlong hi lo => in_builtin_res hi r \/ in_builtin_res lo r
    end.

  Lemma set_res_other:
    forall res vres rs r,
      ~ in_builtin_res res r ->
      set_res res vres rs r = rs r.
  Proof.
    induction res; simpl; intros; eauto.
    rewrite Pregmap.gso; auto.
    rewrite IHres2. apply IHres1. intuition. intuition.
  Qed.

  Theorem real_step_correct:
    forall s1 t s1' (STEP: RawAsm.step ge s1 t s1')
      s2 (MS: match_states s1 s2),
   (exists s2', plus RealAsm.step ge s2 t s2' /\ match_states s1' s2') \/
   (measure s1' < measure s1)%nat /\ t = E0 /\ match_states s1' s2.
  Proof.
    intros s1 t s1' STEP s2 MS.
    inv MS.
    - inv STEP.
      + (* internal *)
        destruct (instr_same i) eqn:SAME.
        admit.
        destruct i; simpl in SAME; try congruence.
        * (* call_s *)
          simpl. simpl in H2. inv H2.
          right.
          destruct (calls_to_defined_functions _ _ _ _ _ H0 H1) as (bf & f' & SA & FFP).
          rewrite SA.
          assert (FS: Genv.find_symbol ge symb = Some bf).
          {
            unfold Genv.symbol_address in SA; repeat destr_in SA.
          }
          split.
          -- unfold measure. unfold classify_state_bool.
             rewrite H, H0, H1. simpl.
             rewrite FFP. rewrite FS. destr. 2: omega.
             destr_in Heqo.
             erewrite pallocframe_at_beginning in Heqo; eauto. simpl in Heqo. inv Heqo. omega.
             inv Heqo. omega.
          -- split; auto.
             eapply match_states_call.
             3: eapply RawAsm.exec_step_internal.
             3: apply H. eauto. econstructor; eauto. econstructor; eauto. eauto. eauto.
             simpl. f_equal. rewrite SA. reflexivity.
        * (* call_r *) admit.
        * (* ret *)
          specialize (CL SKret).
          edestruct CL; [|congruence].
          repeat econstructor; eauto.
        * (* allocframe *)
          specialize (CL SKalloc).
          edestruct CL; [|congruence].
          repeat econstructor; eauto.
        * (* freeframe *)
          destruct (after_freeframe _ _ _ _ _ H0 H1) as (i & NEXTINSTR & CHOICES).
          destruct CHOICES.
          {
            right.
            split.
            - simpl in H2. repeat destr_in H2.
              unfold measure, classify_state_bool. rewrite Asmgenproof0.nextinstr_pc. simpl_regs.
              rewrite H. simpl. rewrite H0, H1. rewrite NEXTINSTR.
              simpl. omega.
            - split; auto.
              eapply match_states_freeframe; eauto.
              2: eapply RawAsm.exec_step_internal; eauto.
              econstructor; eauto. constructor.
          }
          admit.                (* cases jmp, i.e. tailcall *)
      + inv SEQ.                (* builtin *)
        left. eexists; split.
        * apply plus_one.
          eapply exec_step_builtin; rewrite <- ? REQ; eauto.
          eapply eval_builtin_args_eq_rs; eauto.
        * apply match_states_regular; auto.
          -- constructor. intros. apply nextinstr_nf_eq.
             intros. apply set_res_eq.
             intros; apply undef_regs_eq; auto.
          -- (* noalloc or ret *)
            intros sk A; inv A. 2: split; congruence.
            unfold nextinstr_nf in H6.
            rewrite Asmgenproof0.nextinstr_pc in H6. simpl in H6. simpl_regs_in H6.
            setoid_rewrite set_res_other in H6.
            erewrite Asmgenproof0.undef_regs_other in H6.
            rewrite H in H6. simpl in H6. inv H6.
            rewrite_hyps.
            inv H10; try (now intuition congruence).
            eapply pallocframe_only_at_beginning in H8; eauto.
            contradict H8. admit.
            admit. (* ret is always preceded by freeframe. *)
            Transparent destroyed_by_builtin.
            intros r' IN EQ. subst. contradict IN.
            unfold destroyed_by_builtin. repeat destr; simpl; try intuition congruence.
            clear. induction clobbers; simpl; intros. inversion 1.
            destr. simpl. intros [A|A]. destruct m; simpl in A; try congruence. auto.
            admit.              (* res <> PC *)
      + admit. (* external *)
    - inv CL. inv H2.
      + (* call_s *)
        inv STEP0; try congruence.
        rewrite_hyps. simpl in H7. inv H7.
        destruct (calls_to_defined_functions _ _ _ _ _ H0 H1) as (bf & f' & SA & FFP).
        assert (bf = b0).
        {
          unfold Genv.symbol_address in SA; rewrite FS in SA. inv SA; auto.
        }
        subst.
        inv SEQ.
        inv STEP; try congruence.
        * simpl_regs_in H4. rewrite_hyps.
          exploit pallocframe_at_beginning; eauto. intro FI. setoid_rewrite FI in H6. inv H6.
          left. simpl in H9. repeat destr_in H9.
          eexists. split.
          -- eapply plus_two.
             eapply exec_step_internal. rewrite <- REQ; eauto. eauto. eauto. simpl.
             simpl_regs_in Heqo.
             rewrite Val.offset_ptr_assoc in Heqo.
             rewrite Ptrofs.add_commut in Heqo.
             rewrite <- Ptrofs.sub_add_opp in Heqo.
             rewrite ptrofs_sub_sub in Heqo.
             rewrite ! REQ in Heqo. rewrite Heqo. eauto.
             eapply exec_step_internal.
             simpl_regs. eauto. eauto. eauto.
             simpl. eauto.
             reflexivity.
          -- eapply match_states_regular.
             ++ constructor.
                apply nextinstr_eq. simpl_regs.
                intros. apply set_reg_eq.
                intros. apply set_reg_eq.
                intros. rewrite (Pregmap.gso _ _ H2).
                apply set_reg_eq.
                intros; apply set_reg_eq. auto.
                rewrite REQ; auto.
                auto.
                auto.
                rewrite REQ.
                rewrite Val.offset_ptr_assoc.
                rewrite <- Ptrofs.neg_add_distr. f_equal.
                f_equal.
                generalize (Ptrofs.repr (align (frame_size (fn_frame f)) 8)).
                generalize (Ptrofs.repr (size_chunk Mptr)). clear.
                intros.
                rewrite Ptrofs.sub_add_opp.
                rewrite (Ptrofs.add_commut i0).
                rewrite <- Ptrofs.add_assoc.
                rewrite <- Ptrofs.sub_add_opp. rewrite Ptrofs.sub_idem.
                rewrite Ptrofs.add_zero_l; auto.
             ++ intros sk CL. inv CL; try intuition congruence.
                revert H4. rewrite Asmgenproof0.nextinstr_pc.
                simpl_regs. rewrite SA. simpl. rewrite Ptrofs.add_zero_l. intro A; inv A.
                inv H8; try intuition congruence.
                ** eapply pallocframe_only_at_beginning in H6; eauto.
                   contradict H6.
                   rewrite Ptrofs.unsigned_repr by apply instr_size_repr.
                   apply instr_size_not_zero.
                ** admit. (*ret not just after builtin *)
        * rewrite SA in H4. rewrite Pregmap.gss in H4. inv H4. rewrite_hyps.
          erewrite pallocframe_at_beginning in H6; eauto; inv H6.
        * rewrite SA in H4. rewrite Pregmap.gss in H4. inv H4. rewrite_hyps.
          admit.
      + admit. (* same thing with call_r *)
    -  

  Qed.

  Lemma real_instr:
    forall m1 m2 rs1 rs2 f i rs1' m1'
      (MS: match_states (State rs1 m1) (State rs2 m2))
      b o
      (RPC: rs1 PC = Vptr b o)
      (FFP: Genv.find_funct_ptr ge b = Some (Internal f))
      (FI: find_instr (Ptrofs.unsigned o) (fn_code f) = Some i)
      (EI: RawAsm.exec_instr ge f i rs1 m1 = Next rs1' m1')
,
      exists rs2' m2',
        RealAsm.exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ match_states (State rs1' m1') (State rs2' m2').
  Proof.
    intros m1 m2 rs1 rs2 f i rs1' m1' MS b o RPC FFP FI EI.
    destruct (instr_same i) eqn:SAME. eapply real_instr_same; eauto.
    destruct i; simpl in SAME; inv SAME.
    - destruct (calls_to_defined_functions _ _ _ _ _ FFP FI)
        as (bf & SA & FFP').
      destr_in FFP'.
      destr_in FFP'.
      + (* call to internal function *)
        assert (CS: classify_state rs1 = SKcall bf sg).
        {
          unfold classify_state. rewrite RPC, FFP, FI.
          simpl. unfold Genv.symbol_address in SA; repeat destr_in SA.
        }
        inv MS; try congruence.
        destruct RAWSTEP as (rs2' & m2' & RAWSTEP2).
        inversion RAWSTEP2; try congruence. subst.
        rewrite <- REQ in H3. rewrite_hyps.
        do 2 eexists; split. eauto.
        simpl in EI; inv EI.
        eapply match_states_alloc.
        * unfold classify_state.
          rewrite Pregmap.gss.
          rewrite SA, Heqo0, FFP'. simpl. eauto.
        * intros rs0 m1 t STEP.
          inv STEP; try congruence.
          Focus 2. rewrite Pregmap.gss in H3. congruence.
          Focus 2. rewrite Pregmap.gss in H3. congruence.
          rewrite Pregmap.gss in H3. rewrite SA in H3; inv H3.
          rewrite Heqo0 in H5; inv H5.
            rewrite FFP'  in H6; inv H6.
            simpl in H7. repeat destr_in H7.
            repeat rewrite Pregmap.gso in Heqo2 by congruence.
            rewrite Pregmap.gss in Heqo2.
            rewrite Val.offset_ptr_assoc in Heqo2.
            rewrite Ptrofs.add_commut in Heqo2.
            rewrite <- Ptrofs.sub_add_opp in Heqo2.
            rewrite ptrofs_sub_sub in Heqo2.
            rewrite ! REQ in Heqo2. rewrite Heqo1 in Heqo2. inv Heqo2.
            do 2 eexists. split.
            + econstructor. repeat rewrite Pregmap.gso by congruence. rewrite Pregmap.gss. eauto. eauto.
              eauto. simpl. eauto.
            + constructor.
              apply nextinstr_eq.
              repeat rewrite Pregmap.gso by congruence.
              repeat rewrite Pregmap.gss.
              intros. apply set_reg_eq.
              intros. apply set_reg_eq.
              intros. rewrite (Pregmap.gso _ _ H).
              apply set_reg_eq.
              intros; apply set_reg_eq. auto.
              rewrite REQ; auto.
              auto.
              auto.
              rewrite REQ.
              rewrite Val.offset_ptr_assoc.
              rewrite <- Ptrofs.neg_add_distr. f_equal.
              f_equal.
              generalize (Ptrofs.repr (align (frame_size (fn_frame f0)) 8)).
              generalize (Ptrofs.repr (size_chunk Mptr)). clear.
              intros.
              rewrite Ptrofs.sub_add_opp.
              rewrite (Ptrofs.add_commut i0).
              rewrite <- Ptrofs.add_assoc.
              rewrite <- Ptrofs.sub_add_opp. rewrite Ptrofs.sub_idem.
              rewrite Ptrofs.add_zero_l; auto.
              unfold classify_state.
              rewrite Asmgenproof0.nextinstr_pc.
              repeat rewrite Pregmap.gso by congruence.
              rewrite Pregmap.gss. rewrite SA. simpl.
              rewrite Heqo0.
              destr.
              destruct i; auto.
              eapply pallocframe_only_at_beginning in Heqo2; eauto.
              rewrite Ptrofs.add_zero_l in Heqo2.
              simpl in Heqo2.
              rewrite Ptrofs.unsigned_repr in Heqo2.
              2: apply instr_size_repr.

              Lemma instr_size_not_zero:
                forall i,
                  instr_size i <> 0.
              Proof.
                intros; apply not_eq_sym; apply Z.lt_neq, instr_size_positive.
              Qed.

              apply instr_size_not_zero in Heqo2. easy.
        }
        

      + intros.
        setoid_rewrite Pregmap.gsspec. repeat destr; subst.
        repeat setoid_rewrite Pregmap.gsspec. repeat destr; subst.
        repeat setoid_rewrite Pregmap.gsspec. repeat destr; subst.
        repeat setoid_rewrite Pregmap.gsspec. admit.
        repeat setoid_rewrite Pregmap.gsspec. repeat destr; subst.
        setoid_rewrite Pregmap.gso . 2: congruence.
        rewrite Pregmap.gss. rewrite REQ. auto.


        simpl.

      admit.
    - admit.
    - admit.
    - assert (classify_state rs1 = SKalloc frame ofs_ra).
      unfold classify_state. rewrite RPC, FFP, FI; reflexivity.
      inv MS; try congruence.
      edestruct RAWSTEP as (rs4 & m4 & STEP & MS').
      econstructor; eauto.
      inv STEP; try congruence.
      rewrite <- REQ, RPC in H4 ; inv H4.
      rewrite FFP in H5; inv H5.
      rewrite FI in H6; inv H6.
      rewrite H7. do 2 eexists; split; eauto.
    -
  Qed.
    

  
  Lemma instr_correct:
    forall 

  
  Lemma ZEQ: forall a b,
      proj_sumbool (zeq a b) = true -> a = b.
  Proof.
    intros; destruct zeq; auto. discriminate.
  Qed.

  Lemma ZLE: forall a b c d,
      zle a b || zle c d = true ->
      a <= b \/ c <= d.
  Proof.
    intros; destruct (zle a b), (zle c d); try congruence; try omega.
    simpl in H; congruence.
  Qed.

  Lemma perm_stack_eq':
    forall l m b fi j
      (SAP: stack_agree_perms (Mem.perm m) l)
      (PS: inject_perm_stack j (Mem.perm m) l)
      (INBLOCKS: in_stack' l (b, fi))
      o k p,
      Mem.perm m b o k p <-> 0 <= o < frame_size fi.
  Proof.
    induction 2; simpl; intros; eauto.
    - easy.
    - destruct INBLOCKS as [EQ | INSTK]. easy. 
      eapply IHPS; eauto. red; intros; eapply SAP; eauto. right; eauto.
    - destruct INBLOCKS as [EQ | INSTK].
      + red in EQ. simpl in EQ.
        red in EQ. rewrite BLOCKS in EQ. destruct EQ as [A|[]]; inv A.
        split. 2: apply PERM. eapply SAP. left. reflexivity. reflexivity.
        rewrite BLOCKS. left; reflexivity.
      + eapply IHPS; eauto. red; intros; eapply SAP; eauto. right; eauto.
  Qed.

  Lemma perm_stack_eq:
    forall m b fi j
      (PS: inject_perm_stack j (Mem.perm m) (Mem.stack m))
      (INBLOCKS: in_stack' (Mem.stack m) (b, fi))
      o k p,
      Mem.perm m b o k p <-> 0 <= o < frame_size fi.
  Proof.
    intros; eapply perm_stack_eq'; eauto.
    apply Mem.agree_perms_mem.
  Qed.
  
  Lemma size_stack_app:
    forall l1 l2,
      StackADT.size_stack (l1 ++ l2) = StackADT.size_stack l1 + StackADT.size_stack l2.
  Proof.
    induction l1; simpl; intros; eauto.
    rewrite IHl1. omega.
  Qed.

  Lemma val_inject_set:
    forall j rs1 rs2 r0 r1
      (RINJ: r0 <> r1 -> Val.inject j (rs1 r0) (rs2 r0))
      v v' (VINJ: Val.inject j v v'),
      Val.inject j ((rs1 # r1 <- v) r0) ((rs2 # r1 <- v') r0).
  Proof.
    intros.
    destruct (PregEq.eq r1 r0); subst; auto.
    rewrite ! Pregmap.gss; auto.
    rewrite ! Pregmap.gso by auto. auto.
  Qed.

  Lemma val_inject_undef_regs:
    forall l j rs1 rs2
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
      r,
      Val.inject j (undef_regs l rs1 r) (undef_regs l rs2 r).
  Proof.
    induction l; simpl; intros; eauto.
    apply IHl.
    intros; apply val_inject_set; auto.
  Qed.

  Lemma val_inject_nextinstr:
    forall j rs1 rs2 r sz
      (RINJ: forall r0, r0 = r \/ r0 = PC -> Val.inject j (rs1 r0) (rs2 r0)),
      Val.inject j (nextinstr rs1 sz r) (nextinstr rs2 sz r).
  Proof.
    unfold nextinstr.
    intros.
    apply val_inject_set; auto. 
    apply Val.offset_ptr_inject; auto.
  Qed.

  Lemma find_var_info_none_ge:
    forall b,
      (Genv.genv_next ge <= b)%positive ->
      Genv.find_var_info ge b = None.
  Proof.
    unfold Genv.find_var_info. intros.
    destr.
    apply Genv.genv_defs_range in Heqo. xomega.
  Qed.

  Lemma load_record_stack_blocks:
    forall m fi m',
      Mem.record_stack_blocks m fi = Some m' ->
      forall chunk b ofs,
        Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
  Proof.
    intros.
    destruct (plt b (Mem.nextblock m)).
    eapply Mem.load_unchanged_on_1.
    eapply Mem.strong_unchanged_on_weak.
    eapply Mem.record_stack_block_unchanged_on; eauto.
    apply p.
    instantiate (1 := fun _ _ => True); simpl; auto.
    destruct (Mem.load chunk m b ofs) eqn:LOAD.
    apply Mem.load_valid_access in LOAD. destruct LOAD.
    exfalso; apply n.
    eapply Mem.perm_valid_block. apply H0.
    instantiate (1:= ofs). generalize (size_chunk_pos chunk); omega.
    clear LOAD.
    destruct (Mem.load chunk m' b ofs) eqn:LOAD; auto.
    apply Mem.load_valid_access in LOAD. destruct LOAD.
    exfalso; apply n.
    eapply Mem.perm_valid_block.
    specialize (H0 ofs). trim H0. generalize (size_chunk_pos chunk); omega.
    rewrite_perms_bw H0.
    apply H0.
  Qed.
  
  Lemma size_frames_nil: size_frames (None,nil) = 0.
  Proof.
    reflexivity.
  Qed.

  Lemma size_frames_one:
    forall f,
      size_frames (Some f , nil) = align (frame_adt_size f) 8.
  Proof.
    intros. rewrite size_frames_cons. simpl. unfold size_frame.
    apply Z.max_l. etransitivity.
    2: apply align_le.
    apply frame_adt_size_pos. omega.
  Qed.

  Opaque Mem.stack_limit.



  Lemma in_stack_inj_below:
    forall j P l
      (IS: inject_perm_stack j P l)
      b fi
      (INFRAMES: in_stack' l (b,fi)),
    exists l1 l2,
      l = l1 ++ l2 /\
      j b = Some (bstack, Mem.stack_limit - size_active_stack l2).
  Proof.
    induction 1; simpl; intros; eauto. easy.
    - destruct INFRAMES as [[]|INFRAMES].
      edestruct IHIS as (l1 & l2 & EQ & JB); eauto.
      exists ((None,r)::l1),l2; split; auto. simpl. subst. reflexivity.
    - destruct INFRAMES as [IFR|INSTACK].
      + red in IFR. simpl in IFR.
        red in IFR. rewrite BLOCKS in IFR.
        destruct IFR as [EQ|[]]. inv EQ.
        rewrite JB.
        exists nil, ((Some fr, r)::l). simpl. split; auto.
        unfold size_frame. rewrite SIZE. f_equal. f_equal. omega.
      + edestruct IHIS as (l1 & l2 & EQ & JB'); eauto.
        exists ((Some fr,r)::l1),l2; split; auto. simpl. subst. reflexivity.
  Qed.

  Lemma size_active_smaller:
    forall s,
      size_active_stack s <= size_stack s.
  Proof.
    induction s; simpl; intros; eauto. omega.
    apply Z.add_le_mono; auto.
    destruct a; simpl. rewrite size_frames_cons.
    apply Z.le_max_l.
  Qed.

  Lemma size_active_stack_below:
    forall m,
      size_active_stack (Mem.stack m) < Mem.stack_limit.
  Proof.
    intros. eapply Z.le_lt_trans.
    2: apply Mem.size_stack_below.
    apply size_active_smaller.
  Qed.

  Lemma size_active_stack_pos:
    forall s,
      0 <= size_active_stack s.
  Proof.
    induction s; simpl; intros; eauto. omega.
    generalize (opt_size_frame_pos (fst a)); omega.
  Qed.
  
  Lemma size_frame_rew:
    forall b fi fr,
      size_frame (make_singleton_frame_adt' b fi (frame_size fr)) = align (frame_size fr) 8.
  Proof.
    unfold size_frame; simpl. intros.
    rewrite Z.max_r; auto.
    apply frame_size_pos.
  Qed.

  Lemma align_frame_size_pos:
    forall fr,
      0 <= align (frame_size fr) 8.
  Proof.
    intros.
    etransitivity.
    2: apply align_le; try omega.
    apply frame_size_pos.
  Qed.
  
 Lemma alloc_inject:
    forall j ostack m1 (rs1 rs1': regset) fi b m1' m5 ofs_ra m2 m4 sz,
      match_states j (Ptrofs.unsigned ostack) (State rs1 m1) (State rs1' m1') ->
      top_tframe_tc (Mem.stack m1) ->
      Mem.alloc m1 0 (frame_size fi) = (m2, b) ->
      Mem.store Mptr m2 b ofs_ra rs1#RA = Some m4 ->
      Mem.record_stack_blocks m4 (make_singleton_frame_adt' b  fi (frame_size fi)) = Some m5 ->
      0 <= ofs_ra <= Ptrofs.max_unsigned ->
      0 < frame_size fi ->
      let sp := Val.offset_ptr (rs1' RSP) (Ptrofs.neg (Ptrofs.repr (align (frame_size fi) 8))) in
      let newostack := Ptrofs.unsigned ostack - align (frame_size fi) 8 in
      let rs2 := nextinstr ( rs1 #RAX <- (rs1#RSP)  #RSP <- (Vptr b Ptrofs.zero)) sz in
      let rs2' := nextinstr (rs1' #RAX <- (rs1'#RSP) #RSP <- sp) sz in
      exists j',
        (forall bb, j' bb = if peq bb b then Some (bstack, newostack) else j bb)
        /\ inject_incr j j'
        /\
        exists m4',
          Mem.storev Mptr m1' (Val.offset_ptr sp (Ptrofs.repr ofs_ra)) rs1'#RA = Some m4'
          /\ match_states j' newostack (State rs2 m5) (State rs2' m4').
  Proof.
    intros j ostack m1 rs1 rs1' fi b m1' m5 ofs_ra m2 m4 sz
           MS TIN ALLOC STORE RSB REPRretaddr sizepos
           sp newostack rs2 rs2'.
    inv MS.
    assert (RNGframe: 0 <= align (frame_size fi) 8 <= Ptrofs.max_unsigned).
    {
      split. apply align_frame_size_pos.
      etransitivity. 2: eapply Z.lt_le_incl, Z.lt_le_trans.
      2: apply (size_active_stack_below m5).
      repeat rewrite_stack_blocks. simpl.
      rewrite size_frame_rew. generalize (size_active_stack_pos r). intros; omega.
      apply Mem.stack_limit_range.
    }
    assert (SP: sp = Vptr bstack (Ptrofs.repr newostack)).
    {
      unfold sp. rewrite RSPEQ. simpl. f_equal.
      rewrite <- Ptrofs.sub_add_opp. unfold newostack.
      unfold Ptrofs.sub. rewrite H1. rewrite Ptrofs.unsigned_repr; auto.
    }
    assert (REPRcur: align (frame_size fi) 8 <= Ptrofs.unsigned ostack0 <= Ptrofs.max_unsigned).
    {
      split. 2: apply Ptrofs.unsigned_range_2.
      red in AGSP. specialize (AGSP _ RSPEQ). rewrite AGSP.
      apply Z.le_add_le_sub_r.
      eapply Z.lt_le_incl, Z.le_lt_trans. 2: apply (size_active_stack_below m5).
      repeat rewrite_stack_blocks. intro. 
      simpl. rewrite EQ1. simpl. rewrite size_frame_rew. omega.
    }
    assert (REPR: 0 <= newostack <= Ptrofs.max_unsigned).
    {
      unfold newostack. omega.
    }
    generalize (Mem.alloc_left_mapped_inject _ _ _ _ _ _ _ _ _ newostack MINJ ALLOC VB).
    intro A.
    trim A. now omega.
    trim A. intros; right; eapply PBS; now eauto.
    trim A.
    {
      intros; eapply Mem.perm_implies. eapply PBSL; eauto.
      split. omega.
      unfold newostack.
      eapply Z.lt_le_trans with (Ptrofs.unsigned ostack).
      cut (frame_size fi <= align (frame_size fi) 8). omega.
      apply align_le. omega.
      erewrite <- H1, (AGSP _ RSPEQ); eauto.
      generalize (size_active_stack_pos (Mem.stack m1)); intros. omega.
      simpl in H0. auto.
    }
    trim A.
    {
      red.
      intros.
      unfold newostack.
      eapply Zdivides_trans with 8.
      destruct chunk; try (exists 8; reflexivity);
        try (exists 4; reflexivity);
        try (exists 2; reflexivity);
        try (exists 1; reflexivity).
      apply Z.divide_sub_r.
      rewrite <- H1. apply SPAL; auto.
      apply align_divides. omega.
    }
    trim A.
    {
      intros b0 delta' ofs k p JB PERM RNG.
      generalize (NIB _ _ _ _ _ JB PERM).
      generalize (align_le (frame_size fi) 8).
      unfold newostack in RNG. simpl in RNG. omega.
    }
    trim A.
    {
      revert NS. unfold no_stack.
      intros (fr & fi0 & rr & EQS & BLOCKS & ZERO & PUBLIC & SIZE). rewrite EQS.
      simpl. intros fi1 [INFR|INS]; subst.
      - red in INFR.  simpl in INFR. red in INFR; revert INFR.
        rewrite <- BLOCKS.
        intros [EQ|[]]. inv EQ.
        intros; apply PUBLIC.
      - exploit Mem.stack_norepet. rewrite EQS.
        intro ND; inv ND.
        exfalso; eapply H3. 2: eapply in_stack'_in_stack; apply INS.
        red; simpl. unfold get_frame_blocks. rewrite <- BLOCKS. left; reflexivity.
    }
    destruct A as (f' & MINJ' & INCR & EQ1 & EQ2).
    exists f'.
    split.
    {
      intros.
      destruct peq; subst; eauto.
    }
    split; auto.
    (* store return address *)
    exploit Mem.store_mapped_inject. apply MINJ'. simpl in *; eauto. eauto. 
    eapply val_inject_incr; eauto. intros (m4' & STORE' & MINJ3).
    assert (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr newostack) (Ptrofs.repr ofs_ra)) =
            ofs_ra + newostack) as EQ'.
    2: simpl. 
    rewrite Ptrofs.add_commut.
    erewrite Mem.address_inject; eauto.
    rewrite Ptrofs.unsigned_repr; omega.
    exploit Mem.store_valid_access_3. exact STORE.
    intro VA; eapply Mem.store_valid_access_1 in VA; eauto. destruct VA.
    eapply H. 
    rewrite Ptrofs.unsigned_repr; generalize (size_chunk_pos Mptr); omega.
    rewrite SP. simpl. unfold Ptrofs.add.
    rewrite (Ptrofs.unsigned_repr _ REPR).
    rewrite (Ptrofs.unsigned_repr _ REPRretaddr) in *.
    rewrite Ptrofs.unsigned_repr. rewrite Z.add_comm. rewrite STORE'.
    eexists; split; eauto.
    (* record the stack block *)
    destruct NS as (frstack & fstack & rr & EQstk & BLOCKS & ZERO & PUB & SZ).
    exploit Mem.record_stack_block_inject_left_zero. apply MINJ3. 3: eauto.
    repeat rewrite_stack_blocks. rewrite EQstk. constructor; reflexivity.
    {
      red. simpl.
      intros ? EQ HPF. inv EQ.
      exists frstack; split; auto.
      red. simpl.
      constructor; auto. simpl. rewrite EQ1.
      intros b2 delta A; inv A.
      rewrite <- BLOCKS. simpl.
      eexists; split. eauto.
      constructor.
      intros; eapply stack_perm_le_public. intros; apply PUB.
      intros; rewrite SZ.
      unfold newostack.
      rewrite <- H1.
      red in AGSP. apply AGSP in RSPEQ.  rewrite RSPEQ.
      cut (frame_size fi <= align (frame_size fi) 8).
      generalize (size_active_stack_pos (Mem.stack m1)). omega.
      apply align_le; omega.
    }
    intro MINJ4.
    (* proving the final match_states *)
    rewrite <- (Ptrofs.unsigned_repr newostack) by omega.
    destruct lprog.
    {
      revert init_sp_ptr. unfold init_sp. simpl in STK. subst.
      clear STK. inv TIN. simpl. unfold current_frame_sp; rewrite H0. inversion 1.
    }
    simpl in STK.
    assert (
        Mem.stack m5 = (Some (make_singleton_frame_adt' b fi (frame_size fi)), opt_cons (fst t) (snd t)) :: lprog ++ init_stk
        /\ Mem.stack m1 = (None, (snd t)) :: lprog ++ init_stk
      ).
    {
      repeat rewrite_stack_blocks.
      rewrite STK. inversion 1; subst. simpl. auto.
    }
    destruct H as (STK5 & STK1).
    econstructor. eauto.
    - rewrite STK5. rewrite app_comm_cons. reflexivity.
    - simpl. reflexivity.
    - unfold rs2. rewrite nextinstr_rsp, Pregmap.gss. eauto.
    - intros r.
      unfold rs2, rs2'.
      apply val_inject_nextinstr. intros.
      apply val_inject_set; eauto. intro. apply val_inject_set. intros; eauto.
      eapply val_inject_incr; eauto.
      subst sp. simpl. rewrite RSPEQ. econstructor; eauto. rewrite Ptrofs.add_zero_l; auto.
      unfold newostack. rewrite <- Ptrofs.sub_add_opp. unfold Ptrofs.sub. rewrite <- H1. rewrite Ptrofs.unsigned_repr; auto.
    - red. rewnb. eauto.
    - red. unfold rs2'. rewrite nextinstr_rsp. rewrite Pregmap.gss. rewrite SP. inversion 1. subst.
      repeat rewrite_stack_blocks.
      rewrite Ptrofs.unsigned_repr by auto.
      unfold newostack in *.
      rewrite <- H1. rewrite (AGSP _ RSPEQ).
      intro EQ0; rewrite EQ0. simpl. rewrite size_frame_rew. omega.
    - red. intros ostack1 A. unfold rs2' in A. rewrite nextinstr_rsp in A. rewrite Pregmap.gss in A.
      rewrite SP in A. inversion A. subst.
      rewrite Ptrofs.unsigned_repr by omega.
      unfold newostack.
      apply Z.divide_sub_r. rewrite <- H1. apply SPAL. auto.
      apply align_divides. omega.
    - red. intros ofs k p PERM.
      repeat rewrite_perms_bw PERM. eauto.
    - red; intros.
      repeat rewrite_perms_fw. eauto.
    - red. repeat rewrite_stack_blocks. exists frstack, fstack, rr; rewrite EQstk, <- BLOCKS, <- ZERO. eauto.
    - unfold rs2'. rewrite nextinstr_rsp, Pregmap.gss. auto.
    - rewrite Ptrofs.unsigned_repr by omega.
      red. intros b0 delta o k p JB PERM.
      repeat rewrite_perms_bw PERM.
      destruct peq.
      * subst. rewrite EQ1 in JB. clear EQstk. inv JB. split. omega.
        rewrite STK5. rewrite in_stack_cons. rewrite in_frames_cons.
        left. eexists; split; eauto. unfold in_frame; simpl; auto.
      * split. unfold newostack.
        transitivity (Ptrofs.unsigned ostack).
        -- generalize (align_le ((frame_size fi)) 8). omega.
        -- rewrite <- H1.
          rewrite EQ2 in JB; auto. 
          exploit NIB; eauto. tauto.
        -- rewrite STK5.
           rewrite in_stack_cons.
           right.
           edestruct NIB; eauto. rewrite <- EQ2; eauto.
           rewrite STK1 in H0. rewrite in_stack_cons in H0. destruct H0; auto. easy.
    - rewrite STK5.
      rewrite STK1 in IS. inv IS. 
      econstructor; try reflexivity; eauto.
      eapply inject_stack_incr; eauto.
      eapply inject_stack_more_perm with (P:=Mem.perm m1).
      intros; repeat rewrite_perms.
      exploit Mem.perm_valid_block; eauto. intro VB'.
      generalize (Mem.fresh_block_alloc _ _ _ _ _ ALLOC). destr. auto.
      rewrite EQ1. f_equal. f_equal.
      unfold newostack.
      rewrite <- H1.
      rewrite AGSP. rewrite STK1. simpl. omega. auto. 
      simpl. rewrite Z.max_r; auto. omega.
      intros. repeat rewrite_perms. destr.
    - intros b0 fi0 delta INSTK FB0 b' o delta' k p FB1 P1.
      revert INSTK. rewrite STK5. intro INSTK.
      simpl in INSTK.
      repeat rewrite_perms_bw P1.
      destruct INSTK as [IFR|INSTK].
      + red in IFR. simpl in IFR. red in IFR. simpl in IFR. destruct IFR as [EQ|[]]. inv EQ.
        rewrite FB0 in EQ1; inv EQ1.
        destr_in P1.
        * subst. rewrite FB0 in FB1; inv FB1. omega.
        * rewrite EQ2 in FB1 by auto.
          eapply NIB in P1; eauto.
          destruct P1 as (LE & IN).
          unfold newostack.
          rewrite <- H1.
          omega.
      + assert (b0 <> b). intro; subst.
        exploit Mem.stack_norepet. rewrite STK5. intro ND; inv ND.
        eapply in_stack'_in_stack in INSTK; eauto. eapply H3 in INSTK; eauto.
        left. reflexivity.
        rewrite EQ2 in FB0 by auto.
        intro RNG.
        assert (0 < frame_size fi0).
        destruct (zlt 0 (frame_size fi0)); auto.
        assert (frame_size fi0 = 0). generalize (frame_size_pos fi0); omega. rewrite H0 in RNG.
        change (align 0 8) with 0 in RNG. omega.
        destr_in P1. 
        * subst. rewrite EQ1 in FB1; inv FB1.
          cut (newostack + (frame_size fi)  <= delta). omega.
          unfold newostack. rewrite <- H1.
          rewrite AGSP; auto.
          rewrite STK1 in IS. inv IS.
          eapply in_stack_inj_below in INSTK; eauto.
          destruct INSTK as (l1 & l2 & EQADT & JB0). rewrite FB0 in JB0. inv JB0.
          rewrite STK1. simpl. rewrite EQADT.

          Lemma size_active_stack_app:
            forall l1 l2,
              size_active_stack (l1 ++ l2) = size_active_stack l1 + size_active_stack l2.
          Proof.
            induction l1; simpl; intros; eauto.
            rewrite IHl1. omega.
          Qed.
          rewrite size_active_stack_app.
          generalize (size_active_stack_pos l1).
          cut (frame_size fi <= align (frame_size fi) 8). omega.
          apply align_le; omega.
        * eapply IP. rewrite STK1. right. eauto. eauto.
          rewrite <- EQ2. apply FB1. auto. eauto. omega.
    - eauto.
    - eauto.
    - destruct GLOBSYMB_INJ; split.
      + intros. eapply INCR. eauto.
      + intros. destruct (peq b1 b).
        subst; rewrite EQ1 in H2. clear EQstk. inv H2.
        simpl.
        unfold Genv.block_is_volatile.
        unfold Genv.find_var_info.
        replace (Genv.find_def ge bstack) with (None (A:=globdef Asm.fundef unit)).
        replace (Genv.find_def ge b) with (None (A:=globdef Asm.fundef unit)).
        auto.
        unfold Genv.find_def.
        destruct (Maps.PTree.get b (Genv.genv_defs ge)) eqn:EQdef; auto.
        apply Genv.genv_defs_range in EQdef.
        exploit Mem.fresh_block_alloc. eauto. red. xomega. easy.
        unfold Genv.find_def.
        destruct (Maps.PTree.get bstack (Genv.genv_defs ge)) eqn:EQdef; auto.
        apply Genv.genv_defs_range in EQdef.
        unfold bstack in EQdef. xomega.
        rewrite EQ2 in H2.
        eauto.
        auto.
    - erewrite Mem.record_stack_block_nextblock. 2: eauto.
      erewrite Mem.nextblock_store. 2 : eauto.
      erewrite Mem.nextblock_alloc. 2: eauto. xomega.
    - erewrite Mem.nextblock_store. 2 : eauto. xomega.
    - rewrite STK5. simpl. right. rewrite STK1 in SPinstack. destruct SPinstack; auto. easy.
    - rewrite Z.add_comm, <- EQ'. apply Ptrofs.unsigned_range_2.
  Qed.

  Lemma max_l_divide l: (8 | max_l (map size_frame l)).
  Proof.
    induction l; simpl. exists 0; omega.
    rewrite Zmax_spec.
    destr.
    apply align_divides. omega.
  Qed.
  
  Lemma opt_size_frame_divides f:
    (8 | opt_size_frame f).
  Proof.
    destruct f.
    apply align_divides. omega.
    exists 0; simpl; omega.
  Qed.

  Lemma size_frames_divides f:
    (8 | size_frames f).
  Proof.
    unfold size_frames.
    destruct f; simpl. 
    rewrite Zmax_spec.
    destr.
    apply opt_size_frame_divides.
    apply max_l_divide.
  Qed.

  Lemma size_stack_divides l:
    (8 | size_stack l).
  Proof.
    induction l; simpl; intros; eauto.
    exists 0; omega.
    apply Z.divide_add_r. auto. apply size_frames_divides; auto.
  Qed.

  Lemma size_active_stack_divides l:
    (8 | size_active_stack l).
  Proof.
    induction l; simpl; intros; eauto.
    exists 0; omega.
    apply Z.divide_add_r. auto. apply opt_size_frame_divides.
  Qed.
  
  Lemma inject_stack_init_sp:
    forall j P l,
      inject_perm_stack j P l ->
      forall b,
        in_stack l b ->
        exists o,
          j b = Some (bstack, o).
  Proof.
    induction 1; simpl; intros bb INS. easy.
    rewrite in_stack_cons in INS. destruct INS as [INF|INS]. easy. eauto.
    rewrite in_stack_cons in INS. destruct INS as [INF|INS].
    rewrite in_frames_cons in INF. destruct INF as (f1 & EQ & IFR); inv EQ.
    edestruct in_frame_info as (ffi & IFRR). eauto.
    rewrite BLOCKS in IFRR. destruct IFRR as [IFRR|[]]. inv IFRR. eauto.
    eauto.
  Qed.

  Lemma init_sp_inj:
    forall j P l,
      inject_perm_stack j P l ->
      in_stack l binit_sp ->
      exists o,
        Val.inject j init_sp (Vptr bstack o).
  Proof.
    intros. edestruct inject_stack_init_sp; eauto.
    rewrite init_sp_ptr. exists (Ptrofs.repr x).
    econstructor; eauto. rewrite Ptrofs.add_zero_l. auto.
  Qed.

  Ltac use_ains :=
    repeat match goal with
           | AINS: asm_instr_no_stack ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?init_stk _ _ ?i _ ?m1 = Next _ ?m2 |-
             context [Mem.stack ?m2] =>
             let AINS_stack := fresh "AINS_stack" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (AINS_stack & _); rewrite ! AINS_stack;
             clear AINS_stack
           | AINS: asm_instr_no_stack ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?init_stk _ _ ?i _ ?m1 = Next _ ?m2,
                            H: context [Mem.stack ?m2] |- _ =>
             let AINS_stack := fresh "AINS_stack" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (AINS_stack & _); rewrite ! AINS_stack in H;
             clear AINS_stack

           | AINS: asm_instr_no_stack ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?init_stk _ _ ?i _ ?m1 = Next _ ?m2 |-
             context [Mem.perm ?m2 _ _ _ _] =>
             let AINS_perm := fresh "AINS_perm" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (_ & AINS_perm); rewrite ! AINS_perm;
             clear AINS_perm
           | AINS: asm_instr_no_stack ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?init_stk _ _ ?i _ ?m1 = Next _ ?m2,
                            H : context [Mem.perm ?m2 _ _ _ _] |- _ =>
             let AINS_perm := fresh "AINS_perm" in
             edestruct (AINS UNC _ _ _ _ _ _ _ _ _ EI) as (_ & AINS_perm); rewrite ! AINS_perm in H;
             clear AINS_perm
           | AINR: asm_instr_no_rsp ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?init_stk _ _ ?i ?rs1 _ = Next ?rs2 _ |-
             context [?rs2 (IR RSP)] =>
             rewrite (AINR UNC _ _ _ _ _ _ _ _ _ EI)
           | AINR: asm_instr_no_rsp ?i,
                   UNC: stack_invar ?i = true,
                        EI: Asm.exec_instr ?init_stk _ _ ?i ?rs1 _ = Next ?rs2 _,
                            H: context [?rs2 (IR RSP)] |- _ =>
             rewrite (AINR UNC _ _ _ _ _ _ _ _ _ EI) in H
                                                          
           end.

  Lemma is_unchanged_stack_invar:
    forall i,
      is_unchanged i = true ->
      stack_invar i = true.
  Proof.
    intros. destruct i. destruct i eqn:?; simpl in *; try congruence.
  Qed.

  (* Lemma clear_stage_inject_left: *)
  (*   forall j n g m1 m2 m1', *)
  (*     Mem.inject j (S n :: g) m1 m2 -> *)
  (*     le 1 n -> *)
  (*     Mem.clear_stage m1 = Some m1' -> *)
  (*     (forall b : block, is_stack_top (Mem.stack m1) b -> forall (o : Z) (k : perm_kind) (p : permission), ~ Mem.perm m1 b o k p) -> *)
  (*     Mem.inject j (S n :: g) m1' m2. *)
  (* Proof. *)
  (*   intros j n g m1 m2 m1' INJ LE CS TOP. *)
  (*   unfold Mem.clear_stage in CS; repeat destr_in CS. *)
  (*   apply Mem.inject_push_new_stage_left. *)
  (*   eapply Mem.unrecord_stack_block_inject_left; eauto. *)
  (* Qed. *)

  Lemma zle_zlt:
    forall lo hi o,
      zle lo o && zlt o hi = true <-> lo <= o < hi.
  Proof.
    intros.
    destruct (zle lo o), (zlt o hi); intuition; try congruence; try omega.
  Qed.

  Lemma max_align:
    forall x, 0 <= x ->
         Z.max 0 (align x 8) = align (Z.max 0 x) 8.
  Proof.
    intros.
    rewrite ! Z.max_r; auto.
    etransitivity. 2: apply align_le. auto. omega.
  Qed.

  Lemma mod_divides:
    forall a b c,
      c <> 0 ->
      (a | c) ->
      (a | b) ->
      (a | b mod c).
  Proof.
    intros.
    rewrite Zmod_eq_full.
    apply Z.divide_sub_r. auto.
    apply Z.divide_mul_r. auto. auto.
  Qed.
  
  Lemma exec_instr_inject':
    forall j ostack m1 m2 rs1 rs2 f i rs1' m1'
      (MS: match_states j ostack (State rs1 m1) (State rs2 m2))
      (AINR: asm_instr_no_rsp i)
      (AINS: asm_instr_no_stack i)
      (EI: Asm.exec_instr init_stk ge f i rs1 m1 = Next rs1' m1'),
      exists j' ostack' rs2' m2',
        exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ match_states j' ostack' (State rs1' m1') (State rs2' m2')
        /\ inject_incr j j'.
  Proof.
    intros. 
    destruct (is_unchanged i) eqn:ISUNCH.
    - inversion MS.
      edestruct exec_instr_inject as (rs2' & m2' & EXEC' & MINJ' & RINJ'); eauto.
      exists j, ostack, rs2', m2'; split; [|split]; eauto.
      destruct i as (i & szinfo); destruct i; simpl in *; eauto; try congruence.
      generalize (is_unchanged_stack_invar _ ISUNCH) as SINVAR. intro.
      subst. eapply match_states_intro; eauto; try now ((intros; use_ains; eauto) || (red; intros; use_ains; eauto)).
      + eapply asmgen_nextblock_forward in EXEC'.
        red in VB |- *. xomega.
      + use_ains. 
        eapply perm_stack_inv. eauto.
        intros; use_ains. tauto.
      + etransitivity. apply GlobLe.
        eapply asmgen_nextblock_forward; eauto.
      + etransitivity. apply GlobLeT.
        eapply asmgen_nextblock_forward; eauto.
        
    - destruct i as (i & szinfo).
      destruct i; simpl in *; try congruence.
      + (* call_s *)
        inv EI. inv MS. do 4 eexists. split. eauto. split. econstructor; eauto.
        * instantiate (1:= _::_). simpl. eapply Mem.inject_push_new_stage_left; eauto.
        * rewrite_stack_blocks. rewrite STK. simpl. reflexivity.
        * intros; apply val_inject_set; auto.
          intros; apply val_inject_set; auto.
          apply Val.offset_ptr_inject; auto.
          unfold Genv.symbol_address. destr; auto.
          destruct GLOBSYMB_INJ. apply H in Heqo.
          econstructor; eauto.
        * red. rewrite_stack_blocks. simpl.
          repeat rewrite Pregmap.gso by congruence.
          rewrite Z.add_0_r. eauto.
        * red. intros b delta o k p. rewrite_perms. rewrite_stack_blocks. rewrite in_stack_cons.
          intros. exploit NIB; eauto. tauto.
        * rewrite_stack_blocks. constructor.
          eapply inject_stack_more_perm. 2: eauto. intros. rewrite_perms. auto.
        * red. rewrite_stack_blocks. simpl. intros b fi delta H H0 b' o delta' k p. rewrite_perms. eapply IP; eauto. tauto.
        * rewnb. auto.
        * rewrite_stack_blocks. simpl; auto.
        * red. auto.
      + (* call_r *)
        inv EI. inv MS. do 4 eexists. split. eauto. split. econstructor; eauto.
        * instantiate (1:= (None,nil)::lprog). simpl. eapply Mem.inject_push_new_stage_left; eauto.
        * rewrite_stack_blocks. rewrite STK; auto. 
        * intros; apply val_inject_set; auto.
          intros; apply val_inject_set; auto.
          apply Val.offset_ptr_inject; auto.
        * red. rewrite_stack_blocks. simpl.
          repeat rewrite Pregmap.gso by congruence.
          rewrite Z.add_0_r. eauto.
        * red. intros b delta o k p. rewrite_perms. rewrite_stack_blocks. rewrite in_stack_cons.
          intros. exploit NIB; eauto. tauto.
        * rewrite_stack_blocks. constructor. eapply inject_stack_more_perm. 2: eauto. intros; rewrite_perms; auto.
        * red. rewrite_stack_blocks. simpl. intros b fi delta H H0 b' o delta' k p. rewrite_perms. eapply IP; eauto. tauto.
        * rewnb. auto.
        * rewrite_stack_blocks. simpl; auto.
        * red. auto.
      + (* ret *)
        unfold Asm.exec_instr in EI. simpl in EI.
        repeat destr_in EI.
        eexists j,ostack, _, _; split; eauto. split; auto.
        inv MS.
        assert (exists f rprog, lprog = f :: rprog).
        {
          inv t.
          rewrite <- H in IS.
          destruct lprog. exfalso.
          revert init_sp_ptr; unfold init_sp; simpl in STK; rewrite <- STK.
          rewrite <- H. simpl. unfold current_frame_sp. rewrite H0. inversion 1.
          eauto.
        }
        destruct H as (ff & rprog & EQ). subst.
        simpl in MINJ.
        econstructor; eauto.
        * eapply Mem.unrecord_stack_block_inject_left_zero; eauto.
          red. inv t. constructor. unfold in_frames; rewrite H0. easy.
          omega.
        * rewrite_stack_blocks.
          rewrite STK. simpl. eauto.
        * simpl; intros. apply val_inject_set; auto.
          intros; apply val_inject_set; auto.
        * red. repeat rewrite Pregmap.gso by congruence.
          rewrite_stack_blocks. inv t. rewrite EQ in H; inv H. simpl.
          intros; erewrite AGSP; eauto.
          rewrite EQ. simpl. rewrite H0. simpl.  omega.
        * red; intros. rewrite_stack_blocks. revert EQ. inv t. inversion 1; subst. simpl.
          red in NIB. rewrite <- H1 in NIB.
          revert H0. rewrite_perms. intro.
          exploit NIB; eauto. rewrite in_stack_cons; unfold in_frames; rewrite H2. simpl. tauto.
        * rewrite_stack_blocks. revert EQ. inv t. inversion 1; subst. simpl.
          rewrite <- H in IS. inv IS.
          eapply inject_stack_more_perm. 2: eauto. intros; rewrite_perms. auto. inv H0.
        * red. rewrite_stack_blocks. revert EQ. inv t. inversion 1; subst. simpl.
          red in IP. rewrite <- H in IP.
          intros. revert H4; rewrite_perms. eapply IP; eauto.
          right. auto.
        * rewnb. auto.
        * rewrite_stack_blocks. revert EQ. inv t. inversion 1; subst. rewrite <- H in SPinstack. simpl.
          simpl in SPinstack. destruct SPinstack. red in H1. rewrite H0 in H1; easy. auto.

     + (* allocframe *)
       clear ISUNCH.
       unfold Asm.exec_instr in EI; simpl in EI.
       repeat destr_in EI.
       inversion MS; subst.
       edestruct alloc_inject as (j' & JSPEC & INCR & m4' & STORE2 & MS') ; eauto.
       apply Ptrofs.unsigned_range_2.
       simpl in *.
       rewrite Ptrofs.repr_unsigned in STORE2. setoid_rewrite STORE2.
       eexists j', _, _, _; split; eauto.

     + (* freeframe *)
       unfold Asm.exec_instr in EI; simpl in EI.
       repeat (destr_in EI; [idtac]).
       clear ISUNCH.
       rename Heqv0 into RS1RSP.
       rename Heqo into LOADRA.
       rename Heqb0 into CHECKFRAME.
       rename Heqo0 into FREE.
       rename Heqo1 into UNRECORD.
       rename Heqo2 into ISDEF.
       inv MS. rewrite RS1RSP in RSPzero. destruct RSPzero as [bb EQ]; inv EQ.
       exploit Mem.loadv_inject. eauto. apply LOADRA.
       apply Val.offset_ptr_inject. rewrite <- RS1RSP; auto.
       intros (ra' & LOADRA' & INJra).
       rewrite LOADRA'.
       unfold check_top_frame in CHECKFRAME.
       repeat destr_in CHECKFRAME.
       (* repeat destr_in AGSP1. *)
       repeat rewrite andb_true_iff in H0.
       destruct H0 as (A & B).
       destruct Forall_dec; simpl in A; try congruence. clear A.
       apply ZEQ in B.
       set (newostack := Ptrofs.unsigned ostack0 + align ((frame_adt_size f0)) 8).

       assert (RNGframe: 0 <= align (frame_adt_size f0) 8 < Ptrofs.max_unsigned).
       {
         generalize (size_active_stack_below m1).
         generalize (size_active_stack_pos (Mem.stack m1)). rewrite Heqs.
         generalize (size_active_stack_pos s).
         generalize (Mem.stack_limit_range).
         simpl. unfold size_frame. 
         split. apply size_frame_pos.
         omega.
       }

       exploit Mem.free_left_inject. apply MINJ. eauto. intro MINJ'.
       exploit Mem.tailcall_stage_inject_left. apply MINJ'. eauto.
       intros INJ. 
       exists j, newostack; eexists; eexists; split; [|split]; eauto.
       generalize (RINJ RSP). rewrite RS1RSP.
       inversion 1 as [ff|ff|ff|ff|? ? ? ? ? INJB ? x EQRSP|ff]; subst.
       symmetry in EQRSP.
       rewrite Ptrofs.add_zero_l in *.
       inversion IS. subst. rewrite BLOCKS in f1. inv f1. red in H2; simpl in H2; destruct H2 as [? _]; subst. clear H3. rewrite JB in INJB; inv INJB.
       specialize (AGSP _ EQRSP).
       specialize (SPAL _ EQRSP).
       rewrite EQRSP in RSPEQ. inv RSPEQ.
       assert (0 <= Mem.stack_limit - size_active_stack (Mem.stack m1') <= Ptrofs.max_unsigned) as RNGnewofs. 
       {
         generalize (size_active_stack_below m1').
         generalize (size_active_stack_pos (Mem.stack m1')).
         generalize (Mem.stack_limit_range).
         omega.
       }
       assert (0 <= newostack <= Ptrofs.max_unsigned) as RNGnew.
       {
         unfold newostack.
         rewrite AGSP. rewrite Heqs. simpl.
         revert RNGnewofs. repeat rewrite_stack_blocks. simpl.
         rewrite Heqs. inversion 1; subst. unfold size_frame. intros; omega.
       }
       rewrite <- (Ptrofs.unsigned_repr newostack) by omega.
       destruct lprog.
       {
         simpl in STK.
         revert init_sp_ptr; unfold init_sp; simpl in STK; rewrite <- STK. simpl.
         unfold current_frame_sp. simpl. repeat destr. inv BLOCKS.
         red in c. simpl in c.
         revert c. unfold current_frame_sp. simpl. rewrite Heql0.
         repeat rewrite_stack_blocks. rewrite in_stack_cons.
         rewrite Heqs. inversion 1. subst s f1. intros [[]|INS]. inversion 1. subst b.
         exploit Mem.stack_norepet; rewrite Heqs. clear STK. intro ND; inv ND.
         edestruct (H4 binit_sp). red. simpl. eapply in_frame'_in_frame. red; rewrite Heql0.
         left; reflexivity.
         eauto.
       }
       eapply match_states_intro with (lprog := (None, f0::l) :: lprog ); eauto.
       * repeat rewrite_stack_blocks. rewrite Heqs. simpl. inversion 1; subst. inv STK.
         simpl. reflexivity.
       * rewrite nextinstr_rsp. rewrite Pregmap.gso by congruence.
         rewrite Pregmap.gss.
         simpl in ISDEF. unfold is_ptr in ISDEF.
         destr_in ISDEF. inv ISDEF. unfold current_sp, current_frame_sp in Heqv1.
         revert Heqv1.
         repeat destr; inversion 1. eauto.
       * intros; apply val_inject_nextinstr.
         intros; apply val_inject_set; auto.
         intros; apply val_inject_set; auto.
         assert (v0 = parent_sp (Mem.stack m1)).
         revert ISDEF. rewrite Heqs.  simpl. unfold is_ptr. destr. 
         simpl.
         revert ISDEF. simpl. unfold is_ptr. destr. inversion 1; subst. inv ISDEF.
         inv IPS_REC.
         -- simpl in Heqv1. inv Heqv1.
         -- simpl in Heqv1. inv Heqv1.
         -- simpl in Heqv1. unfold current_frame_sp in Heqv1; simpl in Heqv1.
            rewrite BLOCKS0 in Heqv1. inv Heqv1.
            econstructor. eauto.
            rewrite Ptrofs.add_zero_l.
            rewrite Ptrofs.add_unsigned.
            f_equal. setoid_rewrite Ptrofs.unsigned_repr. simpl.
            unfold size_frame; rewrite SIZE0, SIZE.
            rewrite Z.max_r by (apply frame_size_pos). omega.
            generalize (size_active_stack_below m1).
            generalize (size_active_stack_pos (Mem.stack m1)).
            rewrite Heqs. simpl. unfold size_frame. rewrite SIZE, SIZE0.
            generalize Mem.stack_limit_range. omega.
            rewrite Z.max_r by apply frame_adt_size_pos. omega.
         
       * red. rewrite nextinstr_rsp.
         rewrite ! Pregmap.gso by congruence.
         rewrite Pregmap.gss. simpl. inversion 1; subst.
         repeat rewrite_stack_blocks. rewrite Ptrofs.add_unsigned. rewrite AGSP. rewrite Heqs. simpl.
         inversion 1. subst.
         rewrite Z.max_r by apply frame_adt_size_pos.
         unfold size_frame.
         rewrite Ptrofs.unsigned_repr. 
         rewrite Ptrofs.unsigned_repr by omega.
         omega.
         rewrite Ptrofs.unsigned_repr by omega.
         generalize (size_active_stack_below m1). rewrite Heqs. simpl.
         generalize (size_active_stack_pos r). 
         generalize Mem.stack_limit_range.
         unfold size_frame. omega.
       * red. rewrite nextinstr_rsp.
         rewrite ! Pregmap.gso by congruence.
         rewrite Pregmap.gss. simpl. inversion 1. subst. clear H0.
         rewrite Ptrofs.add_unsigned.
         rewrite Ptrofs.unsigned_repr_eq. rewrite AGSP.
         rewrite Z.max_r by apply frame_adt_size_pos.
         rewrite Ptrofs.unsigned_repr by omega.

         apply mod_divides. vm_compute. congruence. rewrite Ptrofs.modulus_power.
         exists (two_p (Ptrofs.zwordsize - 3)). change 8 with (two_p 3). rewrite <- two_p_is_exp. f_equal. vm_compute. congruence. omega.
         apply Z.divide_add_r.
         apply Z.divide_sub_r.
         apply Mem.stack_limit_aligned.
         apply size_active_stack_divides.
         apply align_divides. omega.
       * rewrite nextinstr_rsp.
         rewrite ! Pregmap.gso by congruence.
         rewrite Pregmap.gss.
         f_equal. unfold newostack.
         simpl. rewrite Z.max_r. rewrite Ptrofs.add_unsigned.
         rewrite AGSP.
         rewrite Ptrofs.unsigned_repr by omega.
         reflexivity.
         apply frame_adt_size_pos.
       * red. intros b' delta0 o k p JB0.
         repeat rewrite_perms. destr. intro PERMS.
         generalize (NIB b' delta0 o k p JB0 PERMS).
         intros (LE & INS).
         destruct (peq b b').
         -- subst.
            rewrite perm_stack_eq in PERMS; eauto.
            2: rewrite Heqs; econstructor; eauto.
            2: rewrite Heqs. 2: left. 2: red; simpl. 2: red; rewrite BLOCKS; left; reflexivity.
            rewrite <- SIZE in PERMS.
            apply zle_zlt in PERMS. rewrite <- andb_assoc in Heqb0. rewrite PERMS in Heqb0. inv Heqb0.
         -- repeat rewrite_stack_blocks. rewrite Heqs. simpl. 
            rewrite Heqs in INS.
            rewrite in_stack_cons in INS. destruct INS.
            red in H0. simpl in H0.
            unfold get_frame_blocks in H0. rewrite BLOCKS in H0. simpl in H0. destruct H0;[|easy]. subst.
            intuition.
            rewrite in_stack_cons. split; auto.
            rewrite Ptrofs.unsigned_repr by omega.
            unfold newostack.
            rewrite SIZE.
            destruct (zle (Ptrofs.unsigned (Ptrofs.repr (Mem.stack_limit - size_active_stack s - align ((frame_size fi)) 8)) + align ((frame_size fi)) 8) (o + delta0)); auto.
            exfalso.
            apply Z.gt_lt in g.

            rewrite AGSP in LE, g.
            
            assert (max_perm: forall m b o k p, Mem.perm m b o k p -> Mem.perm m b o Max Nonempty).
            {
              intros.
              eapply Mem.perm_implies.
              eapply Mem.perm_max. eauto. constructor.
            }
            generalize (Mem.free_range_perm _ _ _ _ _ FREE). intro FP.
            assert (LT: 0 < frame_size fi).
            {
              destruct (zlt 0 (frame_size fi)); auto.
              assert (frame_size fi = 0). generalize (frame_size_pos fi); omega.
              rewrite H2 in g.
              change (align 0 8) with 0 in g. omega.
            }
            revert LE g. rewrite Heqs.

            simpl. inv H1.
            unfold size_frame. rewrite SIZE. rewrite Z.sub_add_distr. intros.
            set (delta := Mem.stack_limit - size_active_stack r - align ((frame_size fi)) 8) in *.
            destruct (zlt (o + delta0) (delta + frame_size fi)).
            ++
              assert (DISJ: forall ofs , Mem.perm m1 b ofs Cur Freeable -> bstack <> bstack \/ o + delta0 <> ofs + delta).
              intros; eapply Mem.mi_no_overlap. apply MINJ. apply not_eq_sym. apply n. auto. auto. eapply max_perm; eauto.
              eapply max_perm; eauto.
              assert (exists o2, 0 <= o2 < frame_size fi /\ o + delta0 = o2 + delta) as EX.
              {
                exists (o + delta0 - delta). omega.
              }
              destruct EX as (o2 & RNG & EQ').
              edestruct DISJ; eauto.
            ++ assert (delta + frame_size fi <= o + delta0 < delta + align (frame_size fi) 8).
               omega.
               assert (exists o2, frame_size fi <= o2 < align (frame_size fi) 8 /\ o + delta0 = o2 + delta) as EX.
               {
                 exists (o + delta0 - delta).
                 omega.
               }
               destruct EX as (o2 & RNG & EQ').
               eapply IP. 4: apply PERMS.  3: eauto. 2: apply JB.
               rewrite Heqs. left. red. simpl. red; rewrite BLOCKS. left; reflexivity. omega.
            ++ intuition congruence.
       * repeat rewrite_stack_blocks. rewrite Heqs. simpl. inversion 1. subst. constructor.
         eapply perm_stack_inv. eauto.
         intros. repeat rewrite_perms. destr.
         repeat rewrite andb_true_iff in Heqb1. destruct Heqb1 as ((A & B) & C).
         destruct (peq b b0); simpl in *; try congruence. subst.
         exploit Mem.stack_norepet. rewrite Heqs. intro ND; inv ND.
         eapply H5 in H0; eauto.
       * red. intros b0 fi0 delta' INSTK JB0 b2 o delta2 k p JB2 PERMS.
         revert INSTK. repeat rewrite_stack_blocks. rewrite Heqs. inversion 1; subst. simpl.
         intros [[]|INSTK].
         eapply IP with (k:= k) (p:=p); eauto. rewrite Heqs. simpl. right; eauto. 
         revert PERMS. repeat rewrite_perms. destr.
       * rewnb. xomega.
       * repeat rewrite_stack_blocks. rewrite Heqs. simpl. auto.
         inversion 1; subst.
         simpl in SPinstack. unfold current_frame_sp in SPinstack. simpl in SPinstack.
         destruct SPinstack; auto.
         simpl.  right. red in H0. simpl in H0. red in H0. rewrite BLOCKS in H0.
         destruct H0 as [IFR|[]]. inv IFR.
         red in c.
         revert c. rewrite EQ2.
         unfold Asm.init_sp.
         revert init_sp_ptr. unfold init_sp. intro A; rewrite A.
         rewrite in_stack_cons. intros [[]|INS]. 
         exploit Mem.stack_norepet. rewrite Heqs. intro ND; exfalso; inv ND.
         apply (H3 binit_sp).
         red; simpl. eapply in_frame'_in_frame; eauto. red; rewrite BLOCKS; left; eauto.
         auto.

     + (* load parent pointer *)
       unfold Asm.exec_instr in EI; simpl in EI.
       unfold check_top_frame in EI.
       destruct (Mem.stack m1) eqn:S1; try congruence.
       repeat destr_in EI.
       repeat destr_in Heqb.
       apply andb_true_iff in H0; destruct H0 as (A & B).
       apply ZEQ in B. subst.
       destruct Forall_dec; simpl in A; try congruence. clear A.
       assert (RNGframe: 0 <= align (frame_adt_size f0) 8 < Ptrofs.max_unsigned).
       {
         generalize (size_active_stack_below m1').
         generalize (size_active_stack_pos (Mem.stack m1')). rewrite S1.
         generalize (Mem.stack_limit_range).
         generalize (frame_adt_size_pos f0) (align_le (frame_adt_size f0) 8) (size_stack_pos s).
         generalize (size_active_stack_pos s).
         simpl. unfold size_frame.
         split. omega. omega.
       }
       exists j, ostack; eexists; eexists; split. eauto.
       split; auto.
       inversion MS; subst; econstructor; eauto.
       * rewrite nextinstr_rsp.
         destruct (preg_eq RSP rd).
         rewrite e. rewrite Pregmap.gss. congruence.
         rewrite Pregmap.gso. eauto. auto.
       * intros; apply val_inject_nextinstr.
         intros; apply val_inject_set; auto. rewrite S1 in *.
         simpl in Heqo.
         unfold is_ptr in Heqo; destr_in Heqo. inv Heqo.
         inv IS. 
         rewrite <- Heqv0. unfold current_sp. destr. inv Heqv0.
         inv IPS_REC. inv Heqv0. simpl in *.
         repeat destr_in Heqv0. inv BLOCKS0.
         rewrite RSPEQ. simpl.
         unfold current_frame_sp. simpl. rewrite H2.
         econstructor; eauto. rewrite Ptrofs.add_zero_l.
         rewrite Ptrofs.add_unsigned. 
         rewrite AGSP. rewrite S1.
         simpl. simpl. unfold size_frame.
         rewrite <- SIZE0.
         repeat rewrite Z.max_r by (apply frame_adt_size_pos). f_equal.
         rewrite Ptrofs.unsigned_repr.
         omega. omega.
         auto.
       * red. rewrite nextinstr_rsp.
         rewrite Pregmap.gso; eauto.
       * red. rewrite nextinstr_rsp.
         rewrite Pregmap.gso; eauto.
       * rewrite nextinstr_rsp.
         rewrite Pregmap.gso; eauto.
  Qed.

  Definition asm_prog_no_rsp (ge: Genv.t Asm.fundef unit):=
    forall b f,
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      asm_code_no_rsp (fn_code f).

  Hypothesis prog_no_rsp: asm_prog_no_rsp ge.

  Context `{ecprops: !ExternalCallsProps mem}.

  Lemma inj_incr_sep_same:
    forall j j' m1 m2 b1 b2 delta,
      inject_incr j j' ->
      inject_separated j j' m1 m2 ->
      j' b1 = Some (b2, delta) ->
      Mem.valid_block m2 b2 ->
      j b1 = Some (b2, delta).
  Proof.
    intros.
    destruct (j b1) eqn:JB.
    destruct p. eapply H in JB; eauto.
    congruence.
    exploit H0; eauto. intuition congruence.
  Qed.

  Lemma set_res_no_rsp:
    forall res vres rs,
      no_rsp_builtin_preg res ->
      set_res res vres rs RSP = rs RSP.
  Proof.
    induction res; simpl.
    - intros. eapply Pregmap.gso. auto.
    - auto.
    - intros vres rs (NR1 & NR2).
      rewrite IHres2; auto.
  Qed.

  Lemma val_inject_set_res:
    forall r rs1 rs2 v1 v2 j,
      Val.inject j v1 v2 ->
      (forall r0, Val.inject j (rs1 r0) (rs2 r0)) ->
      forall r0, Val.inject j (set_res r v1 rs1 r0) (set_res r v2 rs2 r0).
  Proof.
    induction r; simpl; intros; auto.
    apply val_inject_set; auto.
    eapply IHr2; eauto.
    apply Val.loword_inject. auto.
    intros; eapply IHr1; eauto.
    apply Val.hiword_inject. auto.
  Qed.

  Definition init_data_diff (id: init_data) (i: ident) :=
    match id with
      Init_addrof ii _ => ii <> i
    | _ => True
    end.

  Lemma store_init_data_eq:
    forall F V m (ge: _ F V) id gv b o i,
      init_data_diff i id ->
      Genv.store_init_data (Genv.add_global ge (id,gv)) m b o i =
      Genv.store_init_data ge m b o i.
  Proof.
    destruct i; simpl; intros; auto.
    unfold Genv.find_symbol; simpl. 
    rewrite Maps.PTree.gso; auto.
  Qed.

  Lemma store_init_data_list_eq:
    forall F V id i, 
      Forall (fun x => init_data_diff x id) i ->
      forall m (ge: _ F V) gv b o,
        Genv.store_init_data_list (Genv.add_global ge (id,gv)) m b o i =
        Genv.store_init_data_list ge m b o i.
  Proof.
    induction 1; simpl; intros; auto.
    rewrite store_init_data_eq; auto.
    destr. 
  Qed.

  Lemma alloc_global_eq:
    forall F V (l: (ident * option (globdef F V))) m (ge: _ F V) id gv,
      (forall v, snd l = Some (Gvar v) -> Forall (fun x => init_data_diff x id) (gvar_init v)) ->
      Genv.alloc_global (Genv.add_global ge (id,gv)) m l =
      Genv.alloc_global ge m l .
  Proof.
    destruct l; simpl; intros.
    repeat (destr; [idtac]).
    rewrite store_init_data_list_eq. auto.
    apply H; auto.
  Qed.

  Lemma alloc_globals_eq:
    forall F V (l: list (ident * option (globdef F V))) m (ge: _ F V) id gv,
      (forall x v, In x l -> snd x = Some (Gvar v) -> Forall (fun x => init_data_diff x id) (gvar_init v)) ->
      Genv.alloc_globals (Genv.add_global ge (id,gv)) m l =
      Genv.alloc_globals ge m l .
  Proof.
    induction l; simpl; intros; eauto.
    rewrite alloc_global_eq. destr.
    apply IHl. intros; eauto.
    eauto.
  Qed.

  Lemma find_symbol_add_globals_other:
    forall F V l (ge: _ F V) s,
      ~ In s (map fst l) ->
      Genv.find_symbol (Genv.add_globals ge l) s =
      Genv.find_symbol ge s.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite IHl.
    unfold Genv.find_symbol; simpl.
    apply Maps.PTree.gso. intuition. intuition.
  Qed.


  Lemma find_symbol_add_global_other:
    forall F V l (ge: _ F V) s,
      s <> fst l ->
      Genv.find_symbol (Genv.add_global ge l) s =
      Genv.find_symbol ge s.
  Proof.
    destruct l; simpl; intros; eauto.
    unfold Genv.find_symbol; simpl.
    apply Maps.PTree.gso. intuition. 
  Qed.

  Lemma find_symbol_none_add_global:
    forall F V (ge: Genv.t F V) a i,
      Genv.find_symbol (Genv.add_global ge a) i = None ->
      i <> fst a /\ Genv.find_symbol ge i = None.
  Proof.
    unfold Genv.find_symbol; simpl.
    intros F V ge0 a i.
    rewrite Maps.PTree.gsspec.
    destr.
  Qed.

  Lemma find_symbol_none_add_globals:
    forall F V a (ge: Genv.t F V) i,
      Genv.find_symbol (Genv.add_globals ge a) i = None ->
      ~ In i (map fst a) /\ Genv.find_symbol ge i = None.
  Proof.
    induction a; simpl; intros; eauto.
    apply IHa in H.
    destruct H as (H1 & H).
    apply find_symbol_none_add_global in H; auto.
    intuition.
  Qed.

  Lemma find_symbol_none_not_in_defs:
    forall F V (p: program F V) i,
      Genv.find_symbol (Genv.globalenv p) i = None ->
      ~ In i (map fst (prog_defs p)).
  Proof.
    unfold Genv.globalenv.
    intros F V p.
    generalize (Genv.empty_genv F V (prog_public p)).
    generalize (prog_defs p).
    induction l; simpl; intros; eauto.
    apply find_symbol_none_add_globals in H.
    destruct H as (A & B).
    apply find_symbol_none_add_global in B.
    destruct B as (B & C).
    intuition.    
  Qed.

  Lemma extcall_arg_inject:
    forall j g rs1 m1 arg1 loc rs2 m2,
      extcall_arg rs1 m1 loc arg1 ->
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Mem.inject j g m1 m2 ->
      exists arg2,
        extcall_arg rs2 m2 loc arg2 /\
        Val.inject j arg1 arg2.
  Proof.
    destruct 1; simpl; intros.
    eexists; split; try econstructor; eauto.
    exploit Mem.loadv_inject; eauto.
    apply Val.offset_ptr_inject; eauto.
    intros (v2 & LOAD & INJ).
    eexists; split; try econstructor; eauto.
  Qed.

  Lemma extcall_arg_pair_inject:
    forall j g rs1 m1 arg1 ty rs2 m2,
      extcall_arg_pair rs1 m1 ty arg1 ->
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Mem.inject j g m1 m2 ->
      exists arg2,
        extcall_arg_pair rs2 m2 ty arg2 /\
        Val.inject j arg1 arg2.
  Proof.
    destruct 1; simpl; intros.
    eapply extcall_arg_inject in H; eauto.
    destruct H as (arg2 & EA & INJ);
      eexists; split; try econstructor; eauto.
    eapply extcall_arg_inject in H; eauto.
    destruct H as (arg2 & EA & INJ).
    eapply extcall_arg_inject in H0; eauto.
    destruct H0 as (arg3 & EA1 & INJ1).
    eexists; split; try econstructor; eauto.
    apply Val.longofwords_inject; eauto.
  Qed.

  Lemma extcall_arguments_inject:
    forall j g rs1 m1 args1 sg rs2 m2,
      extcall_arguments rs1 m1 sg args1 ->
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Mem.inject j g m1 m2 ->
      exists args2,
        extcall_arguments rs2 m2 sg args2 /\
        Val.inject_list j args1 args2.
  Proof.
    unfold extcall_arguments.
    intros j g rs1 m1 args1 sg rs2 m2.
    revert args1. generalize (loc_arguments sg).
    induction 1; simpl; intros; eauto.
    exists nil; split; try econstructor.
    eapply extcall_arg_pair_inject in H; eauto.
    decompose [ex and] H.
    edestruct IHlist_forall2 as (a2 & EA & INJ); eauto.
    eexists; split; econstructor; eauto.
  Qed.

  Lemma set_pair_no_rsp:
    forall p res rs,
      no_rsp_pair p ->
      set_pair p res rs RSP = rs RSP.
  Proof.
    destruct p; simpl; intros; rewrite ! Pregmap.gso; intuition. 
  Qed.

  Lemma val_inject_set_pair:
    forall j p res1 res2 rs1 rs2,
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Val.inject j res1 res2 ->
      forall r,
        Val.inject j (set_pair p res1 rs1 r) (set_pair p res2 rs2 r).
  Proof.
    destruct p; simpl; intros; eauto.
    apply val_inject_set; auto.
    repeat (intros; apply val_inject_set; auto).
    apply Val.hiword_inject; auto.
    apply Val.loword_inject; auto.
  Qed.

  Theorem step_simulation:
    forall S1 t S2,
      Asm.step init_stk ge S1 t S2 ->
      forall j ostack S1' (MS: match_states j ostack S1 S1'),
      exists j' ostack' S2',
        step ge S1' t S2' /\
        match_states j' ostack' S2 S2'.
  Proof.
    destruct 1; intros; inversion MS; subst.
    - (* internal step *)
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      rewrite JB in H7; inv H7. 
      assert (asm_instr_no_rsp i).
      {
        eapply prog_no_rsp. eauto.
        eapply Asmgenproof0.find_instr_in; eauto.
      }
      destruct (exec_instr_inject' _ _ _ _ _ _ _ _ _ _ MS H4 (asmgen_no_change_stack i) H2)
        as ( j' & ostack' & rs2' & m2' & EI' & MS' & INCR).
      do 3 eexists; split.
      eapply exec_step_internal; eauto.
      rewrite Ptrofs.add_zero. eauto.
      eauto.
    - (* builtin step *)
      edestruct (eval_builtin_args_inject) as (vargs' & Hargs & Hargsinj).
      6: eauto.
      eauto. eauto. eauto.
      eauto. 
      eapply GLOBSYMB_INJ.
      edestruct (external_call_mem_inject_gen ef ge ge)
        as (j' & vres' & m2' & EC & RESinj & MemInj & Unch1 & Unch2 & INCR & SEP).
      apply meminj_preserves_globals'_symbols_inject.
      eauto.
      eauto.
      eapply Mem.inject_push_new_stage_left. eauto.
      eauto.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      rewrite JB in H10; inv H10.
      exploit Mem.unrecord_stack_block_inject_left. apply MemInj. eauto.
      omega. 
      red; repeat rewrite_stack_blocks. constructor. easy. 
      intro MemInj'.
      do 3 eexists; split.
      eapply exec_step_builtin.
      eauto.
      eauto. 
      rewrite Ptrofs.add_zero; eauto.
      eauto.
      eauto.
      auto.
      reflexivity.
      econstructor.
      + eauto.
      + repeat rewrite_stack_blocks. simpl; eauto.
      + reflexivity.
      + rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H7.
        destruct H7 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        auto.
      + intros. apply val_inject_nextinstr_nf.
        apply val_inject_set_res; auto.
        apply val_inject_undef_regs; auto.
        intros; eapply val_inject_incr; eauto.
      + red; rewnb. auto.
      + red. rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other.
        repeat rewrite_stack_blocks. simpl; auto.
        intros r INR EQ; subst.
        rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      (* + red. erewrite <- external_call_stack_blocks. 2: eauto. *)
      (*   rewrite nextinstr_nf_rsp. *)
      (*   rewrite set_res_no_rsp; auto. *)
      (*   rewrite Asmgenproof0.undef_regs_other. eauto. *)
      (*   intros; intro; subst. *)
      (*   rewrite in_map_iff in H6. *)
      (*   destruct H6 as (x & EQ & IN). *)
      (*   apply preg_of_not_rsp in EQ. congruence. *)
      (* + erewrite <- external_call_stack_blocks; eauto. *)
      + red. 
        rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros r' INR; intro; subst.
        rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + red. intros ofs0 k p PERM.
        revert PERM; rewrite_perms. eauto.
        destruct NS as (fr & fi & r & STK' & BLK & ZERO & PUB).
        rewrite STK'.
        rewrite in_stack_cons; left. 
        rewrite in_frames_cons. eexists; split; eauto.
        red; unfold get_frame_blocks; rewrite <- BLK. simpl. auto.
      + red.
        intros.
        eapply ec_perm_unchanged. eapply external_call_spec. eauto.
        eauto.
        intros. eapply PBS in H8. destruct H8.  intro A; inv A; inv H10. 
        eauto.
      + red.
        erewrite <- external_call_stack_blocks. 2: eauto.
        eauto.
      + rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros ? INR; intro; subst.
        rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + red. intros b delta o k p JB1 PERM.
        repeat rewrite_stack_blocks. simpl.
        destruct (j b) eqn:A. destruct p0.
        exploit INCR. eauto. eauto. intro JB2. rewrite JB1 in JB2; inv JB2.
        eapply NIB; eauto.
        eapply Mem.perm_max in PERM. eapply Mem.push_new_stage_perm.
        eapply external_call_max_perm. eauto. red; rewnb.
        eapply Mem.valid_block_inject_1; eauto.
        eapply Mem.unrecord_stack_block_perm. eauto. eauto.
        exploit SEP. eauto. eauto.
        unfold Mem.valid_block.  rewnb. intuition congruence. 
      + eapply inject_stack_incr. apply INCR.
        repeat rewrite_stack_blocks. simpl.
        eapply perm_stack_inv. eauto. intros.
        repeat rewrite_perms; auto. rewrite_stack_blocks. rewrite in_stack_cons; auto.
      + red.
        repeat rewrite_stack_blocks. simpl.
        intros b fi delta INS J'B b' o delta' k p J'B' PERM.
        exploit inj_incr_sep_same. eauto. eauto. apply J'B. auto.
        exploit inj_incr_sep_same. eauto. eauto. apply J'B'. auto.
        intros NJB' NJB.
        eapply IP; eauto.
        eapply Mem.perm_max in PERM. eapply Mem.push_new_stage_perm.
        eapply external_call_max_perm. eauto. red; rewnb.
        eapply Mem.valid_block_inject_1; eauto.
        eapply Mem.unrecord_stack_block_perm. eauto. eauto.
      + intros.
        eapply INCR; eauto.
      + intros.
        eapply INCR; eauto.
      + destruct GLOBSYMB_INJ.
        split. intros.
        eapply INCR; eauto.
        intros.
        destruct (j b1) eqn:JB1.
        destruct p.
        exploit INCR; eauto. rewrite H10; intro X; inv X.
        eauto.
        exploit SEP; eauto. unfold Mem.valid_block; rewnb. intros (NV1 & NV2).
        simpl; unfold Genv.block_is_volatile.
        rewrite ! find_var_info_none_ge.
        auto.
        unfold Mem.valid_block in NV1. xomega.
        unfold Mem.valid_block in NV2. xomega.
      + etransitivity. apply GlobLe. fold Ple. rewnb. xomega.
      + etransitivity. apply GlobLeT. fold Ple. rewnb. xomega.
      + repeat rewrite_stack_blocks. simpl; eauto.
    - (* external step *)
      edestruct (extcall_arguments_inject) as (vargs' & Hargs & Hargsinj).
      eauto.
      eauto. eauto. 
      edestruct (external_call_mem_inject_gen ef ge ge)
        as (j' & vres' & m2' & EC & RESinj & MemInj & Unch1 & Unch2 & INCR & SEP).
      apply meminj_preserves_globals'_symbols_inject. eauto.
      eauto.
      eauto.
      eauto. 
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      rewrite JB in H9; inv H9.
      exploit (Mem.unrecord_stack_block_inject_left _ _ _ _ _ _ MemInj H3).
      inv TIN. rewrite STK in H6.
      destruct lprog; simpl in *. 2: omega.
      revert init_sp_ptr. unfold init_sp. rewrite <- H6. simpl. unfold current_frame_sp; rewrite H7. inversion 1.
      red; repeat rewrite_stack_blocks. inv TIN. constructor. unfold in_frames; rewrite H7. easy.
      intro MemInj'.
      do 3 eexists; split.
      eapply exec_step_external.
      eauto.
      eauto.
      eauto.
      generalize (RINJ RSP). destruct (rs RSP); simpl in *; inversion 1; subst; try congruence.
      generalize (RINJ RA). destruct (rs RA); simpl in *; inversion 1; subst; try congruence.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      generalize (RINJ RSP). destruct (rs RSP); simpl in *; inversion 1; subst; try congruence.
      generalize (RINJ RA). destruct (rs RA); simpl in *; inversion 1; subst; try congruence.
      eauto.
      reflexivity.

      econstructor; eauto.
      + repeat rewrite_stack_blocks.
        instantiate (1 := tl lprog).
        destruct lprog. inv TIN. exfalso.
        revert init_sp_ptr; unfold init_sp; simpl in STK; rewrite <- STK. rewrite <- H6.
        simpl; unfold current_frame_sp; simpl. rewrite H7; 
        inversion 1.
        revert EQ; rewrite_stack_blocks. intro A; rewrite A. simpl.
        rewrite STK in A. simpl in A ; inv A. auto.
      + destruct lprog; simpl; try reflexivity.
        exfalso.
        revert init_sp_ptr; unfold init_sp; simpl in STK; rewrite <- STK. rewrite STK.
        inv TIN. rewrite <- H6.
        simpl; unfold current_frame_sp; simpl. rewrite H7; 
        inversion 1.        
      + repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros ? INR; intro; subst. rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H6; simpl in *; intuition congruence.
        auto.
      + intros; apply val_inject_set.
        intros; apply val_inject_set.
        intros; apply val_inject_set_pair; auto.
        apply val_inject_undef_regs; auto.
        apply val_inject_undef_regs; auto.
        intros; eapply val_inject_incr; eauto.
        intros; eapply val_inject_incr; eauto.
        auto.
      + red; rewnb; eauto.
      + red. repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        repeat rewrite_stack_blocks. inv TIN. simpl.
        intros ostack RRSP. apply AGSP in RRSP. rewrite <- H6 in RRSP. simpl in RRSP.
        rewrite H7 in RRSP; simpl in RRSP. omega. 
        intros ? INR; intro; subst. rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H6; simpl in *; intuition congruence.
        auto.
      + red.
        repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros ? INR; intro; subst. rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H6; simpl in *; intuition congruence.
        auto.
      + red.
        intros.
        eapply Mem.perm_max in H6.
        eapply external_call_max_perm in H6.
        2: eauto.
        eauto. eauto.
      + red.
        intros.
        eapply ec_perm_unchanged. eapply external_call_spec. eauto.
        eauto.
        intros. eapply PBS in H7. destruct H7.  intro A; inv A; inv H9.
        eauto.
      + red.
        erewrite <- external_call_stack_blocks. 2: eauto.
        eauto.
      + repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros ? INR; intro; subst. rewrite in_map_iff in INR.
        destruct INR as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H6; simpl in *; intuition congruence.
        auto. 
      + red. intros b delta o k p JB1 PERM.
        repeat rewrite_stack_blocks. inv TIN. simpl.
        destruct (j b) eqn:A. destruct p0.
        * exploit INCR. eauto. eauto. intro JB2. rewrite JB1 in JB2; inv JB2.
          exploit NIB; eauto.
          eapply Mem.perm_max in PERM.
          eapply external_call_max_perm. eauto.
          eapply Mem.valid_block_inject_1; eauto.
          eapply Mem.unrecord_stack_block_perm; eauto. rewrite <- H6. rewrite in_stack_cons.
          unfold in_frames; rewrite H7. intuition.
        * exploit SEP. eauto. eauto. intuition congruence.
      + eapply inject_stack_incr; eauto.
        repeat rewrite_stack_blocks. inv IS. constructor. simpl.
        eapply perm_stack_inv. eauto.
        intros; repeat rewrite_perms; auto.
        rewrite <- H7. rewrite in_stack_cons; auto.
        simpl.
        eapply perm_stack_inv. eauto.
        intros; repeat rewrite_perms; auto.
        rewrite <- H7. rewrite in_stack_cons; auto.
      + red.
        repeat rewrite_stack_blocks.
        intros b fi delta INS J'B b' o delta' k p J'B' PERM.
        exploit inj_incr_sep_same. eauto. eauto. apply J'B. auto.
        exploit inj_incr_sep_same. eauto. eauto. apply J'B'. auto.
        intros.
        eapply IP; eauto.
        revert INS. inv TIN. simpl. auto.
        eapply Mem.perm_max in PERM.
        eapply external_call_max_perm. eauto.
        eapply Mem.valid_block_inject_1; eauto.
        eapply Mem.unrecord_stack_block_perm; eauto.
      + destruct GLOBSYMB_INJ.
        split. intros.
        eapply INCR; eauto.
        intros.
        destruct (j b1) eqn:JB1.
        destruct p.
        exploit INCR; eauto. rewrite H9; intro X; inv X.
        eauto.
        exploit SEP; eauto. intros (NV1 & NV2).
        simpl; unfold Genv.block_is_volatile.
        rewrite ! find_var_info_none_ge.
        auto.
        unfold Mem.valid_block in NV1. xomega.
        unfold Mem.valid_block in NV2.
        xomega. 
      + etransitivity. apply GlobLe. fold Ple; rewnb; xomega.
      + etransitivity. apply GlobLeT. fold Ple; rewnb; xomega.
      + repeat rewrite_stack_blocks. revert SPinstack. inv TIN. simpl.
        unfold in_frames'. rewrite H7. tauto.
  Qed.

End PRESERVATION.


  Lemma repr_stack_limit:
    Ptrofs.unsigned (Ptrofs.repr (Mem.stack_limit)) = Mem.stack_limit.
  Proof.
    apply Ptrofs.unsigned_repr.
    generalize (Mem.stack_limit_range); omega.
  Qed.
  
  Lemma match_initial_states s:
    Asm.initial_state prog s ->
    exists s' j ostack, match_states ((Some (make_singleton_frame_adt (Genv.genv_next ge) 0 0),nil) :: nil) (Genv.genv_next ge) j ostack s s' /\
                   RawAsm.initial_state prog (Pregmap.init Vundef) s'.
  Proof.
    inversion 1. subst.
    rename H into INIT.
    rename H0 into INITMEM.
    unfold Mem.record_init_sp in H1; destr_in H1.
    rename Heqp into ALLOC.
    rename H1 into RSB.
    exploit Genv.initmem_inject; eauto. intro FLATINJ.
    apply Mem.push_new_stage_inject_flat in FLATINJ.
    assert  (ALLOCINJ:
               exists (f' : meminj) (m2' : mem) (b2 : block),
                 Mem.alloc (Mem.push_new_stage m0) 0 Mem.stack_limit = (m2', b2) /\
                 Mem.inject f' (flat_frameinj (length (Mem.stack (Mem.push_new_stage m0)))) m m2' /\
                 inject_incr (Mem.flat_inj (Mem.nextblock m0)) f' /\
                 f' b = Some (b2, Mem.stack_limit) /\ (forall b0 : block, b0 <> b -> f' b0 = Mem.flat_inj (Mem.nextblock m2) b0)).
    {
      destruct (Mem.alloc (Mem.push_new_stage m0) 0 Mem.stack_limit) as (m2' & b2) eqn: ALLOC'.
      eapply Mem.alloc_right_inject in FLATINJ; eauto.
      exploit (Mem.alloc_left_mapped_inject _ _ _ _ _ _ _ _ b2 Mem.stack_limit FLATINJ ALLOC).
      - exploit Mem.alloc_result; eauto. intro; subst. red; rewnb. xomega.
      - apply Mem.stack_limit_range.
      - intros ofs k p. rewrite_perms. rewrite pred_dec_true; auto.
        generalize (Mem.stack_limit_range). intros; omega.
      - intros ofs k p. omega.
      - red. intro. generalize (size_chunk_pos chunk); omega.
      - unfold Mem.flat_inj. intros b0 delta' ofs k p. destr. inversion 1; subst.
        exploit Mem.alloc_result; eauto. intro; subst. xomega.
      - repeat rewrite_stack_blocks. simpl. intuition easy.
      - intros (f' & INJ & INCR & FB & FOTHER).
        do 3 eexists. split; eauto. split; eauto. split; eauto. split; eauto.
        intros; rewrite FOTHER; auto.
        unfold Mem.flat_inj. exploit Mem.alloc_result; eauto. intro; subst.
        revert FB FOTHER. rewnb. repeat destr. intros; xomega.
        apply Plt_succ_inv in p. intuition. subst. contradict H. exploit Mem.alloc_result. apply ALLOC. intro; subst.
        rewnb. auto.
    }
    destruct ALLOCINJ as (f' & m2' & b2 & ALLOC' & ALLOCINJ & INCR & F'B & F'O).
    assert (b = b2).
    {
      exploit Mem.alloc_result. apply ALLOC.
      exploit Mem.alloc_result. apply ALLOC'. intros; subst. rewnb. congruence.
    }
    subst.
    assert (b2 = bstack).
    {
      unfold bstack.
      exploit Mem.alloc_result; eauto. intro; subst.
      rewnb. fold ge; reflexivity.
    } subst.
    edestruct (Mem.range_perm_drop_2) with (p := Writable) as (m3' & DROP).
    red; intros; eapply Mem.perm_alloc_2; eauto.
    assert (DROPINJ: Mem.inject f' (flat_frameinj (length (Mem.stack (Mem.push_new_stage m0)))) m m3').
    {
      eapply Mem.drop_outside_inject. apply ALLOCINJ. eauto.
      intros b' delta ofs k p FB1 PERM RNG.
      revert PERM; repeat rewrite_perms. destr. omega. intros.
      revert FB1; unfold Mem.flat_inj. rewrite F'O. unfold Mem.flat_inj. destr. auto.
    }
    assert (RSB': exists m4',
               Mem.record_stack_blocks m3' (make_singleton_frame_adt' bstack frame_info_mono 0) = Some m4' /\
               Mem.inject f'
                          (flat_frameinj (length (Mem.stack (Mem.push_new_stage m0)))) m2 m4').
    {
      edestruct Mem.record_stack_blocks_inject_parallel as (m4' & RSB' & RSBinj).
      apply DROPINJ. 7: eauto.
      instantiate (1 := make_singleton_frame_adt' bstack frame_info_mono 0).
      - red; intros.
        constructor; auto.
        simpl. rewrite F'B. inversion 1.
        eexists; split; eauto.
        split; simpl; intros; rewrite Z.max_r in H0; omega.
      - repeat rewrite_stack_blocks. easy.
      - red. intros b [A|[]].
        subst. unfold bstack; simpl.
        red. rewnb. fold ge. xomega.
      - intros b fi o k p [A|[]]; inv A.
        repeat rewrite_perms. destr.
      - unfold Mem.flat_inj. intros b1 b0 delta FB.
        destruct (peq b1 bstack); subst. rewrite F'B in FB; inv FB. tauto.
        rewrite F'O in FB; auto. unfold Mem.flat_inj in FB. destr_in FB. inv FB.
        tauto.
      - reflexivity.
      - repeat rewrite_stack_blocks. constructor. reflexivity.
      - repeat rewrite_stack_blocks. simpl. omega.
      - eexists; split; eauto.
    }
    destruct RSB' as (m4' & RSB' & RSBINJ).
    eexists _, f', _; split.
    2: now (econstructor; eauto; econstructor; eauto).
    econstructor; eauto.
    - apply Mem.inject_push_new_stage_left.
      revert RSBINJ.
      instantiate (1 := (None,nil) :: nil).
      repeat rewrite_stack_blocks. simpl. auto.
    - repeat rewrite_stack_blocks. simpl. unfold bstack. inversion 1. intros;reflexivity.
    - unfold rs0. rewrite Pregmap.gss. eauto.
    - intros. unfold rs0.
      repeat (intros; apply val_inject_set; auto).
      + unfold ge0. unfold Genv.symbol_address. destr; auto.
        eapply Genv.genv_symb_range in Heqo.
        econstructor; eauto.
        rewrite F'O.
        unfold Mem.flat_inj. rewrite pred_dec_true. eauto. rewnb. xomega.
        exploit Mem.alloc_result; eauto. intro; subst. rewrite H1. rewnb. apply Plt_ne. auto.
        reflexivity.
      + unfold Vnullptr; constructor.
      + econstructor. rewnb. eauto. rewrite Ptrofs.add_zero_l. auto.
    - red; unfold bstack; rewnb. fold ge. xomega.
    - red. rewrite Pregmap.gss. inversion 1; subst.
      repeat rewrite_stack_blocks. simpl. rewrite repr_stack_limit. unfold size_frame.
      simpl. inversion 1. subst. simpl. omega.
    - red. rewrite Pregmap.gss. inversion 1; subst.
      rewrite repr_stack_limit. apply Mem.stack_limit_aligned.
    - red. intros o k p.
      repeat rewrite_perms. rewrite peq_true. intros (A & B).
      generalize (Mem.stack_limit_range). trim B; auto. trim B ; auto. split; auto. omega.
    - red; intros.
      repeat rewrite_perms. rewrite peq_true. split; auto. intros; constructor.
    - red.
      repeat rewrite_stack_blocks. inversion 1; subst.
      repeat econstructor.
    - rewrite Pregmap.gss. eauto.
    - red.
      intros b delta o k p INJ. repeat rewrite_perms. destr. omega. intro P.
      rewrite F'O in INJ by auto. unfold Mem.flat_inj in INJ.
      revert INJ.
      apply Mem.perm_valid_block in P. red in P; revert P.
      rewnb. destr.
    - repeat rewrite_stack_blocks.
      inversion 1; subst.
      repeat econstructor; eauto.
      simpl. rewrite Z.max_r by omega. change (align 0 8) with 0. rewrite F'B. f_equal. f_equal. omega. simpl. rewrite Z.max_r ; intros;  omega.
    - red. repeat rewrite_stack_blocks. inversion 1; subst. simpl.
      intros. destruct H as [[]|[[A|[]]|[]]]. inv A.
      simpl. rewrite Z.max_r by omega. change (align 0 8) with 0. omega.
    - intros.
      assert (Plt b (Genv.genv_next ge)).
      {
        unfold Genv.find_funct_ptr in H. repeat destr_in H.
        eapply Genv.genv_defs_range in Heqo; eauto.
      }
      rewrite F'O. unfold Mem.flat_inj. rewnb. fold ge. destr. xomega.
      apply Plt_ne; auto.
    - intros.
      assert (Plt b (Genv.genv_next ge)).
      {
        eapply Genv.genv_defs_range in H; eauto.
      }
      rewrite F'O. unfold Mem.flat_inj. rewnb. fold ge. destr. xomega.
      apply Plt_ne; auto.
    - split.
      simpl; intros.
      assert (Plt b (Genv.genv_next ge)).
      {
        eapply Genv.genv_symb_range in H; eauto.
      }
      rewrite F'O. unfold Mem.flat_inj. rewnb. fold ge. destr. xomega.
      apply Plt_ne; auto.
      intros b1 b2 delta FB. destruct (peq b1 bstack); subst.
      rewrite F'B in FB; inv FB; auto.
      rewrite F'O in FB; auto.
      unfold Mem.flat_inj in FB; repeat destr_in FB; auto.
    - rewnb. fold ge. xomega.
    - rewnb. fold ge. xomega.
    - repeat rewrite_stack_blocks. simpl. right; left; left. simpl. reflexivity.
  Qed.

  Lemma transf_final_states:
    forall istk isp j o st1 st2 r,
      match_states istk isp j o st1 st2 -> Asm.final_state st1 r -> final_state st2 r.
  Proof.
    inversion 1; subst.
    inversion 1; subst.
    econstructor.
    generalize (RINJ PC). rewrite H3. unfold Vnullptr. destruct ptr64; inversion 1; auto.
    generalize (RINJ RAX). rewrite H5. unfold Vnullptr. destruct ptr64; inversion 1; auto.
  Qed.
  
  Theorem transf_program_correct:
    asm_prog_no_rsp ge ->
    forward_simulation (Asm.semantics
                          prog
                          ((Some (make_singleton_frame_adt (Genv.genv_next ge) 0 0), nil) :: nil))
                       (RawAsm.semantics prog (Pregmap.init Vundef)).
  Proof.
    intros APNR.
    eapply forward_simulation_step with (fun s1 s2 => exists j o, match_states _  (Genv.genv_next ge) j o s1 s2).
    - simpl. reflexivity. 
    - simpl. intros s1 IS; inversion IS.
      exploit match_initial_states. eauto.
      intros (s' & j & ostack & MS & MIS); eexists; split; eauto. inv MIS. eauto.
    - simpl. intros s1 s2 r (j & o & MS) FS. eapply transf_final_states; eauto.
    - simpl. intros s1 t s1' STEP s2 (j & o & MS). 
      edestruct step_simulation as (isp' & j' & o' & STEP' & MS'); eauto.
      reflexivity.
  Qed.
  
End WITHMEMORYMODEL.
