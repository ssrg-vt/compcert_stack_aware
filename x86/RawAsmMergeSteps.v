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

  Definition make_palloc f : instruction :=
    let sz := frame_size f in 
    (Pallocframe f (Ptrofs.sub (Ptrofs.repr (align sz 8)) (Ptrofs.repr (size_chunk Mptr)))).

  Lemma make_palloc_is_alloc:
    forall f,
      is_alloc (frame_size f) (make_palloc f).
  Proof. constructor. auto. Qed.
  
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
  | step_other:
      forall s1 t s2 r
        (PC: pc_at s1 = Some r)
        (NOFREE: forall f0 i, r = inl (f0,i) -> forall f, ~ is_free f i)
        (NOFREE: forall f0 i, r = inl (f0,i) -> forall f, ~ is_alloc f i)
        (NOCALL: forall f0 i, r = inl (f0,i) -> i <> Pret /\ ~ is_jmp i /\ ~ is_call (rs_state s1) i)
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

  Lemma nextinstr_nf_pc: forall rs sz, nextinstr_nf rs sz PC = Val.offset_ptr (rs PC) sz.
  Proof.
    unfold nextinstr_nf. simpl.
    intros. rewrite Asmgenproof0.nextinstr_pc. f_equal.
  Qed.

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

  Record wf_asm_function (f: function): Prop :=
    {
      wf_asm_call_target_exists:
        forall o symb sg,
          find_instr o (fn_code f) = Some (Pcall_s symb sg) ->
          exists bf f',
            Genv.symbol_address ge symb Ptrofs.zero = Vptr bf Ptrofs.zero /\
            Genv.find_funct_ptr ge bf = Some f';

      wf_asm_jmp_target_exists:
        forall o symb sg,
          find_instr o (fn_code f) = Some (Pjmp_s symb sg) ->
          exists bf f',
            Genv.symbol_address ge symb Ptrofs.zero = Vptr bf Ptrofs.zero /\
            Genv.find_funct_ptr ge bf = Some f';

      wf_asm_alloc_only_at_beginning:
        forall o fi ora,
          find_instr o (fn_code f) = Some (Pallocframe fi ora) ->
          o = 0;
      wf_asm_alloc_at_beginning:
        find_instr 0 (fn_code f) = Some (make_palloc (fn_frame f));

      wf_asm_after_freeframe:
        forall i o sz,
          find_instr (Ptrofs.unsigned o) (fn_code f) = Some i ->
          is_free sz i ->
          sz = frame_size (fn_frame f) /\
          exists i' ,
            find_instr (Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (instr_size i)))) (fn_code f) = Some i' /\
            (i' = Pret \/ is_jmp ge i' );

      wf_asm_ret_jmp_comes_after_freeframe:
        forall i o,
          find_instr (Ptrofs.unsigned o) (fn_code f) = Some i ->
          i = Pret \/ is_jmp ge i ->
          exists o' ifree,
            find_instr (Ptrofs.unsigned o') (fn_code f) = Some ifree /\
            is_free (frame_size (fn_frame f)) ifree /\
            Ptrofs.unsigned (Ptrofs.repr (instr_size (make_palloc (fn_frame f)))) <= Ptrofs.unsigned o' < Ptrofs.unsigned o;
      
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

  Lemma pc_at_not_final:
    forall s i r,
      pc_at ge s = Some i ->
      final_state s r ->
      False.
  Proof.
    intros s i r PCAT FS; inv FS.
    simpl in PCAT. rewrite H in PCAT.
    unfold Vnullptr in PCAT. destruct (ptr64); inv PCAT.
  Qed.

  Inductive intermediate_instruction : instruction -> Prop :=
  | ii_ret: intermediate_instruction Pret
  | ii_alloc i sz: is_alloc sz i -> intermediate_instruction i
  | ii_jmp i: is_jmp ge i -> intermediate_instruction i.


  Axiom instr_size_repr:
    forall i,
      0 <= instr_size i <= Ptrofs.max_unsigned.

  Lemma find_instr_pos_positive:
    forall l o i,
      find_instr o l = Some i -> 0 <= o.
  Proof.
    induction l; simpl; intros; eauto. congruence.
    destr_in H. omega. apply IHl in H.
    generalize (instr_size_positive a). omega.
  Qed.
  
  Lemma find_instr_no_overlap:
    forall l o1 o2 i1 i2,
      find_instr o1 l = Some i1 ->
      find_instr o2 l = Some i2 ->
      o1 <> o2 ->
      o1 + instr_size i1 <= o2 \/ o2 + instr_size i2 <= o1.
  Proof.
    induction l; simpl; intros; eauto. congruence.
    repeat destr_in H; repeat destr_in H0.
    - apply find_instr_pos_positive in H2. omega.
    - apply find_instr_pos_positive in H3. omega.
    - specialize (IHl _ _ _ _ H3 H2). trim IHl. omega. omega.
  Qed.
  
  Lemma group_progress:
    forall rs s1
      (SAFE : safe (RawAsm.semantics prog rs) s1)
      (INV: forall f i, pc_at ge s1 = Some (inl (f, i)) -> ~ intermediate_instruction i),
      (exists r, final_state s1 r) \/ (exists t s2, step (Genv.globalenv prog) s1 t s2 /\
                                         forall f i, pc_at ge s2 = Some (inl (f, i)) -> ~ intermediate_instruction i).
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
             right; exists E0, (State rs' m'). split.
             eapply step_call_internal.  5: apply STEP. 5: apply STEP2. eauto.
             unfold pc_at. rewrite PC2. rewrite H0, H1. eauto. eauto.
             erewrite wf_asm_alloc_at_beginning in H1; eauto. inv H1. apply make_palloc_is_alloc.
             simpl.
             erewrite wf_asm_alloc_at_beginning in H1; eauto. inv H1.
             simpl in H2. repeat destr_in H2. unfold ge in FFP; rewrite FFP in H0. inv H0.
             simpl_regs. rewrite PC2. simpl. unfold ge. rewrite FFP.
             destr. inversion 1; subst. intro A.
             rewrite Ptrofs.add_zero_l in Heqo0.
             inv A.
             eapply wf_asm_ret_jmp_comes_after_freeframe in Heqo0; eauto.
             destruct Heqo0 as (o' & ifree & FI & IFREE & RNG). omega.
             inv H0. eapply wf_asm_alloc_only_at_beginning in Heqo0; eauto.
             rewrite Ptrofs.unsigned_repr in Heqo0. generalize (instr_size_positive (make_palloc (fn_frame f1))). omega.
             apply instr_size_repr.
             eapply wf_asm_ret_jmp_comes_after_freeframe in Heqo0; eauto.
             destruct Heqo0 as (o' & ifree & FI & IFREE & RNG). omega.
          -- simpl in *. rewrite_hyps.
             erewrite wf_asm_alloc_at_beginning in H1; eauto. inv H1. 
          -- simpl in PC2. rewrite_hyps.
             right; eexists t, (State _ m').
             split. eapply step_call_external.  4: apply STEP. 4: apply STEP2. eauto. eauto.
             unfold pc_at. rewrite PC2. rewrite H0. eauto.
             Opaque destroyed_at_call.
             simpl. simpl_regs.
             unfold pc_at in PCs; repeat destr_in PCs.
             assert (rs0 RA = Vptr b (Ptrofs.add i0 (Ptrofs.repr (instr_size i)))).
             {
               inv CALL; simpl in EI; repeat destr_in EI; simpl_regs; rewrite Heqv; simpl; auto.
             }
             rewrite H. rewrite Heqo. destr. inversion 1; subst.
             intro II; inv II.
             eapply wf_asm_ret_jmp_comes_after_freeframe in Heqo1; eauto.
             destruct Heqo1 as (o' & ifree & FO & IFREE & _ & RNG).
             generalize (find_instr_no_overlap _ _ _ _ _ FO Heqo0). intro NOOV.
             trim NOOV.
             intro EQ; rewrite EQ in FO. rewrite Heqo0 in FO. inv FO. inv IFREE; inv CALL.
             rewrite Ptrofs.add_unsigned in RNG. rewrite Ptrofs.unsigned_repr in RNG.
             rewrite Ptrofs.unsigned_repr in RNG. 

      + (* not a call, free ? *)
        destruct (is_free_dec i) as [(sz & ISFREE)|NISFREE].
        * inversion ISFREE; subst. clear NOTCALL.
          exploit step_internal; eauto. intro IB; inv IB. intros (EI & T0). subst.
          assert (PC2: sz = frame_size (fn_frame f) /\ exists i, pc_at ge s2 = Some (inl (f, i)) /\ (i = Pret \/ is_jmp ge i)).
          {
            unfold pc_at in PCs |- *. repeat destr_in PCs.
            destr. simpl in EI. repeat destr_in EI.
            repeat simpl_regs. rewrite Heqv. simpl. rewrite Heqo.
            destruct (wf_asm_after_freeframe _ (wf_asm_prog _ _ Heqo) _ _ _ Heqo0 ISFREE) as (SZ & i0 & FI0 & SPECi0). rewrite FI0. eauto. 
          }
          destruct PC2 as (SZ & i2 & PC2 & SPECi2). subst.
          destruct (SAFE _ (star_one _ _ _ _ _ STEP)) as [(r & FS)|(t & s3 & STEP2)].
          edestruct pc_at_not_final; eauto.
          simpl in EI. repeat destr_in EI.
          assert (t = E0).
          {
            inv STEP2; auto; unfold ge in *; simpl in *; subst; rewrite_hyps.
            rewrite H, H2, H3 in PC2. inv PC2. destruct SPECi2 as [A|A]; inv A.
            rewrite H, H2 in PC2. inv PC2.
          }
          subst.
          destruct SPECi2 as [RET | JMP].
          -- subst. right.
             eexists _, _; eapply step_free_ret. 4: apply STEP. 4: apply STEP2.
             eauto. eauto. eauto.
          -- exploit step_internal; eauto. intro IB; inv JMP; inv IB. intros (EI & T0).
             assert (PC3: exists i3,
                        pc_at ge s3 = Some i3 /\
                        ((exists f' ialloc, i3 = inl (f',ialloc) /\ is_alloc (frame_size (fn_frame f')) ialloc )
                         \/ (exists ef, i3 = inr ef))).
             {
               unfold pc_at in PC2 |- *. repeat destr_in PC2. destr. simpl in *; subst.
               inv JMP.
               - (* jmp_s*)
                 simpl in EI; repeat destr_in EI.
                 unfold ge in *. rewrite_hyps.
                 simpl_regs.
                 destruct (wf_asm_jmp_target_exists _ (wf_asm_prog _ _ Heqo0) _ _ _ Heqo1)
                   as (bf & f' & SA & FFP). 
                 unfold ge in *. rewrite SA.
                 unfold Genv.symbol_address in SA. rewrite H in SA. inv SA. rewrite FFP.
                 destr.
                 erewrite wf_asm_alloc_at_beginning; eauto.
                 eexists; split; eauto. left; do 2 eexists; split; eauto using make_palloc_is_alloc.
                 eexists; split; eauto.
               - simpl in EI.
                 repeat destr_in EI. simpl_regs.
                 simpl_regs_in Heqo2.
                 unfold Genv.find_funct in Heqo2. repeat destr_in Heqo2. rewrite H0.
                 destr.
                 erewrite wf_asm_alloc_at_beginning; eauto.
                 eexists; split; eauto. left; do 2 eexists; split; eauto using make_palloc_is_alloc.
                 eexists; split; eauto.
             }
             destruct PC3 as (i3 & PC3 & SPECi3).
             destruct (SAFE _ (star_two _ _ _ _ _ _ _ STEP STEP2 eq_refl)) as [(ret & FS)|(t & s4 & STEP3)].
             edestruct pc_at_not_final; eauto.
             destruct SPECi3 as [(f' & ialloc & EQ & ALLOC)|(ef&EXT)]; subst.
             ++
               edestruct step_internal. apply STEP3. eauto. intro IB; inv IB; inv ALLOC. subst.
               right; do 2 eexists. eapply step_free_tailcall.
               apply PCs. apply PC2. apply PC3.
               all: eauto.
             ++ right; do 2 eexists. eapply step_free_external.
                apply PCs. apply PC2. apply PC3. all: eauto.
        * (* not call nor free -> regular step *)

          right; do 2 eexists.
          eapply step_other. eauto.
          inversion 1; subst. intros f ISFREE; apply NISFREE. eauto.
          inversion 1; subst; intros; eauto. eauto.
    - right; do 2 eexists; eapply step_other; eauto.
      inversion 1. inversion 1.
    -
      unfold pc_at in PCs. destr_in PCs. inv STEP; simpl in *; unfold ge in *.
      + repeat destr_in PCs.
      + repeat destr_in PCs.
      + repeat destr_in PCs.
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
