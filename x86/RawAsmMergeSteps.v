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

  Inductive is_call: instruction -> Prop :=
  | is_call_s:
      forall symb b sg,
        Genv.find_symbol ge symb = Some b ->
        is_call (Pcall_s symb sg)
  | is_call_r:
      forall (r: ireg) sg,
        is_call (Pcall_r r sg).

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
        is_jmp (Pjmp_r r sg).

  Inductive intermediate_instruction : instruction -> Prop :=
  | ii_alloc i sz: is_alloc sz i -> intermediate_instruction i
  | ii_jmp i: i = Pret \/ is_jmp i -> intermediate_instruction i.

  Inductive step: state -> trace -> state -> Prop :=
  | step_call_internal:
      forall s1 s2 s3 f0 icall f ialloc
        (PC1: pc_at s1 = Some (inl (f0, icall)))
        (PC2: pc_at s2 = Some (inl (f, ialloc)))
        (CALL: is_call icall)
        (ALLOC: is_alloc (frame_size (fn_frame f)) ialloc)
        (STEP1: RawAsm.step ge s1 E0 s2)
        (STEP2: RawAsm.step ge s2 E0 s3),
        step s1 E0 s3
  | step_call_external:
      forall s1 s2 s3 f0 icall ef t
        (PC1: pc_at s1 = Some (inl (f0, icall)))
        (CALL: is_call icall)
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
        (NOFREE: forall f0 i, r = inl (f0,i) -> ~ intermediate_instruction i)
        (NOCALL: forall f0 i, r = inl (f0,i) -> ~ is_call i)
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


  Lemma is_call_dec:
    forall i,
      is_call ge i \/ ~ is_call ge i.
  Proof.
    destruct i; try now (right; intro A; inv A).
    - destruct (Genv.find_symbol ge symb) eqn:FS.
      left; econstructor; eauto.
      right; intro A; inv A. congruence.
    - left; econstructor; eauto.
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

  Lemma is_builtin_dec i: is_builtin i \/ ~ is_builtin i.
  Proof.
    destruct i; first [right; now inversion 1|now econstructor].
  Qed.
  
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



  Lemma set_res_other:
    forall res vres rs r,
      ~ in_builtin_res res r ->
      set_res res vres rs r = rs r.
  Proof.
    induction res; simpl; intros; eauto.
    rewrite Pregmap.gso; auto.
    rewrite IHres2. apply IHres1. intuition. intuition.
  Qed.

  
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
            Ptrofs.unsigned o' + instr_size ifree = Ptrofs.unsigned o;

      wf_asm_pc_repr:
        forall i o,
          find_instr (Ptrofs.unsigned o) (fn_code f) = Some i ->
          Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (instr_size i))) = Ptrofs.unsigned o + instr_size i;

      wf_asm_code_bounded:
        0 <= code_size (fn_code f) <= Ptrofs.max_unsigned;

      wf_asm_builtin_not_PC:
        forall o ef args res,
          find_instr o (fn_code f) = Some (Pbuiltin ef args res) ->
          ~ in_builtin_res res PC;

    }.

  Hypothesis wf_asm_prog:
    forall b f,
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      wf_asm_function f.

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

  Lemma find_instr_no_overlap':
    forall l o1 o2 i1 i2,
      find_instr o1 l = Some i1 ->
      find_instr o2 l = Some i2 ->
      i1 = i2 \/ o1 + instr_size i1 <= o2 \/ o2 + instr_size i2 <= o1.
  Proof.
    intros l o1 o2 i1 i2 FI1 FI2.
    destruct (zeq o1 o2). subst. rewrite FI1 in FI2; inv FI2; auto.
    right.
    eapply find_instr_no_overlap; eauto.
  Qed.

  Lemma intermediate_before:
    forall f i0 i i1,
      wf_asm_function f ->
      find_instr (Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr (instr_size i)))) (fn_code f) = Some i1 ->
      find_instr (Ptrofs.unsigned i0) (fn_code f) = Some i ->
      intermediate_instruction ge i1 ->
      intermediate_instruction ge i \/ is_call ge i \/ exists sz, is_free sz i.
  Proof.
    intros f i0 i i1 WF FI1 FI II1.
    inv II1.
    {
      inv H. exploit wf_asm_alloc_only_at_beginning. eauto. apply FI1.
      erewrite wf_asm_pc_repr; eauto.
      generalize (Ptrofs.unsigned_range i0) (instr_size_positive i); omega.
    }
    {
      exploit wf_asm_ret_jmp_comes_after_freeframe. eauto. 2: eauto. eauto.
      intros (o' & ifree & FI' & IFREE & RNG).
      generalize (find_instr_no_overlap' _ _ _ _ _ FI FI').
      intros [EQ|RNG']. right; right; subst. eauto.
      erewrite wf_asm_pc_repr in RNG; eauto.
      generalize (instr_size_positive ifree) (instr_size_positive i); omega.
    }
  Qed.

  Lemma exec_load_nextinstr:
    forall chunk m a r rd sz r0 m0,
      rd <> PC ->
      exec_load ge chunk m a r rd sz = Next r0 m0 ->
      r0 PC = Val.offset_ptr (r PC) sz.
  Proof.
    unfold exec_load; intros chunk m a r rd sz r0 m0 NOPC EL; repeat destr_in EL. simpl_regs.
    auto.
  Qed.

  Lemma exec_store_nextinstr:
    forall chunk m a r rd lrd sz r0 m0,
      rd <> PC -> Forall (fun x => x <> PC) lrd ->
      exec_store ge chunk m a r rd lrd sz = Next r0 m0 ->
      r0 PC = Val.offset_ptr (r PC) sz.
  Proof.
    unfold exec_store; intros chunk m a r rd lrd sz r0 m0 NOPC NOTPC EL; repeat destr_in EL. simpl_regs.
    rewrite Asmgenproof0.undef_regs_other. auto.
    intros r' IN EQ; subst. rewrite Forall_forall in NOTPC; apply NOTPC in IN. congruence.
  Qed.

  Lemma label_pos_rng:
    forall lbl c pos z,
      label_pos lbl pos c = Some z ->
      0 <= pos ->
      0 <= z - pos <= code_size c.
  Proof.
    induction c; simpl; intros; eauto. congruence. repeat destr_in H.
    generalize (code_size_non_neg c) (instr_size_positive a); omega.
    apply IHc in H2.
    generalize (instr_size_positive a); omega.
    generalize (instr_size_positive a); omega.
  Qed.

  Lemma label_pos_repr:
    forall lbl c pos z,
      code_size c + pos <= Ptrofs.max_unsigned ->
      0 <= pos ->
      label_pos lbl pos c = Some z ->
      Ptrofs.unsigned (Ptrofs.repr (z - pos)) = z - pos.
  Proof.
    intros.
    apply Ptrofs.unsigned_repr.
    generalize (label_pos_rng _ _ _ _ H1 H0). omega.
  Qed.

  Lemma find_instr_ofs_pos:
    forall c o i,
      find_instr o c = Some i ->
      0 <= o.
  Proof.
    induction c; simpl; intros; repeat destr_in H.
    omega. apply IHc in H1. generalize (instr_size_positive a); omega.
  Qed. 
  
  Lemma label_pos_spec:
    forall lbl c pos z,
      code_size c + pos <= Ptrofs.max_unsigned ->
      0 <= pos ->
      label_pos lbl pos c = Some z ->
      find_instr ((z - pos) - instr_size (Plabel lbl)) c = Some (Plabel lbl).
  Proof.
    induction c; simpl; intros; repeat destr_in H1. 
    destruct a; simpl in Heqb; try congruence. repeat destr_in Heqb.
    apply pred_dec_true. omega.
    eapply IHc in H3. 2: omega. 2: generalize (instr_size_positive a); omega.
    generalize (find_instr_ofs_pos _ _ _ H3). intro.
    rewrite pred_dec_false. 2: generalize (instr_size_positive a); omega.
    rewrite <- H3. f_equal. omega.                  
  Qed.

  Lemma goto_label_PC:
    forall f l r m r0 m0
      (GL: goto_label ge f l r m = Next r0 m0)
      b i
      (PCbef: r PC = Vptr b i)
      (FFP: Genv.find_funct_ptr ge b = Some (Internal f)) ,
      (forall f0 i2,
          pc_at ge (State r0 m0) = Some (inl (f0,i2)) ->
          ~ intermediate_instruction ge i2)
      /\ (forall ef,
            pc_at ge (State r0 m0) = Some (inr ef) ->
            False ).
  Proof.
    intros.
    simpl.
    unfold goto_label in GL.
    rewrite PCbef, FFP in GL. destr_in GL. inv GL. simpl_regs. rewrite FFP.
    destr. split. 2: inversion 1. intros f0 i2 EQ; inv EQ.
    assert (EQz: Ptrofs.unsigned (Ptrofs.repr z) = z).
    {
      replace z with (z-0) by omega.
      eapply label_pos_repr. rewrite Z.add_0_r. eapply wf_asm_code_bounded. eauto. omega. eauto.
    } rewrite EQz in *.
    generalize (label_pos_spec l (fn_code f0) 0 z). intro LPS; trim LPS.
    rewrite Z.add_0_r. apply wf_asm_code_bounded; eauto. trim LPS. omega. trim LPS; auto.
    generalize (find_instr_ofs_pos _ _ _ LPS).
    intros POS II; inv II.
    {
      inv H. exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo0.
      generalize (instr_size_positive (Plabel l)); omega.
    }
    {
      exploit wf_asm_ret_jmp_comes_after_freeframe. eauto. 2: apply H.
      rewrite EQz. eauto.
      intros (o' & ifree & FI & IFREE & RNG).
      generalize (find_instr_no_overlap' _ _ _ _ _ FI LPS).
      intros [EQ|NOOV]. subst; inv IFREE.
      rewrite EQz in *.
      generalize (instr_size_positive ifree) (instr_size_positive (Plabel l)). omega.
    }
  Qed.

  Lemma normal_steps_preserves_normal:
    forall s1 f i s2,
      pc_at ge s1 = Some (inl (f, i)) ->
      ~ intermediate_instruction ge i ->
      ~ is_call ge i ->
      ~ (exists sz, is_free sz i) ->
      exec_instr ge f i (rs_state s1) (m_state s1) = Next (rs_state s2) (m_state s2) ->
      (forall f0 i0, pc_at ge s2 = Some (inl (f0, i0)) -> ~ intermediate_instruction ge i0) /\
      (forall ef, pc_at ge s2 = Some (inr ef) -> False).
  Proof.
    intros s1 f i s2 PC1 INV NOTCALL NOTFREE EI.
    unfold pc_at in *. repeat destr_in PC1. destr. simpl in *. subst.
    destruct (Val.eq (r0 PC) (Val.offset_ptr (r PC) (Ptrofs.repr (instr_size i)))).
    ++ rewrite e, Heqv; simpl. rewrite Heqo.
       destr.
       split. 2: inversion 1. intros f0 i2 FI; inv FI.
       intro II; eapply intermediate_before in II; eauto.
       destruct II as [II|[CALL|FRE]]; eauto.
    ++ destruct i;
         first
           [ exfalso; simpl in EI; repeat destr_in EI; simpl_regs_in n; rewrite Heqv in n; simpl in n; congruence
           | exfalso; simpl in EI; apply n; eapply exec_load_nextinstr; eauto; congruence
           | exfalso; simpl in EI; apply n; eapply exec_store_nextinstr; eauto; congruence
           |   exfalso; simpl in EI; apply n; eapply (fun pf pf' => exec_store_nextinstr _ _ _ _ _ _ _ _ _ pf pf' EI); eauto; repeat constructor; congruence
           | idtac
           ].
       simpl in EI. unfold compare_ints in EI. inv EI. simpl_regs_in n. congruence.
       simpl in EI. unfold compare_longs in EI. inv EI. simpl_regs_in n. congruence.
       simpl in EI. unfold compare_ints in EI. inv EI. simpl_regs_in n. congruence.
       simpl in EI. unfold compare_longs in EI. inv EI. simpl_regs_in n. congruence.
       simpl in EI. unfold compare_ints in EI. inv EI. simpl_regs_in n. congruence.
       simpl in EI. unfold compare_longs in EI. inv EI. simpl_regs_in n. congruence.
       simpl in EI. unfold compare_ints in EI. inv EI. simpl_regs_in n. congruence.
       simpl in EI. unfold compare_longs in EI. inv EI. simpl_regs_in n. congruence.
       simpl in EI. exfalso. unfold compare_floats in EI. inv EI. apply n. simpl_regs.
       repeat destr; simpl_regs; congruence.
       simpl in EI. exfalso. unfold compare_floats32 in EI. inv EI. apply n. simpl_regs.
       repeat destr; simpl_regs; congruence.
       simpl in EI.
       eapply goto_label_PC; eauto.
       edestruct wf_asm_jmp_target_exists as (bf & f'  & SA & _); eauto. unfold Genv.symbol_address in SA; destr_in SA.
       exfalso; apply INV; constructor. right; econstructor; eauto.
       exfalso; apply INV; constructor. right; econstructor; eauto.
       simpl in EI. repeat destr_in EI. eapply goto_label_PC; eauto. simpl_regs_in n. congruence.
       simpl in EI. repeat destr_in EI. eapply goto_label_PC; eauto. simpl_regs_in n. congruence.
       simpl_regs_in n; congruence.
       simpl in EI. repeat destr_in EI. eapply goto_label_PC; eauto.
       exfalso; apply NOTCALL.
       edestruct wf_asm_call_target_exists as (bf & f'  & SA & _); eauto. unfold Genv.symbol_address in SA; destr_in SA.
       econstructor; eauto.
       exfalso; apply NOTCALL. econstructor.
       exfalso; apply INV. constructor. auto.
       simpl in *. inv EI. rewrite Heqv, Heqo, Heqo0.
       split. 2: inversion 1. intros f0 i A; inv A; eauto.
  Qed.

  Inductive match_states : state -> state -> Prop :=
  | match_states_intro
      s
      (INV: forall f i, pc_at ge s = Some (inl (f, i)) -> ~ intermediate_instruction ge i)
      (INV2: forall ef, pc_at ge s = Some (inr ef) -> False):
      match_states s s.
  
  Lemma step_correct:
    forall rs s t s' 
      (STEP : step ge s t s')
      (MS: match_states s s)
      (SAFE: safe (RawAsm.semantics prog rs) s),
      plus RawAsm.step (Genv.globalenv prog) s t s' /\ match_states s' s'.
  Proof.
    intros.
    inv MS.
    inv STEP.
    - split. eapply plus_two; eauto.
      exploit step_internal. apply STEP1. eauto. intro IB; inv IB; inv CALL. intros (EI1 & _).
      exploit step_internal. apply STEP2. eauto. intro IB; inv IB; inv ALLOC. intros (EI2 & _).
      clear STEP1 STEP2.
      destruct s2, s'; simpl in *; subst. repeat destr_in PC2.
      inv ALLOC. simpl in EI2. repeat destr_in EI2.
      constructor.
      + simpl. simpl_regs. rewrite Heqv. simpl. rewrite Heqo.
        destr. intros f2 i1 A; inv A. intro A.
        inv A.
        {
          inv H1. exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo0. intro I0.
          exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo2.
          rewrite Ptrofs.add_unsigned. rewrite I0. introrewrite Ptrofs.unsigned_repr by apply instr_size_repr.
          unfold make_palloc. apply not_eq_sym. apply Z.lt_neq. apply instr_size_positive.
        }
        {
          exploit wf_asm_ret_jmp_comes_after_freeframe; eauto.
          intros (o' & ifree & FI & IFREE & RNG).
          exploit wf_asm_alloc_at_beginning; eauto.
          intro FALLOC.
          generalize (find_instr_no_overlap' _ _ _ _ _ FI FALLOC).
          rewrite Ptrofs.unsigned_repr in RNG by apply instr_size_repr.
          rewrite RNG.
          intros [EQ|NOOV]. subst; inv IFREE.
          generalize (instr_size_positive (make_palloc (fn_frame f1))) (instr_size_positive ifree). omega.
        }
    - eapply plus_two; eauto.
    - eapply plus_two; eauto.
    - eapply plus_three; eauto.
    - eapply plus_three; eauto.
    - apply plus_one; auto.
  Qed.

  
  Lemma group_progress:
    forall rs s1
      (SAFE : safe (RawAsm.semantics prog rs) s1)
      (INV: forall f i, pc_at ge s1 = Some (inl (f, i)) -> ~ intermediate_instruction ge i)
      (INV2: forall ef, pc_at ge s1 = Some (inr ef) -> False),
      (exists r, final_state s1 r) \/ (exists t s2, step (Genv.globalenv prog) s1 t s2)
      (* /\ *)
      (*                                    (forall f i, pc_at ge s2 = Some (inl (f, i)) -> ~ intermediate_instruction ge i) /\ *)
      (*                                    (forall ef, pc_at ge s2 = Some (inr ef) -> False)) *).
  Proof.
    intros.
    destruct (SAFE _  (star_refl _ _ _)) as [(r & FS)|(t & s2 & STEP)].
    eauto.
    destruct (pc_at ge s1) as [[[f i]|ef]|] eqn:PCs.
    - destruct (is_call_dec i) as [CALL|NOTCALL].
      + (* it's a call instruction : the next step is going to be either an external function or a Pallocframe. *)
        simpl in STEP.
        exploit step_internal; eauto. intro IB; inv IB; inv CALL. intros (EI & T0). subst.
        destruct (SAFE _ (star_one _ _ _ _ _ STEP)) as [(r & FS)|(t & s3 & STEP2)].
        * inv FS. simpl in EI.
          inv CALL; simpl in EI; repeat destr_in EI.
          -- simpl_regs_in H. unfold Genv.symbol_address in H. repeat destr_in H.
          -- simpl_regs_in H. rewrite H in Heqo.  inv Heqo.
        * simpl in STEP2.
          assert (exists b f', Genv.find_funct_ptr ge b = Some f' /\
                          rs_state s2 PC = Vptr b Ptrofs.zero).
          {
            inv CALL; simpl in EI; repeat destr_in EI.
            - unfold pc_at in PCs; repeat destr_in PCs; simpl in *; subst.
              eapply wf_asm_call_target_exists in Heqo0; eauto.
              destruct Heqo0 as (bf & f' & SA & FFP).
              inv STEP2; simpl in *; subst; simpl_regs; simpl_regs_in H0; eauto.
            - simpl_regs. unfold Genv.find_funct in Heqo; repeat destr_in Heqo. eauto.
          }
          destruct H as (b & f' & FFP & PC2).
          inversion STEP2; subst.
          -- simpl in *. rewrite_hyps.
             right; exists E0, (State rs' m'). (* split. *)
             eapply step_call_internal.  5: apply STEP. 5: apply STEP2. eauto.
             unfold pc_at. rewrite PC2. rewrite H0, H1. eauto. eauto.
             erewrite wf_asm_alloc_at_beginning in H1; eauto. inv H1. apply make_palloc_is_alloc.
             (* simpl. *)
             (* erewrite wf_asm_alloc_at_beginning in H1; eauto. inv H1. *)
             (* simpl in H2. repeat destr_in H2. unfold ge in FFP; rewrite FFP in H0. inv H0. *)
             (* simpl_regs. rewrite PC2. simpl. unfold ge. rewrite FFP. *)
             (* destr. split; inversion 1; subst. intro A. *)
             (* rewrite Ptrofs.add_zero_l in Heqo0. *)
             (* inv A. *)
             (* { *)
             (*   inv H0. exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo0. *)
             (*   rewrite Ptrofs.unsigned_repr by apply instr_size_repr. *)
             (*   unfold make_palloc. apply not_eq_sym. apply Z.lt_neq. apply instr_size_positive.  *)
             (* } *)
             (* { *)
             (*   exploit wf_asm_ret_jmp_comes_after_freeframe; eauto. *)
             (*   intros (o' & ifree & FI & IFREE & RNG). *)
             (*   exploit wf_asm_alloc_at_beginning; eauto. *)
             (*   intro FALLOC. *)
             (*   generalize (find_instr_no_overlap' _ _ _ _ _ FI FALLOC). *)
             (*   rewrite Ptrofs.unsigned_repr in RNG by apply instr_size_repr. *)
             (*   rewrite RNG. *)
             (*   intros [EQ|NOOV]. subst; inv IFREE. *)
             (*   generalize (instr_size_positive (make_palloc (fn_frame f1))) (instr_size_positive ifree). omega. *)
             (* } *)
          -- simpl in *. rewrite_hyps.
             erewrite wf_asm_alloc_at_beginning in H1; eauto. inv H1. 
          -- simpl in PC2. rewrite_hyps.
             right; eexists t, (State _ m').
             eapply step_call_external.  4: apply STEP. 4: apply STEP2. eauto. eauto.
             unfold pc_at. rewrite PC2. rewrite H0. eauto.
             Opaque destroyed_at_call.
             (* simpl. simpl_regs. *)
             (* unfold pc_at in PCs; repeat destr_in PCs. *)
             (* assert (rs0 RA = Vptr b (Ptrofs.add i0 (Ptrofs.repr (instr_size i)))). *)
             (* { *)
             (*   inv CALL; simpl in EI; repeat destr_in EI; simpl_regs; rewrite Heqv; simpl; auto. *)
             (* } *)
             (* rewrite H. rewrite Heqo. destr. split; inversion 1; subst. *)
             (* intro II; inv II. *)
             (* { *)
             (*   inv H4. exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo1. *)
             (*   erewrite wf_asm_pc_repr; eauto. *)
             (*   generalize (Ptrofs.unsigned_range i0) (instr_size_positive i); omega. *)
             (* } *)
             (* { *)
             (*   exploit wf_asm_ret_jmp_comes_after_freeframe; eauto. *)
             (*   intros (o' & ifree & FI & IFREE & RNG). *)
             (*   generalize (find_instr_no_overlap _ _ _ _ _ FI Heqo0). *)
             (*   intro NOOV. trim NOOV. intro EQ; rewrite EQ in FI. rewrite FI in Heqo0; inv Heqo0. inv IFREE; inv CALL. *)
             (*   erewrite wf_asm_pc_repr in RNG; eauto. rewrite RNG in NOOV.  *)
             (*   generalize (instr_size_positive ifree) (instr_size_positive i); omega. *)
             (* } *)
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
             eexists _, _. split. eapply step_free_ret. 4: apply STEP. 4: apply STEP2.
             eauto. eauto. eauto.
             exploit step_internal; eauto. intro IB; inv IB. intros (EI & T0).
             simpl in EI. inv EI. unfold pc_at. destr. simpl in *. subst. simpl_regs.
             exploit step_internal. apply STEP. eauto. intro IB; inv IB. intros (EI & _).
             simpl in EI. repeat destr_in EI. simpl_regs. destr. inv Heqo.
             destr. admit.
             (* ret should jump right after a call instruction, i.e. not alloc
             or ret or jmp. (jmp_s and jmp_r are used exclusively for tailcalls,
             while jmp_l is used for "goto labels") -- not easy to ensure
             because RA is stored in memory. --> ensure in the semantics ?*)
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
               right; do 2 eexists. split. eapply step_free_tailcall.
               apply PCs. apply PC2. apply PC3.
               all: eauto.
               unfold pc_at in PC3; repeat destr_in PC3.
               unfold pc_at. destr. subst. simpl in H. inv ALLOC; simpl in H. repeat destr_in H.
               simpl_regs. rewrite Heqv0. simpl. rewrite Heqo0. repeat destr.
               intros. split; [intros f1 i1 EQ | intros ef EQ]; inv EQ.
               intro A; inv A.
               {
                 inv H. exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo3.
                 erewrite wf_asm_pc_repr; eauto. 
                 generalize (Ptrofs.unsigned_range i) (instr_size_positive (Pallocframe f0 (Ptrofs.sub (Ptrofs.repr (align (frame_size (fn_frame f1)) 8)) (Ptrofs.repr (size_chunk Mptr)))) ); omega.
               }
               {
                 exploit wf_asm_ret_jmp_comes_after_freeframe; eauto.
                 intros (o' & ifree & FI & IFREE & RNG).
                 generalize (find_instr_no_overlap' _ _ _ _ _ FI Heqo1). intros [EQ|NOOV].
                 destruct H as [H|H]; subst; inv IFREE; inv H.
                 erewrite wf_asm_pc_repr in RNG; eauto. rewrite <- RNG in NOOV.
                 generalize (instr_size_positive (Pallocframe f0 (Ptrofs.sub (Ptrofs.repr (align (frame_size (fn_frame f1)) 8)) (Ptrofs.repr (size_chunk Mptr))))).
                 generalize (instr_size_positive ifree). omega.
               }

             ++ right; do 2 eexists. split. eapply step_free_external.
                apply PCs. apply PC2. apply PC3. all: eauto.
                unfold pc_at in PC3; repeat destr_in PC3.
                unfold pc_at. destr. subst.
                inv STEP3; simpl in *; unfold ge in *; rewrite_hyps; try congruence.
                simpl_regs.
                assert (r RA = v).
                edestruct step_internal. apply STEP2. eauto. intro IB; inv IB; inv JMP.
                edestruct step_internal. apply STEP. eauto. intro IB; inv IB.
                simpl in H3. rewrite Heqo in H3. inv H3.
                inv JMP; simpl in H; repeat destr_in H. rewrite <- H6. simpl_regs. auto.
                rewrite <- H6. simpl_regs. auto.
                rewrite H.
                (* ret should jump right after a call instruction, i.e. not alloc
                   or ret or jmp. (jmp_s and jmp_r are used exclusively for tailcalls,
                   while jmp_l is used for "goto labels") *)
                admit.

        * (* not call nor free -> regular step *)

          right; do 2 eexists. split.
          eapply step_other. eauto.
          inversion 1; subst. intros f ISFREE; apply NISFREE. eauto.
          intros. inv H. eapply INV. eauto. 
          inversion 1; subst; intros; eauto. eauto.
          destruct (is_builtin_dec i) as [IB|NIB].
          -- unfold pc_at in PCs; repeat destr_in PCs.
             simpl in STEP. inv STEP; unfold ge in *; rewrite_hyps; try congruence.
             inv IB. simpl in H6. congruence.
             simpl. simpl_regs.
             rewrite set_res_other.
             rewrite Asmgenproof0.undef_regs_other.
             rewrite Heqv. simpl. rewrite Heqo.
             destr. split;[intros f i0 EQ|intros eef EQ]; inv EQ.
             intro II; inv II.
             {
               inv H. exploit wf_asm_alloc_only_at_beginning. eauto. apply Heqo1.
               erewrite wf_asm_pc_repr; eauto.
               generalize (Ptrofs.unsigned_range ofs) (instr_size_positive (Pbuiltin ef args res)); omega.
             }
             {
               exploit wf_asm_ret_jmp_comes_after_freeframe; eauto.
               intros (o' & ifree & FI & IFREE & RNG).
               generalize (find_instr_no_overlap _ _ _ _ _ FI Heqo0).
               intro NOOV. trim NOOV. intro EQ; rewrite EQ in FI. rewrite FI in Heqo0; inv Heqo0. inv IFREE; inv CALL.
               erewrite wf_asm_pc_repr in RNG; eauto. rewrite RNG in NOOV. 
               generalize (instr_size_positive ifree) (instr_size_positive (Pbuiltin ef args res)); omega.
             }
             {
               intros r'  IN EQ; subst.
               apply in_map_iff in IN. destruct IN as (mr & EQ & _).
               eapply Asmgenproof0.preg_of_not_PC; eauto.
             }
             {
               eapply wf_asm_builtin_not_PC; eauto.
             }
          -- edestruct step_internal. apply STEP. eauto. auto. subst.
             specialize (INV _ _ eq_refl).
             simpl in *.
             fold ge in STEP.
             eapply normal_steps_preserves_normal; eauto.

    - edestruct INV2. eauto.
    - unfold pc_at in PCs. destr_in PCs. inv STEP; simpl in *; unfold ge in *; repeat destr_in PCs.
  Admitted.

  Theorem group_correct:
    forall rs,
      backward_simulation (RawAsm.semantics prog rs) (semantics prog rs).
  Proof.
    intro rs.
    eapply backward_simulation_plus with (match_states := fun (s1 s2: Asm.state) =>
                                                            s1 = s2 /\
                                                            (forall f i, pc_at ge s1 = Some (inl (f, i)) -> ~ intermediate_instruction ge i)
                                                            /\ ( forall ef, pc_at ge s1 = Some (inr ef) -> False)
                                         ).
    - reflexivity.
    - intros; eauto.
    - simpl; intros s1 s2 I1 I2. eexists; split. apply I1.
      inv I1; inv I2. rewrite_hyps.
      inv H0; inv H2. rewrite_hyps. split. unfold rs0, rs1. f_equal.
      simpl. unfold rs0. simpl_regs.
      unfold Genv.symbol_address.
      destr. repeat destr_in Heqv. destr. admit.
    - intros s1 s2 r (eq & NOINT & NOEXT) FS; subst. auto.
    - simpl; intros s1 s2 (EQ & NOINT & NOEXT) SAFE; subst.
      edestruct (group_progress _ _ SAFE NOINT NOEXT) as [(r & FS)|(r & s2' & STEP & _)]; eauto.      
    - simpl; intros s2 t s2' STEP s1 (EQ & NOINT & NOEXT) SAFE. subst.
      eexists; split; eauto.
      eapply step_correct; eauto.
  Qed.

End SIMU.
