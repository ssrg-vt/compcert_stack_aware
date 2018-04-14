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
Require Import Asmgen.
Require Asmgenproof0.
Require Import Errors.

Section WITHMEMORYMODEL.

  (* Context {mem} `{memory_model: Mem.MemoryModel mem}. *)

  Existing Instance mem_accessors_default.

  Context {mem} `{external_calls_props: ExternalCallsProps mem}
          `{enable_builtins_instance: !EnableBuiltins (memory_model_ops:=memory_model_ops) mem}.

  Definition stack_invar (i: instr_with_info) :=
    match i with
    | (i,_) =>
      match i with
        Pallocframe _ _  
      | Pfreeframe _ _
      | Pcall_s _ _
      | Pcall_r _ _ 
      | Pret => false
      | _ => true
      end
    end.

  (** Instructions other than [Pallocframe] and [Pfreeframe] do not modify the
      content of the RSP register. We prove that Asm programs resulting from the
      Stacking pass satisfy this requirement. *)

  Definition asm_instr_no_rsp (i : Asm.instr_with_info) : Prop :=
    stack_invar i = true ->
    forall {F V} (ge: _ F V) rs1 m1 rs2 m2 f init_stk,
      Asm.exec_instr init_stk ge f i rs1 m1 = Next rs2 m2 ->
      rs2 # RSP = rs1 # RSP.

  Definition asm_code_no_rsp (c : Asm.code) : Prop :=
    forall i,
      In i c ->
      asm_instr_no_rsp i.

  Lemma asm_code_no_rsp_cons:
    forall a l,
      asm_instr_no_rsp a ->
      asm_code_no_rsp l ->
      asm_code_no_rsp (a::l).
  Proof.
    unfold asm_code_no_rsp.
    intros. simpl in H1. destruct H1; subst; auto.
  Qed.

  Lemma nextinstr_rsp:
    forall rs sz,
      nextinstr rs sz RSP = rs RSP.
  Proof.
    unfold nextinstr.
    intros; rewrite Pregmap.gso; congruence.
  Qed.

  Lemma nextinstr_nf_rsp:
    forall rs sz,
      nextinstr_nf rs sz RSP = rs RSP.
  Proof.
    unfold nextinstr_nf.
    intros. rewrite nextinstr_rsp.
    rewrite Asmgenproof0.undef_regs_other; auto.
    simpl; intuition subst; congruence. 
  Qed.

  Lemma preg_of_not_rsp:
    forall m x,
      preg_of m = x ->
      x <> RSP.
  Proof.
    unfold preg_of. intros; subst.
    destruct m; congruence.
  Qed.
  
  Lemma ireg_of_not_rsp:
    forall m x,
      Asmgen.ireg_of m = OK x ->
      IR x <> RSP.
  Proof.
    unfold Asmgen.ireg_of.
    intros m x A.
    destr_in A. inv A.
    eapply preg_of_not_rsp in Heqp.
    intro; subst. congruence.
  Qed.

  Lemma freg_of_not_rsp:
    forall m x,
      Asmgen.freg_of m = OK x ->
      FR x <> RSP.
  Proof.
    unfold Asmgen.freg_of.
    intros m x A. destr_in A. 
  Qed.


  Lemma compare_floats_rsp:
    forall a b rs1,
      compare_floats a b rs1 RSP = rs1 RSP.
  Proof.
    unfold compare_floats.
    intros.
    destruct a, b; rewrite ?Asmgenproof0.undef_regs_other by simpl; intuition congruence.
  Qed.


  Lemma compare_floats32_rsp:
    forall a b rs1,
      compare_floats32 a b rs1 RSP = rs1 RSP.
  Proof.
    unfold compare_floats32.
    intros.
    destruct a, b; rewrite ?Asmgenproof0.undef_regs_other by simpl; intuition congruence.
  Qed.


  Lemma exec_load_rsp:
    forall F V (ge: _ F V) K m1 am rs1 f0 rs2 m2 sz,
      IR RSP <> f0->
      exec_load ge K m1 am rs1 f0 sz = Next rs2 m2 ->
      rs2 RSP = rs1 RSP.
  Proof.
    intros F V ge' K m1 am rs1 f0 rs2 m2 sz DIFF LOAD.
    unfold exec_load in LOAD. destr_in LOAD. inv LOAD.
    rewrite nextinstr_nf_rsp. 
    rewrite Pregmap.gso. auto. auto. 
  Qed.

  Lemma exec_store_rsp:
    forall F V (ge: _ F V)  K m1 am rs1 f0 rs2 m2 (l: list preg) sz, (* preg_of m = f0 -> *)
      (forall r' : PregEq.t, In r' l -> r' <> RSP) ->
      exec_store ge K m1 am rs1 f0 l sz = Next rs2 m2 ->
      rs2 RSP = rs1 RSP.
  Proof.
    intros F V ge' K m1 am rs1 f0 rs2 m2 l sz INL STORE.
    unfold exec_store in STORE. repeat destr_in STORE.
    rewrite nextinstr_nf_rsp. 
    rewrite Asmgenproof0.undef_regs_other.
    auto. intros; apply not_eq_sym. auto.
  Qed.

  Ltac solve_rs:=
    repeat match goal with
             H2 : Next _ _ = Next _ _ |- _ =>
             inv H2
           | |- _ :preg <> RSP => eapply preg_of_not_rsp; eauto
           | |- _ :preg<> RSP => eapply ireg_of_not_rsp; eauto
           | |- _ :preg <> RSP => eapply freg_of_not_rsp; eauto
           | |- RSP <> _  => apply not_eq_sym
           | |- _ => rewrite ?nextinstr_nf_rsp, ?nextinstr_rsp, ?compare_floats_rsp, ?compare_floats32_rsp;
                   try rewrite Pregmap.gso by (apply not_eq_sym; eapply ireg_of_not_rsp; eauto);
                   try rewrite Pregmap.gso by (apply not_eq_sym; eapply freg_of_not_rsp; eauto);
                   try reflexivity

           end.


  Lemma loadind_no_change_rsp:
    forall i t m x0 x1 r,
      asm_code_no_rsp x0 ->
      loadind r i t m x0 = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    intros i t m x0 x1 r IH EQ.
    unfold loadind in EQ. unfold Asmgen.loadind in EQ.
    unfold Asmgen.instr_to_with_info in EQ; simpl in EQ.
    repeat destr_in EQ; apply asm_code_no_rsp_cons; auto; red; simpl;
    intros _ F V ge rs1 m1 rs2 m2 ff init_stk EI; unfold exec_instr in EI; simpl in EI;
      eapply exec_load_rsp; eauto; apply not_eq_sym; solve_rs.
  Qed.

  Lemma storeind_no_change_rsp:
    forall i t m x0 x1 r,
      asm_code_no_rsp x0 ->
      storeind m r i t x0 = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    intros i t m x0 x1 r IH EQ.
    unfold storeind in EQ. unfold Asmgen.storeind in EQ.
    repeat destr_in EQ; apply asm_code_no_rsp_cons; auto; red; simpl;
      intros _ F V ge rs1 m1 rs2 m2 ff init_stk EI; unfold exec_instr in EI; simpl in EI;
      eapply exec_store_rsp; eauto; simpl; intuition subst; congruence.
  Qed.

  Lemma mk_move_nochange_rsp:
    forall x0 x1 m m0,
      asm_code_no_rsp x0 ->
      mk_mov (preg_of m) (preg_of m0) x0 = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    intros x0 x1 m m0 A B.
    unfold mk_mov in B. unfold Asmgen.mk_mov in B.
    repeat destr_in B; apply asm_code_no_rsp_cons; auto; red; simpl; intros;
      inv H0; rewrite nextinstr_rsp;
        rewrite Pregmap.gso; auto;
          apply not_eq_sym; eapply preg_of_not_rsp; eauto.
  Qed.  
  
  Ltac invasm :=
    repeat match goal with
             H: bind _ ?x = OK ?x1 |- _ =>
             monadInv H
           | H: exec_instr ?init_stk _ _ _ _ _ = _ |- _ =>
             unfold exec_instr in H; simpl in H; inv H
           | |- _ => apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs
           end.

  Lemma mkset_cc_no_rsp:
    forall x0 m x2 i c,
      asm_code_no_rsp x0 ->
      In i (mk_setcc c x2 x0) ->
      Asmgen.ireg_of m = OK x2 ->
      asm_instr_no_rsp i.
  Proof.
    intros x0 m x2 i c A B C.
    Ltac ainr :=
      match goal with
        |- asm_instr_no_rsp (?i, _) =>
        let invar := fresh "invar" in
        let F := fresh "F" in
        let V := fresh "V" in
        let ge := fresh "ge" in
        let rs1 := fresh "rs1" in
        let m1 := fresh "m1" in
        let rs2 := fresh "rs2" in
        let m2 := fresh "m2" in
        let init_stk := fresh "init_stk" in
        let EI := fresh "EI" in
        intros invar F V ge rs1 m1 rs2 m2 f init_stk EI;
        unfold Asm.exec_instr in EI; simpl in EI; solve_rs
      end.
    unfold mk_setcc in B. unfold Asmgen.mk_setcc in B.
    destr_in B; destruct c; simpl in *;
      unfold Asmgen.mk_setcc_base, Asmgen.code_to_with_info, Asmgen.instr_to_with_info in *; simpl in *;
        (intuition subst; simpl in *; auto; try ainr).
    - destr_in B; simpl in *; intuition subst; simpl in *; auto; try ainr.
    - destr_in B; simpl in *; intuition subst; simpl in *; auto; try ainr.
  Qed.

  Lemma asmgen_transl_cond_rsp:
    forall x0 m x2 x1 cond l,
      asm_code_no_rsp x0 ->
      Asmgen.ireg_of m = OK x2 ->
      transl_cond cond l (mk_setcc (Asmgen.testcond_for_condition cond) x2 x0) = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    unfold transl_cond, Asmgen.transl_cond; simpl.
    intros x0 m x2 x1 cond l ACNR IREG TRANSL.
    repeat destr_in TRANSL; try destruct (c:comparison);
      invasm; eauto;
        simpl in *; solve_rs; eauto using mkset_cc_no_rsp.
  Qed.

  Lemma goto_label_rsp:
    forall F V (ge: _ F V) rs1 rs2 f l m1 m2,
      goto_label ge f l rs1 m1 = Next rs2 m2 ->
      rs2 RSP = rs1 RSP.
  Proof.
    unfold goto_label.
    intros F V ge rs1 rs2 f l m1 m2 A.
    repeat destr_in A. solve_rs.
  Qed.

  Lemma mkjcc_no_rsp:
    forall x0 x2 i c,
      asm_code_no_rsp x0 ->
      In i (mk_jcc c x2 x0) ->
      asm_instr_no_rsp i.
  Proof.
    intros x0 x2 i c A H1.
    unfold mk_jcc in H1.
    destr_in H1; simpl in *; intuition subst; simpl in *; unfold instr_to_with_info; auto; ainr;
      repeat destr_in EI; eauto using goto_label_rsp.
  Qed.
  
  Lemma asmgen_transl_cond_rsp':
    forall x0 x2 x1 cond l,
      asm_code_no_rsp x0 ->
      transl_cond cond l (mk_jcc (Asmgen.testcond_for_condition cond) x2 x0) = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    unfold transl_cond; simpl.
    intros x0 x2 x1 cond l ACNR TRANSL.
    repeat destr_in TRANSL;
      try destruct (c: comparison);
      invasm; eauto; unfold Asmgen.instr_to_with_info in *; intuition subst; eauto; try solve_rs;
        ainr; repeat destr_in EI; eauto using goto_label_rsp.
  Qed.

  Lemma intconv_no_change_rsp:
    forall x0
      (ACNR : asm_code_no_rsp x0)
      m x3
      (IREG: Asmgen.ireg_of m = OK x3)
      x2 x1 i
      (REC: forall x2,  asm_instr_no_rsp (Asmgen.instr_to_with_info (i x3 x2)))
      (CONV: Asmgen.mk_intconv i x3 x2 x0 = OK x1),
      asm_code_no_rsp x1.
  Proof.
    intros.
    unfold Asmgen.mk_intconv in CONV. inv CONV.
    destr; repeat apply asm_code_no_rsp_cons; auto.
    red; simpl; intros; invasm; solve_rs.
  Qed.

  Lemma asmgen_no_change_rsp:
    forall f tf,
      transf_function f = OK tf ->
      asm_code_no_rsp (Asm.fn_code tf).
  Proof.
    intros f tf TR.
    unfold transf_function, Asmgen.transf_function in TR.
    monadInv TR.
    destr_in EQ0. inv EQ0.
    unfold transl_function in EQ.
    monadInv EQ. simpl.
    unfold instr_to_with_info.
    apply asm_code_no_rsp_cons. red; simpl. congruence.
    unfold transl_code' in EQ0.
    revert EQ0.
    set (P := fun f => forall x y, f x = OK y -> asm_code_no_rsp x -> asm_code_no_rsp y).
    assert (POK: P (fun c => OK c)).
    { unfold P; simpl. inversion 1; tauto. }
    revert POK.
    generalize (Mach.fn_code f) true (fun c : code => OK c).
    clear g.
    induction c; simpl; intros; eauto.
    eapply POK; eauto. red; easy.
    eapply IHc. 2: apply EQ0.
    unfold P. intros x0 y BIND ACNR. monadInv BIND.
    eapply POK; eauto.

    Ltac t :=
      match goal with
      | EQ: context [match ?a with _ => _ end] |- _ => destr_in EQ
      | EQ: loadind _ _ _ _ _ = OK ?x |- asm_code_no_rsp ?x => eapply loadind_no_change_rsp in EQ; eauto
      | EQ: Asmgen.storeind _ _ _ _ _ = OK ?x |- asm_code_no_rsp ?x => eapply storeind_no_change_rsp in EQ; eauto
      | EQ: Asmgen.mk_intconv _ _ _ _ = OK ?x |- asm_code_no_rsp ?x => eapply intconv_no_change_rsp in EQ; eauto
      | EQ: bind _ _ = OK _ |- _ => monadInv EQ
      | EQ: OK _ = OK _ |- _ => inv EQ
      | |- asm_instr_no_rsp _ => now (red; simpl; intros; invasm; solve_rs)
      | |- asm_code_no_rsp (_ :: _) => eapply asm_code_no_rsp_cons;[red; simpl; intros; invasm; repeat t; solve_rs|eauto]
      | |- _ => intros
      end.
    Hint Resolve not_eq_sym ireg_of_not_rsp freg_of_not_rsp.
    destruct a; simpl in EQ; repeat (t; simpl).
    - unfold Asmgen.transl_op in EQ.
      repeat destr_in EQ; repeat t; try now (invasm; solve_rs).
      + eapply mk_move_nochange_rsp; eauto.
      + repeat (t; simpl).
      + eapply asmgen_transl_cond_rsp; eauto.
    - unfold Asmgen.transl_load in EQ.
      repeat t; eapply exec_load_rsp; eauto.
    - unfold Asmgen.transl_store in EQ.
      repeat t; try eapply exec_store_rsp; eauto; try easy.
      unfold Asmgen.mk_storebyte in EQ4. inv EQ4.
      repeat (t; simpl); eapply exec_store_rsp; eauto; easy.
      unfold Asmgen.mk_storebyte in EQ4. inv EQ4.
      repeat (t; simpl); eapply exec_store_rsp; eauto; easy.
    - repeat t. eapply goto_label_rsp; eauto.
    - eapply asmgen_transl_cond_rsp'; eauto.
    - erewrite goto_label_rsp. 2: eauto. solve_rs.
  Qed.

  Definition asm_instr_no_stack (i : Asm.instr_with_info) : Prop :=
    stack_invar i = true ->
    forall F V (ge: _ F V) rs1 m1 rs2 m2 f init_stk,
      Asm.exec_instr init_stk ge f i rs1 m1 = Next rs2 m2 ->
      Mem.stack m2 = Mem.stack m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).

  Lemma exec_store_stack:
    forall F V (ge: _ F V) k m1 a rs1 rs l rs2 m2 sz,
      exec_store ge k m1 a rs1 rs l sz = Next rs2 m2 ->
      Mem.stack m2 = Mem.stack m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).
  Proof.
    intros F V ge k m1 a rs1 rs l rs2 m2 sz STORE.
    unfold exec_store in STORE; repeat destr_in STORE. 
    unfold Mem.storev in Heqo; destr_in Heqo; inv Heqo.
    erewrite Mem.store_stack_blocks. 2: eauto.
    split; auto.
    split; intros.
    eapply Mem.perm_store_2; eauto.
    eapply Mem.perm_store_1; eauto.
  Qed.

  Lemma exec_load_stack:
    forall F V (ge: _ F V) k m1 a rs1 rs rs2 m2 sz,
      exec_load ge k m1 a rs1 rs sz = Next rs2 m2 ->
      Mem.stack m2 = Mem.stack m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).
  Proof.
    intros F V ge k m1 a rs1 rs rs2 m2 sz LOAD.
    unfold exec_load in LOAD; destr_in LOAD.
  Qed.

  Lemma goto_label_stack:
    forall F V (ge: _ F V) f l m1 rs1 rs2 m2,
      goto_label ge f l rs1 m1 = Next rs2 m2 ->
      Mem.stack m2 = Mem.stack m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).
  Proof.
    intros F V ge f l m1 rs1 rs2 m2 GOTO.
    unfold goto_label in GOTO; repeat destr_in GOTO.
  Qed.

  Lemma asmgen_no_change_stack i:
    asm_instr_no_stack i.
  Proof.
    red; intros IU F V ge0 rs1 m1 rs2 m2 f init_stk EI.
    destruct i as (i & info);
      destruct i; simpl in IU; try discriminate;
        unfold exec_instr in EI; simpl in EI; repeat destr_in EI;
          first [ split;[reflexivity|tauto]
                | now (eapply exec_load_stack; eauto)
                | now (eapply exec_store_stack; eauto)
                | now ( eapply goto_label_stack; eauto)
                | idtac ].
    Unshelve. all: auto.
    apply @Genv.empty_genv. exact nil. exact Mint32. exact PC. exact Ptrofs.zero.
  Qed.

  Definition asm_instr_nb_fw i:=
    forall F V (ge: _ F V) f rs1 m1 rs2 m2 init_stk,
      Asm.exec_instr init_stk ge f i rs1 m1 = Next rs2 m2 ->
      Ple (Mem.nextblock m1) (Mem.nextblock m2).

  Definition asm_code_nb_fw c :=
    forall i, In i c -> asm_instr_nb_fw i.


    Lemma exec_store_nb:
      forall F V (ge: _ F V) k m1 a rs1 rs l rs2 m2 sz,
        exec_store ge k m1 a rs1 rs l sz = Next rs2 m2 ->
        Ple (Mem.nextblock m1) (Mem.nextblock m2).
    Proof.
      intros F V ge k m1 a rs1 rs l rs2 m2 sz STORE.
      unfold exec_store in STORE; repeat destr_in STORE. 
      unfold Mem.storev in Heqo; destr_in Heqo; inv Heqo.
      rewnb. xomega.
    Qed.

    Lemma exec_load_nb:
      forall F V (ge: _ F V) k m1 a rs1 rs rs2 m2 sz,
        exec_load ge k m1 a rs1 rs sz = Next rs2 m2 ->
        Ple (Mem.nextblock m1) (Mem.nextblock m2).
    Proof.
      intros F V ge k m1 a rs1 rs rs2 m2 sz LOAD.
      unfold exec_load in LOAD; destr_in LOAD. inv LOAD.
      apply Ple_refl.
    Qed.

    Ltac destr_all:=
      repeat match goal with
               H: context[match ?a with _ => _ end] |- _ => repeat destr_in H
             end.

  Lemma asmgen_nextblock_forward i:
    asm_instr_nb_fw i.
  Proof.
    red. intros F V ge f rs1 m1 rs2 m2 init_stk EI.
    unfold exec_instr in EI.
    destruct i as(i&info); destruct i; simpl in EI; inv EI; try (apply Ple_refl);
      first [now eapply exec_load_nb; eauto
            | now (eapply exec_store_nb; eauto)
            | unfold goto_label in *; destr_all; rewnb; try xomega ].
  Qed.
  
  Lemma val_inject_set:
    forall j rs1 rs2
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
      v v' (VINJ: Val.inject j v v') r1 r,
      Val.inject j ((rs1 # r1 <- v) r) ((rs2 # r1 <- v') r).
  Proof.
    intros.
    destruct (PregEq.eq r1 r); subst; auto.
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
    forall j rs1 rs2 sz
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r)) r,
      Val.inject j (nextinstr rs1 r sz) (nextinstr rs2 r sz).
  Proof.
    unfold nextinstr.
    intros.
    apply val_inject_set; auto.
    apply Val.offset_ptr_inject; auto.
  Qed.

  Lemma val_inject_nextinstr_nf:
    forall j rs1 rs2 sz
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r)) r,
      Val.inject j (nextinstr_nf rs1 r sz) (nextinstr_nf rs2 r sz).
  Proof.
    unfold nextinstr_nf.
    intros.
    apply val_inject_nextinstr; auto.
    intros.
    apply val_inject_undef_regs; auto.
  Qed.

  Lemma exec_load_unchanged_stack:
    forall F V (ge: _ F V) chunk m1 a rs1 rd sz rs2 m2 P,
      exec_load ge chunk m1 a rs1 rd sz = Next rs2 m2 ->
      Mem.unchanged_on P m1 m2.
  Proof.
    intros F V ge chunk m1 a rs1 rd sz rs2 m2 P EL.
    assert (m1 = m2).
    - unfold exec_load in EL. destr_in EL.
    - subst; apply Mem.unchanged_on_refl.
  Qed.

  Lemma public_stack_access_app:
    forall l s b lo hi
      (ND: nodup (l ++ s))
      (NDT: Forall nodupt (l ++ s))
      (PSA: public_stack_access (l ++ s) b lo hi),
      public_stack_access s b lo hi.
  Proof.
    induction l; simpl; subst; auto.
    - intros s b lo hi ND NDT PSA.
      inversion ND; subst. inversion NDT; subst.
      apply IHl; auto.
      red. red in PSA. destr.
      edestruct (get_assoc_spec _ _ _ Heqo) as (fr & tf & INblocks & INtf & INs).
      erewrite get_assoc_stack_lnr in PSA. eauto. eauto. eauto.
      eauto. eauto. right; auto.
  Qed.

  Lemma stack_access_app:
    forall l s b lo hi
      (ND: nodup (l ++ s))
      (NDT: Forall nodupt (l ++ s))
      (PSA: stack_access (l ++ s) b lo hi),
      stack_access s b lo hi.
  Proof.
    intros l s b lo hi ND NDT [IST|PSA].
    - destruct l; simpl in *. left; eauto.
      right. red. inv ND. red in IST. simpl in IST.
      eapply H2 in IST.
      destr. exfalso; apply IST.
      rewrite <- in_stack_app; right. eapply get_frame_info_in_stack; eauto.
    - right. eapply public_stack_access_app; eauto.
  Qed.

  Lemma nodup_app:
    forall l1 l2,
      nodup (l1 ++ l2) ->
      forall b, in_stack l1 b -> in_stack l2 b -> False.
  Proof.
    induction l1; simpl; intros l2 ND b INS1 INS2; eauto.
    inv ND.
    rewrite in_stack_cons in INS1. destruct INS1 as [INS1|INS1]; eauto.
    eapply H2; eauto. rewrite <- in_stack_app. auto.
  Qed.
  
  Lemma exec_store_unchanged_stack:
    forall F V (ge: _ F V) chunk m1 a rs1 rd rds sz rs2 m2 init_stk l,
      Mem.stack m1 = l ++ init_stk ->
      exec_store ge chunk m1 a rs1 rd rds sz = Next rs2 m2 ->
      Mem.unchanged_on (fun (b : block) (o : Z) => ~ stack_access init_stk b o (o + 1)) m1 m2.
  Proof.
    intros F V ge chunk m1 a rs1 rd rds sz rs2 m2 init_stk l STK ES.
    unfold exec_store in ES. destr_in ES. inv ES.
    unfold Mem.storev in Heqo.
    destr_in Heqo.
    eapply Mem.store_unchanged_on; eauto.
    intros i0 RNG NPSA; apply NPSA; clear NPSA.
    edestruct Mem.store_valid_access_3 as (A & B & C). eauto. trim C. constructor.
    rewrite STK in C.
    eapply stack_access_inside.
    eapply stack_access_app; eauto.
    rewrite <- STK; eapply Mem.stack_norepet.
    rewrite <- STK; eapply Mem.stack_norepet'. omega. omega.
  Qed.

  Lemma goto_label_unchanged_stack:
    forall F V (ge: _ F V) m1 rs1 f lbl rs2 m2 P,
      goto_label ge f lbl rs1 m1 = Next rs2 m2 ->
      Mem.unchanged_on P m1 m2.
  Proof.
    intros F V ge m1 rs1 f lbl rs2 m2 P GL.
    unfold goto_label in GL. repeat destr_in GL.
    apply Mem.unchanged_on_refl.
  Qed.
  
  Lemma exec_instr_unchanged_stack:
    forall F V (ge: _ F V) f i rs1 m1 rs2 m2 init_stk l,
      Mem.stack m1 = l ++ init_stk ->
      Asm.exec_instr init_stk ge f i rs1 m1 = Next rs2 m2 ->
      Mem.unchanged_on
        (fun b o => ~ stack_access init_stk b o (o+1))
        m1 m2 /\
      (is_ptr (init_sp init_stk) <> None -> exists l', Mem.stack m2 = l' ++ init_stk).
  Proof.
    destruct i as [i info].

    intros rs1 m1 rs2 m2 init_stk lstk STK EI.
    split.
    {
      unfold exec_instr in EI.
      destruct i; simpl in EI; repeat destr_in EI;
        first [ now apply Mem.unchanged_on_refl
              | now (eapply exec_load_unchanged_stack; eauto)
              | now (eapply exec_store_unchanged_stack; eauto)
              | now (eapply goto_label_unchanged_stack; eauto)
              | idtac
              ].
      apply Mem.strong_unchanged_on_weak, Mem.push_new_stage_unchanged_on.
      apply Mem.strong_unchanged_on_weak, Mem.push_new_stage_unchanged_on.
      apply Mem.strong_unchanged_on_weak, Mem.unrecord_stack_block_unchanged_on; auto.
      - eapply Mem.unchanged_on_trans.
        eapply Mem.alloc_unchanged_on; eauto.
        eapply Mem.unchanged_on_trans.
        eapply Mem.store_unchanged_on. eauto.
        intros i0 RNG PSA; apply PSA; clear PSA.
        edestruct Mem.store_valid_access_3 as (A & B & C). eauto. trim C. constructor.
        revert C. rewrite_stack_blocks. rewrite STK. intro C.
        eapply stack_access_inside.
        eapply stack_access_app; eauto.
        rewrite <- STK; eapply Mem.stack_norepet.
        rewrite <- STK; eapply Mem.stack_norepet'. omega. omega.
        apply Mem.strong_unchanged_on_weak. eapply Mem.record_stack_block_unchanged_on. eauto.
      - eapply Mem.unchanged_on_trans.
        eapply Mem.free_unchanged_on; eauto.
        intros i1 RNG NPSA; apply NPSA; clear NPSA.
        destruct (is_stack_top_dec init_stk b). left. auto.
        right. red. destr. apply get_frame_info_in_stack in Heqo3.
        rewrite STK in i0. red in i0.
        exfalso. exploit Mem.stack_norepet. rewrite STK.
        intro ND. eapply nodup_app; eauto.
        destruct lstk; simpl in i0. contradict n. red. eauto.
        rewrite in_stack_cons; left; eauto.
        unfold Mem.clear_stage in Heqo1. repeat destr_in Heqo1.
        apply Mem.strong_unchanged_on_weak.
        eapply Mem.strong_unchanged_on_trans.
        eapply Mem.unrecord_stack_block_unchanged_on. eauto.
        apply Mem.push_new_stage_unchanged_on.
        Unshelve.  3: eauto. all: eauto.
        exact Many32. exact rs. exact Ptrofs.zero.
    }
    {
      intro ISPTR.
      destruct (stack_invar (i,info)) eqn:INVAR.
      - generalize (asmgen_no_change_stack (i,info) INVAR _ _ ge _ _ _ _ _ _ EI).
        intros (STKEQ & _); rewrite STKEQ; eauto.
      - unfold stack_invar in INVAR. unfold exec_instr in EI.
        set (AA := i).
        destr_in INVAR; simpl in *; repeat destr_in EI; repeat rewrite_stack_blocks; rewrite ? STK; eauto.
        + exists (nil::lstk); auto.
        + exists (nil::lstk); auto.
        + inv t. rewrite STK in H.
          destruct lstk; simpl; eauto. simpl in *.
          subst. rewrite EQ in H; inv H.
          rewrite EQ in ISPTR. simpl in ISPTR. exfalso; apply ISPTR; reflexivity.
        + inv t. revert EQ1; repeat rewrite_stack_blocks.
          rewrite <- H.  intro A; inv A. rewrite STK in H.
          destruct lstk; simpl in *; eauto. revert STK; subst.
          exfalso; apply ISPTR; reflexivity. inv H.
          rewrite app_comm_cons. eauto.
        + destruct lstk; simpl in *. 2: rewrite app_comm_cons; eauto.
          exfalso. subst.
          unfold check_top_frame in Heqb0.
          red in c; revert c.
          repeat destr_in Heqb0. simpl in *. destr. repeat destr_in Heqv1.
          rewrite andb_true_iff in H0; destruct H0.
          destruct Forall_dec; simpl in *; try congruence.
          inv f2. red in H3. simpl in H3. intuition subst.
          exploit Mem.stack_norepet. rewrite Heqs. intro ND; inv ND.
          revert c.
          repeat rewrite_stack_blocks. rewrite in_stack_cons.
          rewrite Heqs. simpl. intros [[]|INS].
          eapply H5; eauto.
    }
  Qed.

  Lemma step_unchanged_stack:
    forall (ge: genv) rs1 m1 t rs2 m2 init_stk l,
      Mem.stack m1 = l ++ init_stk ->
      step init_stk ge (State rs1 m1) t (State rs2 m2) ->
      Mem.unchanged_on (fun b o => ~ stack_access init_stk b o (o+1)) m1 m2 /\
      (is_ptr (init_sp init_stk) <> None -> exists l', Mem.stack m2 = l' ++ init_stk).
  Proof.
    intros ge rs1 m1 t rs2 m2 init_stk l STK STEP.
    inv STEP.
    - eapply exec_instr_unchanged_stack; eauto.
    - split.
      eapply Mem.unchanged_on_trans. eapply Mem.strong_unchanged_on_weak, Mem.push_new_stage_unchanged_on.
      eapply Mem.unchanged_on_trans.
      eapply Mem.unchanged_on_implies. eapply external_call_unchanged_on. eauto.
      simpl. intros b0 ofs0 NSA VB PSA; apply NSA; clear NSA.
      revert PSA. repeat rewrite_stack_blocks.
      rewrite STK. rewrite app_comm_cons. eapply stack_access_app.
      simpl. constructor. 2: easy. rewrite <- STK; apply Mem.stack_norepet.
      simpl. constructor. constructor. rewrite <- STK; apply Mem.stack_norepet'.
      eapply Mem.strong_unchanged_on_weak, Mem.unrecord_stack_block_unchanged_on; eauto.
      repeat rewrite_stack_blocks. simpl; eauto.
    - split.
      eapply Mem.unchanged_on_trans.
      eapply Mem.unchanged_on_implies. eapply external_call_unchanged_on. eauto.
      simpl. intros b0 ofs0 NSA VB PSA; apply NSA; clear NSA.
      revert PSA.
      rewrite STK. eapply stack_access_app.
      rewrite <- STK; apply Mem.stack_norepet.
      rewrite <- STK; apply Mem.stack_norepet'.
      eapply Mem.strong_unchanged_on_weak, Mem.unrecord_stack_block_unchanged_on; eauto.
      repeat rewrite_stack_blocks.
      inv TIN. rewrite STK in H. simpl.
      destruct l; simpl in *; eauto. subst. rewrite <- H. simpl. intro N; contradict N. reflexivity.
      inv H. eauto.
  Qed.

  Lemma initial_state_stack_is_app:
    forall (prog: Asm.program) rs m,
      initial_state prog (State rs m) ->
      Mem.stack m = (nil :: (make_singleton_frame_adt (Genv.genv_next (Genv.globalenv prog)) 0 0 :: nil) :: nil).
  Proof.
    intros prog rs m IS; inv IS.
    repeat rewrite_stack_blocks. simpl.
    repeat f_equal.
    eapply Mem.alloc_result in H2.
    eapply Genv.init_mem_genv_next in H1. congruence.
    eapply Genv.init_mem_stack; eauto. apply H1.
    Unshelve. exact inject_perm_all.
  Qed.

End WITHMEMORYMODEL.