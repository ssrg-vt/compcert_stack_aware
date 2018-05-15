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
Require Import RealAsm PseudoInstructions.
Require Import RealAsmproof2.
Require Import AsmRegs.

Definition match_prog (p: Asm.program) (tp: Asm.program) :=
  Linking.match_program (fun _ f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
  intros. subst. eapply Linking.match_transform_program; eauto.
Qed.

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

  Variable prog tprog: Asm.program.
  Hypothesis TRANSF: Linking.match_program (fun _ f1 f2 => f2 = transf_fundef f1) eq prog tprog.
  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof (Genv.find_symbol_match TRANSF).

  Lemma senv_preserved:
    Senv.equiv ge tge.
  Proof (Genv.senv_match TRANSF).

  Lemma genv_next_preserved:
    Genv.genv_next tge = Genv.genv_next ge.
  Proof. apply senv_preserved. Qed.

  Lemma functions_translated:
    forall b f,
      Genv.find_funct_ptr ge b = Some f ->
      Genv.find_funct_ptr tge b = Some (transf_fundef f).
  Proof. apply (Genv.find_funct_ptr_transf TRANSF). Qed.

  Lemma functions_transl:
    forall fb f,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      Genv.find_funct_ptr tge fb = Some (Internal (transf_function f)).
  Proof.
    intros. apply functions_translated in H; eauto.
  Qed.
  
  Lemma public_preserved:
    forall id : ident, Genv.public_symbol (Genv.globalenv tprog) id = Genv.public_symbol (Genv.globalenv prog) id.
  Proof.
    apply senv_preserved.
  Qed.

  Axiom instr_size_alloc:
    forall sz pub ora r i a rr,
      instr_size (Pallocframe sz pub ora) = instr_size (Plea r a) + (instr_size (Psub rr rr i)).

  Axiom instr_size_free:
    forall sz ora r s,
      instr_size (Pfreeframe sz ora) = instr_size (Padd r r s).

  Axiom instr_size_load_parent_pointer:
    forall r s rd a,
      instr_size (Pload_parent_pointer r s) = instr_size (Plea rd a).
  
  Lemma transf_instr_size:
    forall i,
      instr_size i = code_size (transf_instr i).
  Proof.
    destruct i; simpl; try omega; rewrite Z.add_0_r.
    apply instr_size_alloc; eauto.
    apply instr_size_free; eauto.
    apply instr_size_load_parent_pointer; eauto.
  Qed.


  Inductive code_at: Z -> code -> code -> Prop :=
  | code_at_nil o c: code_at o c nil
  | code_at_cons o c i c':
      find_instr o c = Some i ->
      code_at (o + instr_size i) c c' ->
      code_at o c (i::c').

  Lemma code_size_app:
    forall c1 c2,
      code_size (c1 ++ c2) = code_size c1 + code_size c2.
  Proof.
    induction c1; simpl; intros; eauto. rewrite IHc1. omega.
  Qed.

  Lemma code_at_app:
    forall b a c, code_at (code_size a) (a ++ (b ++ c)) b.
  Proof.
    induction b; intros.
    - constructor.
    - constructor. 
      replace (code_size a0) with (0 + code_size a0) by omega.
      rewrite find_instr_app by omega. reflexivity.
      replace (a0 ++ (a::b) ++ c) with ((a0 ++ a::nil) ++ b ++ c).
      replace (code_size a0 + instr_size a) with (code_size (a0 ++ a::nil)).
      apply IHb.
      rewrite code_size_app. simpl. omega.
      simpl. rewrite app_ass. simpl. reflexivity.
  Qed.

  Lemma code_at_next:
    forall a i b, code_at (instr_size i) (i :: a ++ b) a.
  Proof.
    intros.
    generalize (code_at_app a (i::nil) b). simpl. rewrite Z.add_0_r. auto.
  Qed.

  Lemma code_at_shift:
    forall i a c o,
      code_at (o - code_size a) c i -> code_at o (a ++ c) i.
  Proof.
    induction i; simpl; intros b c o CA. constructor.
    inv CA. constructor.
    replace o with ((o - code_size b) + code_size b) by omega.
    rewrite find_instr_app. auto. eapply find_instr_pos_positive; eauto.
    apply IHi.
    replace (o + instr_size a - code_size b) with (o - code_size b + instr_size a). auto. omega.
  Qed.

  Lemma find_instr_transl:
    forall c o i,
      find_instr o c = Some i ->
      code_at o (transf_code c) (transf_instr i).
  Proof.
    induction c; simpl; intros; eauto. easy.
    repeat destr_in H.
    - unfold transf_code. simpl.
      destruct transf_instr eqn:TI.
      apply (f_equal code_size) in TI. rewrite <- transf_instr_size in TI. simpl in TI. generalize (instr_size_positive i); omega.
      simpl. constructor. simpl. auto.
      simpl. apply code_at_next.
    - specialize (IHc _ _ H1).
      unfold transf_code. simpl. fold (transf_code c).
      eapply code_at_shift. rewrite <- transf_instr_size; auto.
  Qed.

  Definition id_instr (i: instruction) : bool :=
    match i with
    | Pallocframe _ _ _
    | Pfreeframe _ _
    | Pload_parent_pointer _ _ => false
    | _ => true
    end.
  
  Hypothesis WF: wf_asm_prog ge.
  Hypothesis prog_no_rsp: asm_prog_no_rsp ge.

  Lemma exec_instr_Plea:
    forall ge f r a (rs: regset) m,
      exec_instr ge f (Plea r a) rs m =
      Next (nextinstr (rs # r <- (eval_addrmode ge a rs)) (Ptrofs.repr (instr_size (Plea r a)))) m.
  Proof.
    unfold Plea, eval_addrmode.
    intros. destr.
  Qed.

  Lemma ptrofs_eq_unsigned: forall a b,
      Ptrofs.unsigned a = Ptrofs.unsigned b -> a = b.
  Proof.
    intros.
    rewrite <- (Ptrofs.repr_unsigned a).
    rewrite <- (Ptrofs.repr_unsigned b).
    rewrite H. reflexivity.
  Qed.

  Lemma eval_addrmode_offset_ptr:
    forall (rs: regset) (r: ireg) z (RSPPTR: exists b o, rs r = Vptr b o),
      eval_addrmode (Genv.globalenv tprog) (linear_addr r z) rs = Val.offset_ptr (rs r) (Ptrofs.repr z).
  Proof.
    unfold eval_addrmode. intros.
    destr.
    ++ unfold eval_addrmode64, linear_addr.
       destruct (RSPPTR) as (bb & o & RSPPTR'). rewrite RSPPTR'. simpl. rewrite Heqb.
       f_equal. rewrite Int64.add_zero_l. f_equal.
       erewrite Ptrofs.agree64_of_int_eq. eauto. apply Ptrofs.agree64_repr; auto.
    ++ unfold eval_addrmode32, linear_addr.
       destruct (RSPPTR) as (bb & o & RSPPTR'). rewrite RSPPTR'. simpl. rewrite Heqb.
       f_equal. rewrite Int.add_zero_l. f_equal.
       erewrite Ptrofs.agree32_of_int_eq. eauto. apply Ptrofs.agree32_repr; auto.
  Qed.

  Lemma id_instr_transf:
    forall i,
      id_instr i = true ->
      transf_instr i = i :: nil.
  Proof.
    destruct i; simpl; intros; congruence.
  Qed.  

  Lemma eval_addrmode64_senv_equiv:
    forall (ge1 ge2: genv) (EQ: Senv.equiv ge1 ge2) a rs,
      eval_addrmode64 ge1 a rs = eval_addrmode64 ge2 a rs.
  Proof.
    intros.
    unfold eval_addrmode64.
    destr. unfold Genv.symbol_address.
    destruct const. auto. destruct p.
    destruct EQ as (A & B & C & D). simpl in *. rewrite B. auto.
  Qed.

  Lemma eval_addrmode32_senv_equiv:
    forall (ge1 ge2: genv) (EQ: Senv.equiv ge1 ge2) a rs,
      eval_addrmode32 ge1 a rs = eval_addrmode32 ge2 a rs.
  Proof.
    intros.
    unfold eval_addrmode32.
    destr. unfold Genv.symbol_address.
    destruct const. auto. destruct p.
    destruct EQ as (A & B & C & D). simpl in *. rewrite B. auto. 
  Qed.

  Lemma eval_addrmode_senv_equiv:
    forall (ge1 ge2: genv) (EQ: Senv.equiv ge1 ge2) a rs,
      eval_addrmode ge1 a rs = eval_addrmode ge2 a rs.
  Proof.
    unfold eval_addrmode.
    intros.
    destr; eauto using eval_addrmode64_senv_equiv, eval_addrmode32_senv_equiv.
  Qed.
  
  Lemma exec_load_senv_equiv:
    forall (ge1 ge2: genv) (EQ: Senv.equiv ge1 ge2) chunk m a rs r o,
      exec_load ge1 chunk m a rs r o =
      exec_load ge2 chunk m a rs r o.
  Proof.
    unfold exec_load.
    intros; erewrite eval_addrmode_senv_equiv; eauto.
  Qed.

  Lemma exec_store_senv_equiv:
    forall (ge1 ge2: genv) (EQ: Senv.equiv ge1 ge2) chunk m a rs r lr o,
      exec_store ge1 chunk m a rs r lr o =
      exec_store ge2 chunk m a rs r lr o.
  Proof.
    unfold exec_store.
    intros; erewrite eval_addrmode_senv_equiv; eauto.
  Qed.

  Lemma label_pos_app:
    forall a b l o,
      ~ In (Plabel l) a ->
      label_pos l o (a ++ b) = label_pos l (o + code_size a) b.
  Proof.
    induction a; simpl; intros; eauto.
    rewrite Z.add_0_r; auto.
    destr. destruct a; simpl in Heqb0; try congruence. destr_in Heqb0.
    rewrite IHa; auto. f_equal. omega.
  Qed.

  Lemma label_pos_transf:
    forall c l o,
      label_pos l o c =
      label_pos l o (transf_code c).
  Proof.
    induction c; simpl; intros; eauto.
    unfold transf_code. simpl. fold (transf_code c).
    destr.
    - destruct a; simpl in Heqb; try congruence.
      destr_in Heqb. subst. simpl. rewrite peq_true. reflexivity.
    - rewrite label_pos_app.
      rewrite <- transf_instr_size. auto.
      intro IN.
      destruct a; try now (simpl in *; unfold Padd, Psub, Plea in *; simpl in *; repeat destr_in IN; try intuition congruence).
      simpl in *. destr_in Heqb.
      simpl in *. unfold Padd, Psub, Plea in *. simpl in *. repeat destr_in IN. intuition congruence.
      unfold Padd, Psub, Plea in *. repeat destr_in H. intuition congruence.
      unfold Padd, Psub, Plea in *. repeat destr_in H.
  Qed.
  
  Lemma goto_label_senv_equiv:
    forall f l rs m rs' m',
      goto_label ge f l rs m = Next rs' m' ->
      goto_label tge (transf_function f) l rs m = Next rs' m'.
  Proof.
    unfold goto_label.
    intros.
    simpl; rewrite <- label_pos_transf. destr.
    destr.
    destr_in H. inv H. erewrite functions_translated; eauto.
  Qed.

  Lemma functions_only_translated:
    forall b,
      Genv.find_funct_ptr ge b = None ->
      Genv.find_funct_ptr tge b = None.
  Proof.
    destruct TRANSF as (A & B & C).
    unfold Genv.find_funct_ptr, Genv.find_def.
    unfold ge, tge, Genv.globalenv.
    assert (REC:   forall b : block,
               match Maps.PTree.get b (Genv.genv_defs (Genv.empty_genv Asm.fundef unit (prog_public prog))) with
               | Some (Gfun f) => Some f
               | Some (Gvar _) => None
               | None => None
               end = None ->
               match Maps.PTree.get b (Genv.genv_defs (Genv.empty_genv Asm.fundef unit (prog_public tprog))) with
               | Some (Gfun f) => Some f
               | Some (Gvar _) => None
               | None => None
               end = None).
    {
      simpl. intros b; rewrite Maps.PTree.gempty. auto.
    }
    assert (NEXT: Genv.genv_next (Genv.empty_genv Asm.fundef unit (prog_public prog)) =
                  Genv.genv_next (Genv.empty_genv Asm.fundef unit (prog_public tprog))).
    {
      reflexivity.
    }
    revert REC NEXT.
    generalize (Genv.empty_genv Asm.fundef unit (prog_public prog)) (Genv.empty_genv Asm.fundef unit (prog_public tprog)).
    revert A.
    simpl.
    unfold Asm.fundef.
    generalize (@prog_defs (fundef function) unit prog) (@prog_defs (fundef function) unit tprog).
    induction 1; simpl. eauto.
    intros t t0 REC NEXT. apply IHA.
    simpl. intro b. inv H. inv H1. auto.
    rewrite ! Maps.PTree.gsspec.
    rewrite NEXT. destruct (peq b (Genv.genv_next t0)). inv H3. congruence. auto. auto.
    simpl. congruence.
  Qed.
  
  Lemma goto_label_senv_equiv':
    forall f l rs m,
      goto_label ge f l rs m = Stuck ->
      goto_label tge (transf_function f) l rs m = Stuck.
  Proof.
    unfold goto_label.
    intros.
    simpl; rewrite <- label_pos_transf. destr.
    destr.
    destr_in H. erewrite functions_only_translated; eauto.
  Qed.

  Lemma goto_label_eq:
    forall f l rs m,
      goto_label ge f l rs m =
      goto_label tge (transf_function f) l rs m.
  Proof.
    intros.
    destruct (goto_label ge f l rs m) eqn:GL.
    symmetry; eapply goto_label_senv_equiv; eauto.
    symmetry; eapply goto_label_senv_equiv'; eauto.
  Qed.

  Lemma eval_ros_eq:
    forall ros rs,
      eval_ros ge ros rs = eval_ros tge ros rs.
  Proof.
    unfold eval_ros.
    intros. destr.
    unfold Genv.symbol_address.
    destruct senv_preserved as (A & B & C & D). simpl in *; rewrite B. auto.
  Qed.
  
  Lemma exec_instr_senv_equiv:
    forall f i rs m (ID : id_instr i = true),
      exec_instr ge f i rs m = exec_instr tge (transf_function f) i rs m.
  Proof.
    generalize senv_preserved as EQ.
    destruct i; simpl; intros; eauto using exec_load_senv_equiv, exec_store_senv_equiv.
    unfold Genv.symbol_address.
    destruct EQ as (A & B & C & D). simpl in *. rewrite B. auto.
    erewrite eval_addrmode32_senv_equiv; eauto.
    erewrite eval_addrmode64_senv_equiv; eauto.
    eapply goto_label_eq; eauto.
    unfold Genv.find_funct.
    rewrite eval_ros_eq.
    destruct (eval_ros _ _ _) eqn:?; auto. destruct (Ptrofs.eq_dec _ _); auto.
    destr. erewrite functions_translated; eauto. erewrite functions_only_translated; eauto.
    destr. destr. eapply goto_label_eq; eauto.
    destr. destr. destr. destr. eapply goto_label_eq; eauto.
    destr. destr. eapply goto_label_eq; eauto.
    destr. f_equal. f_equal. f_equal. apply eval_ros_eq.
  Qed.
  
  Lemma pseudo_instructions_step:
    forall s1 t s2
           (STEP : step (Genv.globalenv prog) s1 t s2)
           (INV: real_asm_inv prog s1),
      plus step (Genv.globalenv tprog) s1 t s2.
  Proof.
    intros s1 t s2 STEP INV.
    inv STEP.
    - exploit functions_transl. eauto. intros FFP.
      exploit find_instr_transl; eauto. intro CA.
      destruct (id_instr i) eqn:ID; [| destruct i; simpl in ID; try congruence].
      + pose proof (id_instr_transf _ ID) as NORMAL.
        rewrite NORMAL in CA. inv CA.  inv H8. eapply plus_one.
        econstructor. eauto. eapply FFP. eauto.
        erewrite <- exec_instr_senv_equiv; eauto.
      + subst; simpl in *. inv H2. inv CA. inv H7. inv H9.
        eapply plus_two.
        econstructor. eauto. eapply FFP. eauto.
        unfold Padd. apply exec_instr_Plea.
        econstructor. rewrite Asmgenproof0.nextinstr_pc. repeat rewrite Pregmap.gso by congruence.
        rewrite H. simpl. eauto.
        eauto. erewrite wf_asm_pc_repr'; eauto.
        erewrite (instr_size_alloc sz pubrange ofs_ra RAX (align sz 8 - size_chunk Mptr)
                                   (linear_addr RSP (size_chunk Mptr)) RSP).
        generalize (instr_size_positive (Psub RSP RSP (align sz 8 - size_chunk Mptr))).
        generalize (instr_size_positive (Plea RAX (linear_addr RSP (size_chunk Mptr)))).
        omega.
        unfold Psub, Padd. rewrite exec_instr_Plea. f_equal.
        apply Axioms.extensionality. intro r.
        destruct (preg_eq r PC).
        * subst. simpl_regs. rewrite H. simpl. f_equal.
          generalize (wf_asm_pc_repr' _ (WF _ _ H0) _ _ H1). intro REPR.
          apply ptrofs_eq_unsigned. 
          rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_unsigned (Ptrofs.repr _)).
          erewrite Ptrofs.unsigned_repr by apply instr_size_repr.
          erewrite Ptrofs.unsigned_repr by apply instr_size_repr.
          repeat rewrite ! REPR.
          erewrite instr_size_alloc. unfold Psub, Padd; eauto.
          generalize (instr_size_positive (Pallocframe sz pubrange ofs_ra)); omega.
          setoid_rewrite <- (instr_size_alloc sz pubrange ofs_ra).
          generalize (instr_size_positive (Pallocframe sz pubrange ofs_ra)); omega.
        * simpl_regs. regs_eq. repeat rewrite Asmgenproof0.nextinstr_inv by auto.
          regs_eq. auto.
          apply eval_addrmode_offset_ptr. inv INV. edestruct RSPPTR as ( bb & oo & EQ & _); eauto.
          rewrite eval_addrmode_offset_ptr; simpl_regs.
          2: inv INV; edestruct RSPPTR as ( bb & oo & EQ & _); eauto.
          f_equal.
          unfold Ptrofs.neg. f_equal. f_equal.
          eapply wf_allocframe_repr; eauto.
        * traceEq.
      + subst; simpl in *. inv H2. inv CA. inv H7.
        eapply plus_one.
        econstructor. eauto. eapply FFP. eauto.
        unfold Padd. rewrite exec_instr_Plea.
        f_equal. apply Axioms.extensionality. intro r.
        erewrite (instr_size_free). unfold Padd.
        regs_eq. auto.
        rewrite eval_addrmode_offset_ptr.
        2: inv INV; edestruct RSPPTR as ( bb & oo & EQ & _); eauto.
        f_equal.
        eapply wf_freeframe_repr; eauto.
      + subst; simpl in *. inv H2. inv CA. inv H7.
        eapply plus_one.
        econstructor. eauto. eapply FFP. eauto.
        unfold Padd. rewrite exec_instr_Plea.
        f_equal. apply Axioms.extensionality. intro r.
        setoid_rewrite Pregmap.gsspec. destr. repeat rewrite Pregmap.gso by congruence.
        setoid_rewrite <- instr_size_load_parent_pointer. eauto.
        setoid_rewrite Pregmap.gsspec. destr.
        apply eval_addrmode_offset_ptr.
        inv INV. edestruct RSPPTR as ( bb & oo & EQ & _); eauto.
    - exploit functions_transl. eauto. intros FFP.
      exploit find_instr_transl; eauto. intro CA.
      apply plus_one.
      inv CA. inv H9.
      eapply exec_step_builtin; eauto.
      eapply eval_builtin_args_preserved. apply senv_preserved. eauto.
      eapply external_call_symbols_preserved. apply senv_preserved. eauto.
    - exploit functions_translated. eauto. intros FFP.
      apply plus_one.
      eapply exec_step_external; eauto.
      eapply external_call_symbols_preserved. apply senv_preserved. eauto.
  Qed.
  
  Theorem pseudo_instructions_correct rs:
    forward_simulation (RealAsm.semantics prog rs) (RealAsm.semantics tprog rs).
  Proof.
    eapply forward_simulation_plus with (match_states := fun s1 s2 : Asm.state => s1 = s2 /\ real_asm_inv prog s1).
    - simpl. apply public_preserved.
    - simpl; intros s1 IS1. inversion IS1.
      eapply Genv.init_mem_transf in H; eauto. eexists; split;[|split]; eauto.
      econstructor. eauto.
      inv H0. unfold rs0. unfold ge0.
      rewrite <- symbols_preserved in H1.
      erewrite <- (Linking.match_program_main) in H1 by eauto.
      econstructor; eauto.
      eapply real_initial_inv; eauto.
    - simpl; intros s1 s2 r (MS & INV) FS. subst. auto.
    - simpl. intros s1 t s2 STEP s1' (MS & INV). subst.
      eexists; split; [|split]; eauto.
      eapply pseudo_instructions_step; eauto.
      eapply real_asm_inv_inv; eauto.
  Qed.

       
End WITHMEMORYMODEL.
