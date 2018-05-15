Require Import Coqlib Integers AST Memdata Maps StackADT.
Require Import Asm Asmgen RealAsm.
Require Import Errors.
Require Import Memtype.
Import ListNotations.

Local Open Scope error_monad_scope.
Close Scope nat_scope.

Definition linear_addr reg ofs := 
  Addrmode (Some reg) None (inl ofs).

Definition Plea := if Archi.ptr64 then Pleaq else Pleal.
Definition Padd dst src z := Plea dst (linear_addr src z).
Definition Psub dst src z := Padd dst src (- z).

Definition transf_instr (i: instruction): list instruction :=
  match i with
  | Pallocframe sz pubrange ofs_ra =>
    let sz := align sz 8 - size_chunk Mptr in
    let addr1 := linear_addr RSP (size_chunk Mptr) in
    [ Padd RAX RSP (size_chunk Mptr); Psub RSP RSP sz ]
  | Pfreeframe fsz ofs_ra =>
    let sz := align fsz 8 - size_chunk Mptr in
    [ Padd RSP RSP sz ]
  | Pload_parent_pointer rd z =>
    [ Padd rd RSP (align (Z.max 0 z) 8) ]
  | _ => [ i ]
  end.

Definition transf_code (c: code) : code :=
  concat (map transf_instr c).

Definition transf_function (f: function) : function :=
  {|
    fn_sig := fn_sig f;
    fn_code := transf_code (fn_code f);
    fn_stacksize := fn_stacksize f;
    fn_pubrange := fn_pubrange f;
  |}.

Definition transf_fundef := AST.transf_fundef transf_function.

Definition transf_program (p: Asm.program) : Asm.program :=
  AST.transform_program transf_fundef p.

Definition check_function (f: Asm.function) : bool :=
  wf_asm_function_check f && AsmFacts.check_asm_code_no_rsp (fn_code f).

Definition transf_check_function f := if check_function f then OK f else Error nil.

Definition transf_check_fundef :=
  AST.transf_partial_fundef (transf_check_function).

Require Import Globalenvs.

(* Definition has_main (p: program) := *)
(*   let ge := Genv.globalenv p in *)
(*   match Genv.find_symbol ge (prog_main p) with *)
(*   | Some b => *)
(*     match Genv.find_funct_ptr ge b with *)
(*     | Some (Internal f) => true *)
(*     | _ => false *)
(*     end *)
(*   | _ => false *)
(*   end. *)

Definition check_program p : res (Asm.program) :=
  (* if has_main p *)
  (* then *) AST.transform_partial_program transf_check_fundef p
  (* else Error (msg "no main function in program") *).

Theorem check_program_id:
  forall p1 p2,
    check_program p1 = OK p2 -> p1 = p2.
Proof.
  unfold check_program.
  unfold transform_partial_program.
  unfold transform_partial_program2.
  intros. monadInv H. destruct p1. simpl in *. f_equal.
  revert EQ.
  unfold transf_check_fundef, transf_partial_fundef, transf_check_function.
  revert x; induction prog_defs; simpl; intros; eauto. inv EQ; auto.
  destr_in EQ.
  repeat destr_in EQ; repeat destr_in Heqr; monadInv H0.
  - f_equal. eauto.
  - f_equal. eauto.
  - f_equal; eauto. f_equal. f_equal. f_equal. destruct v; simpl. f_equal.
  - f_equal. eauto.
Qed.

Definition match_check_prog (p: Asm.program) (tp: Asm.program) :=
  Linking.match_program (fun _ f tf => transf_check_fundef f = OK tf) eq p tp (* /\ *)
  (* exists (bmain : Values.block) (fmain : Asm.function), *)
  (*   Globalenvs.Genv.find_symbol (Globalenvs.Genv.globalenv p) (prog_main p) = Some bmain /\ *)
  (*   Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p) bmain = Some (Internal fmain) *).

Lemma check_program_match:
  forall p tp, check_program p = OK tp -> match_check_prog p tp.
Proof.
  intros. unfold check_program in H. destr_in H.
  eapply Linking.match_transform_partial_program; eauto.
Qed.

Theorem check_wf:
  forall p tp,
    match_check_prog p tp ->
    RealAsm.wf_asm_prog (Globalenvs.Genv.globalenv p).
Proof.
  red.
  intros.
  destruct H as (A & B & C).
  eapply Globalenvs.Genv.find_funct_ptr_prop with (P := fun f => match f with Internal f => _ f | _ => True end) in H0.
  apply H0.
  intros. edestruct list_forall2_in_left as (v2 & IN2 & P2); eauto.
  inv P2. simpl in *. subst. inv H2. inv H4.
  destr. simpl in H5. monadInv H5.
  unfold transf_check_function in EQ. repeat destr_in EQ.
  unfold check_function in Heqb0.
  apply andb_true_iff in Heqb0; destruct Heqb0.
  eapply wf_asm_function_check_correct; eauto.
Qed.

Theorem check_no_rsp:
  forall p tp,
    match_check_prog p tp ->
    forall b f,
      Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p) b = Some (Internal f) ->
      AsmFacts.check_asm_code_no_rsp (fn_code f) = true.
Proof.
  intros.
  destruct H as (A & B & C).
  eapply Globalenvs.Genv.find_funct_ptr_prop with (P := fun f => match f with Internal f => _ f | _ => True end) in H0.
  pattern f.
  apply H0.
  simpl. intros. edestruct list_forall2_in_left as (v2 & IN2 & P2); eauto.
  inv P2. simpl in *. subst. inv H2. inv H4.
  destr. simpl in H5. monadInv H5.
  unfold transf_check_function in EQ. repeat destr_in EQ.
  unfold check_function in Heqb0.
  apply andb_true_iff in Heqb0; destruct Heqb0; auto.
Qed.

Section CHECKSIMU.
  Require Import Events Globalenvs Smallstep.

  Context `{memory_model: Mem.MemoryModel }.
  Existing Instance inject_perm_upto_writable.

  Context `{external_calls_ops : !ExternalCallsOps mem }.
  Context `{!EnableBuiltins mem}.

  Existing Instance mem_accessors_default.
  Existing Instance symbols_inject_instance.
  Context `{external_calls_props : !ExternalCallsProps mem
                                    (memory_model_ops := memory_model_ops)
           }.

  Variable rs: regset.
  Variables p tp: program.

  Hypothesis TRANSF: match_check_prog p tp.

  Let ge := Genv.globalenv p.
  Let tge := Genv.globalenv tp.

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
    forall v f,
      Genv.find_funct ge v = Some f ->
      exists tf,
        Genv.find_funct tge v = Some tf /\ transf_check_fundef f = OK tf.
  Proof (Genv.find_funct_transf_partial TRANSF).

  Lemma function_ptr_translated:
    forall b f,
      Genv.find_funct_ptr ge b = Some f ->
      exists tf,
        Genv.find_funct_ptr tge b = Some tf /\ transf_check_fundef f = OK tf.
  Proof (Genv.find_funct_ptr_transf_partial TRANSF).



Lemma globalenv_eq:
  ge = tge.
Proof.
  unfold ge, tge.
  unfold Genv.globalenv.
  destruct TRANSF as (A & B & C).
  setoid_rewrite C.
  fold fundef.
  generalize (Genv.empty_genv fundef unit (prog_public p)).
  revert A.
  fold fundef.
  generalize (prog_defs p) (prog_defs tp).
  induction 1; simpl; intros; eauto.
  inv H. destruct a1, b1; simpl in *. subst. inv H1.
  apply IHA.
  inv H. unfold transf_check_fundef, transf_partial_fundef in H1.
  repeat destr_in H1. unfold bind in H2. destr_in H2. inv H2.
  unfold transf_check_function in Heqr. repeat destr_in Heqr.
  inv H0. apply IHA.
Qed.

Lemma transf_initial_states:
  forall s,
    RealAsm.initial_state p rs s ->
    RealAsm.initial_state tp rs s.
Proof.
  intros. inv H.
  exploit (Genv.init_mem_transf_partial TRANSF). eauto. intro TINIT.
  econstructor. eauto.
  inv H1.
  unfold rs0, ge0.
  econstructor; eauto.
  setoid_rewrite (Linking.match_program_main TRANSF).
  rewrite symbols_preserved. eauto.
Qed.

  Theorem check_simulation:
    forward_simulation (RealAsm.semantics p rs) (RealAsm.semantics tp rs).
  Proof.
    unfold match_check_prog.
    eapply forward_simulation_step with (match_states := fun s1 s2 : Asm.state => s1 = s2).
    - simpl. apply senv_preserved.
    - simpl; intros. eexists; split. eapply transf_initial_states; eauto. auto.
    - simpl; intros. subst. inv H0. econstructor; eauto.
    - simpl; intros; subst. fold tge. fold ge in H. rewrite <- globalenv_eq.
      eexists; split; eauto.
  Qed.

End CHECKSIMU.
