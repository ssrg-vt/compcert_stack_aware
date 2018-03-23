
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Stacklayout.
Require Import Mach.
Require Import Mach2.

Section WITHEXTCALLS.
  Context `{external_calls: ExternalCalls}.

Section WITHINITSP.
  Variables init_sp init_ra: val.
  Variable return_address_offset: function -> code -> ptrofs -> Prop.
  Variable ge: genv.

  Definition same_head (m m': stack_adt) :=
    list_forall2
      (fun tf1 tf2 =>
         match tf1, tf2 with
           a::r, b::nil => a = b
         | _, _ => False
         end)
      m m'.

  Inductive match_states : state -> state -> Prop :=
  | match_states_regular s f sp c rs m m'
                         (UNCH: Mem.unchanged_on (fun _ _ => True) m m')
                         (SH: same_head (Mem.stack_adt m) (Mem.stack_adt m'))
                         (NB: Mem.nextblock m = Mem.nextblock m'):
      match_states (State s f sp c rs m) (State s f sp c rs m')
  | match_states_call s fb rs m m'
                      (UNCH: Mem.unchanged_on (fun _ _ => True) m m')
                      (SH: same_head (tl (Mem.stack_adt m)) (tl (Mem.stack_adt m')))
                      (LEN: length (Mem.stack_adt m) = length (Mem.stack_adt m'))
                      (NB: Mem.nextblock m = Mem.nextblock m'):
      match_states (Callstate s fb rs m) (Callstate s fb rs m')
  | match_states_return s rs m m'
                        (UNCH: Mem.unchanged_on (fun _ _ => True) m m')
                        (SH: same_head (tl (Mem.stack_adt m)) (tl (Mem.stack_adt m')))
                        (LEN: length (Mem.stack_adt m) = length (Mem.stack_adt m'))
                        (NB: Mem.nextblock m = Mem.nextblock m'):
      match_states (Returnstate s rs m) (Returnstate s rs m').

  Lemma loadv_unchanged_on:
    forall P m m' chunk addr v
      (UNCH: Mem.unchanged_on P m m')
      (RNG: forall b ofs i, addr = Vptr b ofs -> Ptrofs.unsigned ofs <= i < Ptrofs.unsigned ofs + size_chunk chunk -> P b i)
      (LOADV: Mem.loadv chunk m addr = Some v),
      Mem.loadv chunk m' addr = Some v.
  Proof.
    intros.
    destruct addr; simpl in *; try congruence.
    eapply Mem.load_unchanged_on; eauto.
  Qed.

  Lemma loadstack_unchanged_on:
    forall P m m' sp ty ofs v
      (UNCH: Mem.unchanged_on P m m')
      (RNG: forall b o i, Val.offset_ptr sp ofs = Vptr b o -> Ptrofs.unsigned o <= i < Ptrofs.unsigned o + size_chunk (chunk_of_type ty) -> P b i)
      (LOADSTACK: load_stack m sp ty ofs = Some v),
      load_stack m' sp ty ofs = Some v.
  Proof.
    intros.
    eapply loadv_unchanged_on; eauto.
  Qed.

  Axiom store_unchanged_on_1:
    forall P chunk m m' b ofs v m1
      (UNCH: Mem.unchanged_on P m m')
      (SH: same_head (Mem.stack_adt m) (Mem.stack_adt m') \/ ~ in_stack (Mem.stack_adt m') b)
      (PERMALL: forall b o, P b o)
      (STORE: Mem.store chunk m b ofs v = Some m1),
    exists m1',
      Mem.store chunk m' b ofs v = Some m1' /\ Mem.unchanged_on P m1 m1'.

  Lemma storev_unchanged_on_1:
    forall P chunk m m' addr v m1
      (UNCH: Mem.unchanged_on P m m')
      (SH: same_head (Mem.stack_adt m) (Mem.stack_adt m')
           \/ forall b o, addr = Vptr b o -> ~ in_stack (Mem.stack_adt m') b
      )
      (PERMALL: forall b o, P b o)
      (STORE: Mem.storev chunk m addr v = Some m1),
    exists m1',
      Mem.storev chunk m' addr v = Some m1' /\ Mem.unchanged_on P m1 m1'.
  Proof.
    destruct addr; simpl; intros; try congruence.
    eapply store_unchanged_on_1; eauto.
    destruct SH; [left|right]; auto.
    eapply H; eauto.
  Qed.

  Lemma storestack_unchanged_on:
    forall P m m' sp ty ofs v m1
      (SH: same_head (Mem.stack_adt m) (Mem.stack_adt m') \/ forall b o, sp = Vptr b o -> ~ in_stack (Mem.stack_adt m') b)
      (UNCH: Mem.unchanged_on P m m')
      (Ptrue: forall b o, P b o)
      (STORESTACK: store_stack m sp ty ofs v = Some m1),
    exists m1',
      store_stack m' sp ty ofs v = Some m1' /\ Mem.unchanged_on P m1 m1'.
  Proof.
    intros.
    unfold store_stack in *.
    eapply storev_unchanged_on_1; eauto.
    destruct SH;[left|right]; auto. intros; destruct sp; simpl in *; try congruence. inv H0. eapply H; eauto.
  Qed.

  Axiom valid_pointer_unchanged:
  forall m1 m2,
    Mem.unchanged_on (fun _ _ => True) m1 m2 ->
    Mem.nextblock m1 = Mem.nextblock m2 ->
    Mem.valid_pointer m1 = Mem.valid_pointer m2.

  Lemma eval_condition_unchanged:
    forall cond args m1 m2,
      Mem.unchanged_on (fun _ _ => True) m1 m2 ->
      Mem.nextblock m1 = Mem.nextblock m2 ->
      eval_condition cond args m1 = eval_condition cond args m2.
  Proof.
    intros.
    generalize (valid_pointer_unchanged _ _ H H0). intro VP.
    unfold eval_condition.
    repeat destr.
  Qed.


  Lemma eval_operation_unchanged:
    forall sp op args m1 m2,
      Mem.unchanged_on (fun _ _ => True) m1 m2 ->
      Mem.nextblock m1 = Mem.nextblock m2 ->
      eval_operation ge sp op args m1 = eval_operation ge sp op args m2.
  Proof.
    intros.
    destruct (op_depends_on_memory op) eqn:?.
    destruct op; simpl in *; try congruence.
    f_equal. f_equal. apply eval_condition_unchanged; auto.
    apply op_depends_on_memory_correct. auto.
  Qed.

  Axiom push_new_stage_strong_unchanged_on:
    forall m1 m2 P,
      Mem.unchanged_on P m1 m2 ->
      Mem.unchanged_on P (Mem.push_new_stage m1) (Mem.push_new_stage m2).

  Axiom unchanged_on_free:
    forall m1 m2,
      Mem.unchanged_on (fun _ _ => True) m1 m2 ->
      forall b lo hi m1',
        Mem.free m1 b lo hi = Some m1' ->
        exists m2',
          Mem.free m2 b lo hi = Some m2' /\ Mem.unchanged_on (fun _ _ => True) m1' m2'.

  Axiom unchanged_on_unrecord:
    forall m1 m2,
      Mem.unchanged_on (fun _ _ => True) m1 m2 ->
      forall m1',
        Mem.unrecord_stack_block m1 = Some m1' ->
        exists m2',
          Mem.unrecord_stack_block m2 = Some m2' /\ Mem.unchanged_on (fun _ _ => True) m1' m2'.

  Axiom unchanged_on_record:
    forall m1 m2,
      Mem.unchanged_on (fun _ _ => True) m1 m2 ->
      forall m1' fi,
        Mem.record_stack_blocks m1 fi = Some m1' ->
        exists m2',
          Mem.record_stack_blocks m2 fi = Some m2' /\ Mem.unchanged_on (fun _ _ => True) m1' m2'.

  
  Axiom unchanged_on_extcall:
    forall m1 m2,
      Mem.unchanged_on (fun _ _ => True) m1 m2 ->
      Mem.nextblock m1 = Mem.nextblock m2 ->
      forall ef args res t m1',
        external_call ef ge args m1 res t m1' ->
        exists m2',
          external_call ef ge args m2 res t m2' /\ Mem.unchanged_on (fun _ _ => True) m1' m2' /\
          Mem.nextblock m1' = Mem.nextblock m2'.


  Lemma unchanged_on_builtin_arg:
    forall {A} m1 m2 (e: A -> val) sp arg varg,
      Mem.unchanged_on (fun _ _ => True) m1 m2 ->
      eval_builtin_arg ge e sp m1 arg varg ->
      eval_builtin_arg ge e sp m2 arg varg.
  Proof.
    induction 2; constructor; auto.
    eapply loadv_unchanged_on; eauto. simpl; auto.
    eapply loadv_unchanged_on; eauto. simpl; auto.
  Qed.

  Lemma unchanged_on_builtin_args:
    forall {A} m1 m2 (e: A -> val) sp args vargs,
      Mem.unchanged_on (fun _ _ => True) m1 m2 ->
      eval_builtin_args ge e sp m1 args vargs ->
      eval_builtin_args ge e sp m2 args vargs.
  Proof.
    induction 2; constructor; eauto using unchanged_on_builtin_arg.
  Qed.

  Lemma unchanged_on_extcall_arg:
    forall m1 m2 rs sp l v,
      Mem.unchanged_on (fun _ _ => True) m1 m2 ->
      extcall_arg rs m1 sp l v ->
      extcall_arg rs m2 sp l v.
  Proof.
    inversion 2; constructor; auto.
    eapply loadstack_unchanged_on; eauto. simpl; auto.
  Qed.
  
  Lemma unchanged_on_extcall_arg_pair:
    forall m1 m2 rs sp l v,
      Mem.unchanged_on (fun _ _ => True) m1 m2 ->
      extcall_arg_pair rs m1 sp l v ->
      extcall_arg_pair rs m2 sp l v.
  Proof.
    induction 2; simpl; intros; econstructor; eauto using unchanged_on_extcall_arg.
  Qed.
  
  Lemma unchanged_on_extcall_args:
    forall m1 m2 rs sp sg vargs,
      Mem.unchanged_on (fun _ _ => True) m1 m2 ->
      extcall_arguments rs m1 sp sg vargs ->
      extcall_arguments rs m2 sp sg vargs.
  Proof.
    unfold extcall_arguments.
    induction 2. constructor. constructor; eauto using unchanged_on_extcall_arg_pair.
  Qed.

  Axiom unrecord_push:
    forall m1 m2 m2',
      Mem.unchanged_on (fun _ _ => True) m1 m2 ->
      Mem.unrecord_stack_block m2 = Some m2' ->
      Mem.unchanged_on (fun _ _ => True) m1 (Mem.push_new_stage m2').

  Lemma clear_stage_unchanged:
    forall m1 m2,
      Mem.unchanged_on (fun _ _  => True) m1 m2 ->
      length (Mem.stack_adt m2) <> O ->
      exists m2',
        Mem.clear_stage m2 = Some m2' /\ Mem.unchanged_on (fun _ _ => True) m1 m2'.
  Proof.
    unfold Mem.clear_stage. intros.
    destruct (Mem.stack_adt m2) eqn:?; simpl in *. omega. clear H0.
    edestruct (Mem.unrecord_stack_block_succeeds m2) as (m3 & USB & EQSTK); eauto.
    rewrite USB. subst. eexists; split; eauto.
    eapply unrecord_push; eauto.
  Qed.

  Lemma step_correct:
    forall S1 t S2 (STEP: Mach.step init_sp init_ra return_address_offset ge S1 t S2)
      S1' (MS: match_states S1 S1') (CSC: call_stack_consistency init_sp ge S1'),
    exists S2',
      Mach2.step init_sp init_ra return_address_offset ge S1' t S2' /\ match_states S2 S2'.
  Proof.
    destruct 1; intros S1' MS CSC; inv MS.
    - eexists; split. econstructor; eauto.
      constructor; auto.
    - eexists; split. econstructor; eauto. eapply loadstack_unchanged_on; simpl; eauto. simpl. auto.
      constructor; auto.
    - edestruct storestack_unchanged_on as (m1' & STORE' & UNCH'); eauto. simpl; auto.
      eexists; split. econstructor; eauto.
      constructor; auto. unfold store_stack in *. repeat rewrite_stack_blocks. auto.
      unfold store_stack in *. rewnb; auto.
    - eexists; split. econstructor; eauto. eapply loadstack_unchanged_on; simpl; eauto. simpl. auto.
      constructor; auto.
    - erewrite eval_operation_unchanged in H; eauto.
      eexists; split; econstructor; eauto.
    - eexists; split; econstructor; eauto. eapply loadv_unchanged_on; eauto. simpl; auto.
    - edestruct storev_unchanged_on_1 as (m1' & STORE' & UNCH'); eauto. simpl; auto.
      eexists; split; econstructor; eauto.
      repeat rewrite_stack_blocks. auto.
      rewnb; auto.
    - eexists; split; econstructor; eauto.
      apply push_new_stage_strong_unchanged_on. auto.
      repeat rewrite_stack_blocks. simpl; auto.
      repeat rewrite_stack_blocks. apply list_forall2_length in SH. simpl. setoid_rewrite SH.
      reflexivity.
      rewnb. auto.
    - edestruct unchanged_on_free as (m2' & FREE' & UNCH'); eauto.
      inv CSC. rewrite FIND in H0; inv H0.
      edestruct (clear_stage_unchanged _ _ UNCH') as (m3' & USB & UNCH'').
      rewrite_stack_blocks. inv CallStackConsistency. simpl; omega.
      eexists; split; econstructor; eauto. eapply loadstack_unchanged_on; eauto. simpl; auto.
      repeat rewrite_stack_blocks; auto. simpl. inv SH; simpl; auto. constructor.
      repeat rewrite_stack_blocks. simpl. apply list_forall2_length in SH. simpl. setoid_rewrite SH.
      inv CallStackConsistency. simpl. auto.
      rewnb. auto.
    - edestruct unchanged_on_extcall as (m2' & EXTCALL & UNCH' & NB').  3: eauto.
      apply push_new_stage_strong_unchanged_on. eauto.
      rewnb. auto.
      edestruct unchanged_on_unrecord as (m3' & USB & UNCH''). apply UNCH'. eauto.
      eexists; split; econstructor; eauto.
      eapply unchanged_on_builtin_args; eauto.
      repeat rewrite_stack_blocks; eauto.
      rewnb; auto.
    - eexists; split; econstructor; eauto.
    - eexists; split; econstructor; eauto.
      erewrite <- eval_condition_unchanged; eauto.
    - eexists; split. eapply Mach2.exec_Mcond_false; eauto.
      erewrite <- eval_condition_unchanged; eauto.
      econstructor; eauto.
    - eexists; split; econstructor; eauto.
    - edestruct unchanged_on_free as (m2' & FREE' & UNCH'); eauto.
      inv CSC. rewrite FIND in H; inv H.
      edestruct (clear_stage_unchanged _ _ UNCH') as (m3' & USB & UNCH'').
      rewrite_stack_blocks. inv CallStackConsistency. simpl; omega.
      eexists; split; econstructor; eauto. eapply loadstack_unchanged_on; eauto. simpl; auto.
      repeat rewrite_stack_blocks; auto. simpl. inv SH; simpl; auto. constructor.
      repeat rewrite_stack_blocks. simpl. apply list_forall2_length in SH. simpl. setoid_rewrite SH.
      inv CallStackConsistency. simpl. auto.
      rewnb. auto.
    - destruct (Mem.alloc m' 0 (fn_stacksize f)) as (m1' & stk') eqn:ALLOC.
      assert (stk = stk').
      apply Mem.alloc_result in ALLOC.
      apply Mem.alloc_result in H1. congruence. subst.

      Axiom unchanged_on_alloc:
        forall m1 m2 (UNCH: Mem.unchanged_on (fun _ _ => True) m1 m2)
          lo hi m1' b (ALLOC1: Mem.alloc m1 lo hi = (m1', b))
          m2' (ALLOC2: Mem.alloc m2 lo hi = (m2', b)),
          Mem.unchanged_on (fun _ _ => True) m1' m2'.
      generalize (unchanged_on_alloc _ _ UNCH _ _ _ _ H1 _ ALLOC). intro UNCH1.
      edestruct (fun SH => storestack_unchanged_on _ _ _ _ _ _ _ _ SH UNCH1 (fun _ _ => I) H2) as (m3' & STORE & UNCH2).
      repeat rewrite_stack_blocks. right; intro; subst. inversion 1; subst.
      intro INS. subst. eapply Mem.fresh_block_alloc; eauto. eapply Mem.in_frames_valid; eauto.

      (* edestruct (clear_stage_unchanged _ _ UNCH2) as (m4' & USB & UNCH3).  *)
      (* unfold store_stack in *. repeat rewrite_stack_blocks. *)
      (* edestruct (Mem.record_stack_blocks_tailcall_original_stack _ _ _ H3) as (ff & r & EQSTK). *)
      (* revert EQSTK; repeat rewrite_stack_blocks. intro. *)
      (* rewrite EQSTK in LEN. simpl in *. intro ISZERO; omega. *)
      edestruct (unchanged_on_record _ _ UNCH2 _ _ H3) as (m5' & RSB & UNCH4).

      eexists; split; econstructor; eauto.

      unfold store_stack in *; repeat rewrite_stack_blocks.
      revert EQ1 EQ0; repeat rewrite_stack_blocks. intros A B; rewrite A, B in SH. simpl in SH.
      constructor; auto. inv CSC. red in TIN. rewrite B in TIN. inv TIN. reflexivity.
      unfold store_stack in *; rewnb. congruence.
    - edestruct unchanged_on_extcall as (m2' & EXTCALL & UNCH' & NB').  3: eauto.
      eauto. auto.
      eexists; split; econstructor; eauto.
      eapply unchanged_on_extcall_args; eauto.
      repeat rewrite_stack_blocks; eauto.
      repeat rewrite_stack_blocks; eauto.
    - edestruct unchanged_on_unrecord as (m1' & USB & UNCH''). apply UNCH. eauto.
      eexists; split; econstructor; eauto.
      repeat rewrite_stack_blocks; eauto.
      rewnb; auto.
  Qed.

End WITHINITSP.
  Existing Instance inject_perm_all.

  Lemma initial_transf:
    forall p s, initial_state p s -> match_states s s.
  Proof.
    intros p s IS. inv IS.
    constructor; try reflexivity.
    - apply Mem.unchanged_on_refl.
    - repeat rewrite_stack_blocks. simpl.
      constructor; auto. constructor.
  Qed.


  Lemma final_transf:
    forall s1 s2 i, match_states s1 s2 -> final_state s1 i -> final_state s2 i.
  Proof.
    intros s1 s2 i MS FS; inv FS; inv MS. econstructor; eauto.
  Qed.

  Lemma mach2_simulation:
    forall rao p,
      (forall (fb : block) (f : function),
          Genv.find_funct_ptr (Genv.globalenv p) fb = Some (Internal f) ->
          frame_size (fn_frame f) = fn_stacksize f) ->
      forward_simulation (Mach.semantics rao p) (Mach2.semantics rao p).
  Proof.
    intros rao p SIZE.
    set (ge := Genv.globalenv p).
    eapply forward_simulation_step with (match_states := fun s1 s2 => match_states s1 s2 /\ call_stack_consistency (Vptr (Genv.genv_next ge) Ptrofs.zero) ge s2).
    - reflexivity.
    - simpl; intros s1 IS. eexists; split; eauto. split. eapply initial_transf; eauto.
      inv IS. constructor. simpl. constructor. split. inversion 1. subst.
      repeat rewrite_stack_blocks.  simpl. repeat eexists.
      apply Mem.alloc_result in H1. subst. apply Genv.init_mem_genv_next in H. rewrite <- H.
      fold ge. reflexivity.
      intros (fsp & fr & r & EQ & GFB).
      revert EQ. repeat rewrite_stack_blocks. simpl. inversion 1. subst. f_equal.
      unfold ge. erewrite Genv.init_mem_genv_next; eauto.
      symmetry. eapply Mem.alloc_result; eauto. inv GFB. eauto.
      repeat rewrite_stack_blocks. simpl. repeat constructor.
      red. rewrite_stack_blocks. constructor; auto.
      constructor.
    - simpl. intros s1 s2 r (MS & CSC). eapply final_transf; eauto.
    - simpl; intros s1 t s1' STEP s2 (MS & CSC).
      edestruct step_correct as (s2' & STEP' & MS'); eauto.
      eexists; split; eauto. split; auto. eapply csc_step; eauto.
  Qed.

End WITHEXTCALLS.