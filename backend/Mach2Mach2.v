
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

Section WITHEXTCALLS.
  Context `{external_calls: ExternalCalls}.

Section WITHINITSP.
  Variables init_ra: val.
  Variable return_address_offset: function -> code -> ptrofs -> Prop.
  Variable prog: program.
  Let ge:= Genv.globalenv prog.

  Existing Instance inject_perm_all.

  Definition stack_equiv s1 s2 :=
    list_forall2 (fun tf1 tf2 => size_frames tf1 = size_frames tf2) s1 s2.
  
  Inductive match_states : state -> state -> Prop :=
  | match_states_regular s f sp c rs rs' m m'
                         (MLD: Mem.extends m m')
                         (RLD: forall r, Val.lessdef (rs r) (rs' r))
                         (SE: stack_equiv (Mem.stack m) (Mem.stack m')):
      match_states (State s f sp c rs m) (State s f sp c rs' m')
  | match_states_call s fb rs rs' m m'
                      (MLD: Mem.extends m m')
                      (RLD: forall r, Val.lessdef (rs r) (rs' r))
                      (SE: stack_equiv (Mem.stack m) (Mem.stack m')):
      match_states (Callstate s fb rs m) (Callstate s fb rs' m')
  | match_states_return s rs rs' m m'
                        (MLD: Mem.extends m m')
                        (RLD: forall r, Val.lessdef (rs r) (rs' r))
                        (SE: stack_equiv (Mem.stack m) (Mem.stack m')):
      match_states (Returnstate s rs m) (Returnstate s rs' m').

  Variable init_sg: signature.
  Variable init_stk: stack.

  Lemma parent_sp_same_tl:
    forall s1 s2 cs
           (LP1: Mach.list_prefix init_sg init_stk cs (tl s1)) (LP2: list_prefix init_sg init_stk cs (tl s2)) (LEN: length s1 = length s2),
      parent_sp s1 = parent_sp s2.
  Proof.
    intros. destruct s1; destruct s2; simpl in LEN; try omega. auto. simpl in *.
    inv LP1; inv LP2.
    auto.
    simpl.
    unfold current_frame_sp. simpl. rewrite BLOCKS, BLOCKS0. auto.
  Qed.

  Lemma list_prefix_length:
    forall cs s,
      Mach.list_prefix init_sg init_stk cs s ->
      length s = (length init_stk + length cs)%nat.
  Proof.
    induction 1; simpl; intros; eauto. subst; omega.
    rewrite IHlist_prefix. omega.
  Qed.

  Lemma parent_sp_same:
    forall s1 s2 cs
           (LP1: list_prefix init_sg init_stk cs s1) (LP2: list_prefix init_sg init_stk cs s2),
      parent_sp s1 = parent_sp s2.
  Proof.
    intros.
    inv LP1; inv LP2. auto.
    eapply parent_sp_same_tl; simpl; eauto. f_equal.
    apply list_prefix_length in REC0.
    apply list_prefix_length in REC.
    congruence.
  Qed.

  Lemma zle_zlt_false:
    forall lo hi o,
      zle lo o && zlt o hi = false <-> ~ (lo <= o < hi)%Z.
  Proof.
    intros.
    destruct (zle lo o), (zlt o hi); intuition; try congruence; try omega.
  Qed.

  Hypothesis frame_correct:
    forall (fb : block) (f : function),
      Genv.find_funct_ptr (Genv.globalenv prog) fb = Some (Internal f) ->
      0 < fn_stacksize f.

  Lemma lessdef_set_reg:
    forall rs rs'
      (RLD : forall r : RegEq.t, Val.lessdef (rs r) (rs' r))
      v v' (LD: Val.lessdef v v') dst r,
      Val.lessdef (rs # dst <- v r) (rs' # dst <- v' r).
  Proof.
    intros; setoid_rewrite Regmap.gsspec. destr. apply RLD.
  Qed.

  Lemma lessdef_set_res:
    forall res rs rs'
      (RLD : forall r : RegEq.t, Val.lessdef (rs r) (rs' r))
      v v' (LD: Val.lessdef v v') r,
      Val.lessdef (set_res res v rs r)
                  (set_res res v' rs' r).
  Proof.
    induction res; simpl; intros; eauto.
    apply lessdef_set_reg; auto.
    eapply IHres2; eauto. eapply IHres1; eauto.
    apply Val.hiword_lessdef; auto.
    apply Val.loword_lessdef; auto.
  Qed.

  Lemma lessdef_set_pair:
    forall pair rs rs'
      (RLD : forall r : RegEq.t, Val.lessdef (rs r) (rs' r))
      v v' (LD: Val.lessdef v v') r,
      Val.lessdef (set_pair pair v rs r)
                  (set_pair pair v' rs' r).
  Proof.
    destruct pair; simpl; intros; eauto;
      repeat apply lessdef_set_reg; auto.
    apply Val.hiword_lessdef; auto.
    apply Val.loword_lessdef; auto.
  Qed.
  
  Lemma lessdef_undef_regs:
    forall rs rs'
      (RLD : forall r : RegEq.t, Val.lessdef (rs r) (rs' r))
      l r,
      Val.lessdef (undef_regs l rs r) (undef_regs l rs' r).
  Proof.
    induction l; simpl; intros. auto.
    apply lessdef_set_reg; auto.
  Qed.

  Lemma lessdef_args:
    forall rs rs'
      (RLD : forall r : RegEq.t, Val.lessdef (rs r) (rs' r))
      l,
      Val.lessdef_list (rs ## l) (rs' ## l).
  Proof.
    induction l; simpl; intros; auto.
  Qed.

  Lemma find_function_ptr_lessdef:
    forall ge ros b rs rs'
      (RLD : forall r : RegEq.t, Val.lessdef (rs r) (rs' r))
      (FFP: find_function_ptr ge ros rs = Some b),
      find_function_ptr ge ros rs' = Some b.
  Proof.
    unfold find_function_ptr; simpl; intros.
    repeat destr_in FFP.
    specialize (RLD m); rewrite Heqv in RLD; inv RLD. rewrite Heqb1. auto.
  Qed.


Section EXTERNAL_ARGUMENTS.

  Variables rs rs': regset.
  Hypothesis RLD: forall r : RegEq.t, Val.lessdef (rs r) (rs' r).
  Variables m m' : mem.
  Hypothesis MLD: Mem.extends m m'.
  Variable sp: val.
  
  Lemma extcall_arg_ld:
    forall l v,
      extcall_arg rs m sp l v ->
      exists v',
        extcall_arg rs' m' sp l v' /\ Val.lessdef v v'.
  Proof.
    intros l v EA. inv EA.
    eexists; split. econstructor. eauto.
    unfold load_stack in H.
    edestruct Mem.loadv_extends as (v2 & LOAD & LD); eauto.
    eexists; split. econstructor. unfold load_stack; eauto. auto.
  Qed.

  Lemma extcall_arg_pair_ld:
    forall l v,
      extcall_arg_pair rs m sp l v ->
      exists v',
        extcall_arg_pair rs' m' sp l v' /\ Val.lessdef v v'.
  Proof.
    intros l v EA. inv EA.
    edestruct extcall_arg_ld as (v' & EA' & LD); eauto. eexists; split. econstructor; eauto. eauto.
    edestruct (extcall_arg_ld hi) as (vhi' & EAhi & LDhi); eauto.
    edestruct (extcall_arg_ld lo) as (vlo' & EAlo & LDlo); eauto.
    eexists; split. econstructor; eauto.
    apply Val.longofwords_lessdef; auto.
  Qed.

  Lemma extcall_arguments_ld:
    forall sg v,
      extcall_arguments rs m sp sg v ->
      exists v',
        extcall_arguments rs' m' sp sg v' /\ Val.lessdef_list v v'.
  Proof.
    unfold extcall_arguments.
    induction 1.
    exists nil; split; eauto. constructor.
    destruct IHlist_forall2 as (v' & LF2 & LDL).
    edestruct (extcall_arg_pair_ld a1) as (v1 & EA1 & LD1); eauto.
    eexists; split.
    econstructor; eauto.
    constructor; auto.
  Qed.

End EXTERNAL_ARGUMENTS.


Lemma max_l_pos:
  forall l, 0 <= max_l l.
Proof.
  induction l; simpl; intros; eauto. omega. apply Z.max_le_iff. auto.
Qed.

Lemma stack_equiv_size_stack:
  forall s1 s2,
    stack_equiv s1 s2 ->
    size_stack s2 = size_stack s1.
Proof.
  induction 1; simpl; intros; eauto. omega.
Qed.

Hypothesis init_ra_not_undef: init_ra <> Vundef.
Lemma parent_ra_not_undef:
  forall ge s,
    callstack_function_defined return_address_offset ge s ->
    parent_ra init_ra s <> Vundef.
Proof.
  inversion 1; simpl; auto. congruence.
Qed.

Ltac same_hyps :=
  repeat match goal with
         | H1: ?a = _, H2: ?a = _ |- _ => rewrite H1 in H2; inv H2
         | H1: ?a, H2: ?a |- _ => clear H1
         end.

      Lemma step_correct:
    forall S1 t S2 (STEP: Mach.step init_ra return_address_offset invalidate_frame1 ge S1 t S2)
      S1' (MS: match_states S1 S1')
      (HC1: has_code return_address_offset ge S1)
      (CSC1: call_stack_consistency ge init_sg init_stk S1)
      (HC1': has_code return_address_offset ge S1')
      (CSC1': call_stack_consistency ge init_sg init_stk S1'),
    exists S2',
      Mach.step init_ra return_address_offset invalidate_frame2 ge S1' t S2' /\ match_states S2 S2'.
  Proof.
    destruct 1; intros S1' MS HC1 CSC1 HC1' CSC1'; inv MS; inv HC1; inv CSC1; inv HC1'; inv CSC1';
      unfold store_stack, load_stack in *; same_hyps.
    - eexists; split. econstructor; eauto. constructor; auto.
    - edestruct Mem.loadv_extends as (v' & LOADV' & LD); eauto.
      eexists; split. econstructor; eauto. constructor; auto.
      eapply lessdef_set_reg; eauto.
    - edestruct Mem.storev_extends as (m2' & STORE' & EXT); eauto.
      eexists; split. econstructor; eauto. constructor; auto.
      eapply lessdef_undef_regs; eauto.
      repeat rewrite_stack_blocks; eauto.
    - edestruct Mem.loadv_extends as (v' & LOADV' & LD); eauto.
      eexists; split. econstructor; eauto.
      erewrite parent_sp_same; eauto.
      constructor; auto.
      eapply lessdef_set_reg; eauto.
      eapply lessdef_set_reg; eauto.
    - edestruct eval_operation_lessdef as (v2 & EOP' & LD).
      apply lessdef_args; eauto. eauto. eauto.
      eexists; split. econstructor; eauto. constructor; eauto.
      eapply lessdef_set_reg; eauto.
      eapply lessdef_undef_regs; eauto.
    - edestruct eval_addressing_lessdef as (v2 & EOP' & LD).
      apply lessdef_args; eauto. eauto.
      edestruct Mem.loadv_extends as (v' & LOADV' & LD2); eauto.
      eexists; split. econstructor; eauto. constructor; eauto.
      eapply lessdef_set_reg; eauto.
    - edestruct eval_addressing_lessdef as (v2 & EOP' & LD).
      apply lessdef_args; eauto. eauto.
      edestruct Mem.storev_extends as (m2' & STOREV' & EXT'); eauto.
      eexists; split. econstructor; eauto. constructor; eauto.
      eapply lessdef_undef_regs; auto.
      repeat rewrite_stack_blocks; eauto.
    - eexists; split. econstructor; eauto.
      eapply find_function_ptr_lessdef; eauto. eauto.
      constructor; auto.
      apply Mem.extends_push; auto.
      repeat rewrite_stack_blocks; eauto. constructor; auto.
    - edestruct Mem.free_parallel_extends as (m2' & FREE' & EXT); eauto. constructor.
      edestruct Mem.loadbytesv_extends as (ra2 & LOADV' & LD). apply MLD.
      2: apply H2. simpl; auto.
      edestruct Mem.tailcall_stage_extends as (m3' & TC' & EXT'); eauto.
      inv CallStackConsistency0. eapply Mem.free_top_tframe_no_perm'; eauto.
      rewrite Ptrofs.unsigned_zero; simpl. unfold frame_info_of_size_and_pubrange in FRAME; repeat destr_in FRAME. reflexivity.
      eexists; split. econstructor; eauto.
      eapply find_function_ptr_lessdef; eauto.
      simpl Val.offset_ptr. rewrite LOADV'.
      inv LD. auto. exfalso; eapply parent_ra_not_undef; eauto.
      constructor; auto.
      repeat rewrite_stack_blocks; eauto.
      intros A B; rewrite A, B in SE.
      inv SE; constructor; auto.
      rewrite ! size_frames_tc. auto.
    - edestruct eval_builtin_args_lessdef as (vl2 & EBA & LDL); eauto.
      edestruct (external_call_mem_extends) as (vres' & m2' & EXTCALL & LDres & EXT' & UNCH); eauto.
      apply Mem.extends_push; eauto.
      edestruct (Mem.unrecord_stack_block_extends) as (m3' & USB & EXT2); eauto.
      eexists; split. econstructor; eauto. constructor; eauto.
      apply lessdef_set_res; auto.
      apply lessdef_undef_regs; auto.
      repeat rewrite_stack_blocks; eauto.
    - eexists; split. econstructor; eauto. constructor; eauto.
    - exploit eval_condition_lessdef. apply lessdef_args. eauto. eauto. eauto. intro COND.
      eexists; split. econstructor; eauto. constructor; eauto.
    - exploit eval_condition_lessdef. apply lessdef_args. eauto. eauto. eauto. intro COND.
      eexists; split. eapply exec_Mcond_false; eauto. constructor; eauto.      
    - generalize (RLD arg); rewrite H; inversion 1; subst.
      eexists; split. econstructor; eauto. constructor; eauto.
      apply lessdef_undef_regs; auto.
    - edestruct Mem.free_parallel_extends as (m2' & FREE' & EXT); eauto. constructor.
      edestruct Mem.loadbytesv_extends as (ra2 & LOADV' & LD). apply MLD. 2: eauto. auto.
      inv H2.
      edestruct Mem.tailcall_stage_right_extends as (m3' & TC & EXT2). apply EXT.
      inv CallStackConsistency. eapply Mem.free_top_tframe_no_perm'; eauto.
      rewrite Ptrofs.unsigned_zero; simpl. unfold frame_info_of_size_and_pubrange in FRAME; repeat destr_in FRAME. reflexivity.
      inv CallStackConsistency0. eapply Mem.free_top_tframe_no_perm'; eauto.
      rewrite Ptrofs.unsigned_zero; simpl. unfold frame_info_of_size_and_pubrange in FRAME; repeat destr_in FRAME. reflexivity.
      eexists; split. econstructor; eauto.
      rewrite LOADV'.
      inv LD. auto. exfalso; eapply parent_ra_not_undef; eauto.
      constructor; auto.
      repeat rewrite_stack_blocks; eauto.
      intro A; rewrite A in SE.  inv SE; constructor; auto. rewrite size_frames_tc; auto.
    - edestruct Mem.alloc_extends as (m1' & ALLOC & EXT1); eauto. reflexivity. reflexivity.
      edestruct Mem.storev_extends as (m2' & STORE & EXT2); eauto.
      edestruct Mem.record_stack_blocks_extends as (m3' & RSB & EXT3); eauto.
      {
        unfold in_frame; simpl. intros b [A|[]]; subst.
        repeat rewrite_stack_blocks. intro INS; apply Mem.in_frames_valid in INS.
        eapply Mem.fresh_block_alloc; eauto.
      }
      {
        red; simpl. intros b fi0 o k p [A|[]]; inv A. repeat rewrite_perms.
        destr.
        unfold frame_info_of_size_and_pubrange in H0; repeat destr_in H0. simpl. auto.
      }
      {
        repeat rewrite_stack_blocks. auto.
      }
      {
        repeat rewrite_stack_blocks.
        inv SE. omega. simpl. eapply stack_equiv_size_stack in H7. omega.
      }
      eexists; split. econstructor; eauto. constructor; auto.
      apply lessdef_undef_regs; auto.
      repeat rewrite_stack_blocks.
      intros A B; rewrite A, B in SE.
      inv SE; constructor; auto.
      revert H7. clear. 
      rewrite ! size_frames_cons. simpl.
      intros. f_equal. rewrite ! Z.max_r in H7; auto.
      apply max_l_pos.
      apply max_l_pos.
    - 
      edestruct (extcall_arguments_ld) as (lv & EA & LDL); eauto.
      edestruct (external_call_mem_extends) as (vres' & m2' & EXTCALL & LDres & EXT' & UNCH); eauto.
      eexists; split. econstructor; eauto.
      erewrite parent_sp_same_tl; eauto.
      apply list_forall2_length in SE. auto.
      constructor. auto.
      apply lessdef_set_pair. apply lessdef_undef_regs. auto. auto.
      repeat rewrite_stack_blocks. auto.
    - edestruct Mem.unrecord_stack_block_extends as (m2' & USB & EXT); eauto.
      eexists; split. econstructor; eauto. constructor; auto.
      revert SE. repeat rewrite_stack_blocks.
      rewrite EQ, EQ0. simpl. inversion 1; auto.
  Qed.

End WITHINITSP.
  Existing Instance inject_perm_all.

  Lemma initial_transf:
    forall p s, initial_state p s -> match_states s s.
  Proof.
    intros p s IS. inv IS.
    constructor; try reflexivity.
    apply Mem.extends_refl. auto.
    repeat rewrite_stack_blocks.
    repeat constructor; auto.
  Qed.

  Lemma final_transf:
    forall s1 s2 i, match_states s1 s2 -> final_state s1 i -> final_state s2 i.
  Proof.
    intros s1 s2 i MS FS; inv FS; inv MS. econstructor; eauto.
    generalize (RLD r); rewrite H0; inversion 1; auto.
  Qed.

  Lemma mach2_simulation:
    forall rao p,
      (forall (fb : block) (f : function),
          Genv.find_funct_ptr (Genv.globalenv p) fb = Some (Internal f) ->
          0 < fn_stacksize f) ->
      forward_simulation (Mach.semantics1 rao p) (Mach.semantics2 rao p).
  Proof.
    intros rao p SIZE.
    set (ge := Genv.globalenv p).
    set (init_stk := ((Some (make_singleton_frame_adt (Genv.genv_next ge) 0 0), nil)::nil) : stack).
    eapply forward_simulation_step with (match_states :=
                                           fun s1 s2 =>
                                             match_states s1 s2 /\
                                             has_code rao ge s1 /\
                                             call_stack_consistency ge signature_main init_stk s1 /\
                                             has_code rao ge s2 /\
                                             call_stack_consistency ge signature_main init_stk s2).
    - reflexivity.
    - simpl; intros s1 IS. eexists; split; eauto. split. eapply initial_transf; eauto.
      inv IS. repeat apply conj; constructor.
      + constructor.
      + simpl. constructor. repeat rewrite_stack_blocks. simpl.
        rewnb. fold ge. reflexivity.
        repeat rewrite_stack_blocks. simpl.
        constructor. constructor.
        change (size_arguments signature_main) with 0. intros; simpl.
        unfold Stacklayout.fe_ofs_arg in H2. omega.
      + repeat rewrite_stack_blocks. constructor. reflexivity.
      + constructor.
      + simpl. constructor. repeat rewrite_stack_blocks. simpl.
        rewnb. reflexivity.
        repeat rewrite_stack_blocks. simpl.
        constructor. constructor.
        change (size_arguments signature_main) with 0. intros; simpl.
        unfold Stacklayout.fe_ofs_arg in H2. omega.
      + repeat rewrite_stack_blocks. constructor. reflexivity.
    - simpl. intros s1 s2 r (MS & CSC). eapply final_transf; eauto.
    - simpl; intros s1 t s1' STEP s2 (MS & HC1 & CSC1 & HC2 & CSC2).
      edestruct step_correct as (s2' & STEP' & MS'); eauto.
      unfold Vnullptr. destr.
      eexists; split; eauto. repeat apply conj; auto.
      eapply has_code_step; eauto.
      eapply csc_step; eauto. apply invalidate_frame1_tl_stack. apply invalidate_frame1_top_no_perm.
      eapply has_code_step; eauto.
      eapply csc_step; eauto. apply invalidate_frame2_tl_stack. apply invalidate_frame2_top_no_perm.
  Qed.

End WITHEXTCALLS.