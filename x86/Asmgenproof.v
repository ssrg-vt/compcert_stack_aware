(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for x86-64 generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm.
Require Import Asmgen Asmgenproof0 Asmgenproof1.
Require AsmFacts.

Definition match_prog (p: Mach.program) (tp: Asm.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section PRESERVATION.
  Existing Instance inject_perm_all.
Context `{external_calls_prf: ExternalCalls}.

Local Existing Instance mem_accessors_default.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.
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
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B.
  rewrite H0 in EQ; inv EQ; auto.
Qed.

(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> code_size (fn_code tf) <= Ptrofs.max_unsigned.
Proof.
  intros. unfold transf_function in H.
  monadInv H. destruct (zlt Ptrofs.max_unsigned (code_size (fn_code x))); monadInv EQ0.
  omega.
Qed.

Section WITHINITSPRA.

Variable init_ra: val.
Variable init_stk: stack.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  exec_straight init_stk tge tf tc rs m c' rs' m' ->
  plus (step init_stk) tge (State rs m) E0 (State rs' m').
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight init_stk tge tf tc rs m tc' rs' m' ->
  transl_code_at_pc ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H.
  exploit exec_straight_steps_2; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.

  In passing, we also prove a "is tail" property of the generated Asm code.
*)

Section TRANSL_LABEL.

Remark mk_mov_label:
  forall rd rs k c, mk_mov rd rs k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_mov; unfold Asmgen.mk_mov; intros.
  destruct rd; try discriminate; destruct rs; TailNoLabel.
Qed.
Hint Resolve mk_mov_label: labels.

Remark mk_shrximm_label:
  forall n k c, mk_shrximm n k = OK c -> tail_nolabel k c.
Proof.
  intros. unfold mk_shrximm in H. monadInv H; TailNoLabel.
Qed.
Hint Resolve mk_shrximm_label: labels.

Remark mk_shrxlimm_label:
  forall n k c, mk_shrxlimm n k = OK c -> tail_nolabel k c.
Proof.
  intros. unfold mk_shrxlimm in H. monadInv H. 
  destruct (Int.eq n Int.zero); simpl; TailNoLabel.
Qed.
Hint Resolve mk_shrxlimm_label: labels.

Remark mk_intconv_label:
  forall f r1 r2 k c, mk_intconv f r1 r2 k = OK c ->
  (forall r r', nolabel (f r r')) ->
  tail_nolabel k c.
Proof.
  unfold mk_intconv; unfold Asmgen.mk_intconv; intros.
  destruct Archi.ptr64; destruct (low_ireg r2); TailNoLabel.
Qed.
Hint Resolve mk_intconv_label: labels.

Remark mk_storebyte_label:
  forall addr r k c, mk_storebyte addr r k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_storebyte; unfold Asmgen.mk_storebyte; intros. 
  destruct Archi.ptr64; destruct (low_ireg r); destruct (addressing_mentions addr RAX); TailNoLabel.
Qed.
Hint Resolve mk_storebyte_label: labels.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c ->
  tail_nolabel k c.
Proof.
  unfold loadind; intros. destruct ty; try discriminate; destruct (preg_of dst); TailNoLabel.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c ->
  tail_nolabel k c.
Proof.
  unfold storeind; intros. destruct ty; try discriminate; destruct (preg_of src); TailNoLabel.
Qed.

Remark mk_setcc_base_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc_base xc rd k).
Proof.
  intros. unfold mk_setcc_base.
  destruct xc; simpl; destruct (ireg_eq rd RAX); simpl; TailNoLabel.
Qed.

Remark mk_setcc_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc xc rd k).
Proof.
  intros. unfold mk_setcc. destruct (Archi.ptr64 || low_ireg rd).
  apply mk_setcc_base_label.
  eapply tail_nolabel_trans. apply mk_setcc_base_label. TailNoLabel.
Qed.

Remark mk_jcc_label:
  forall xc lbl' k,
  tail_nolabel k (mk_jcc xc lbl' k).
Proof.
  intros. unfold mk_jcc. destruct xc; simpl; TailNoLabel.
Qed.

Remark transl_cond_label:
  forall cond args k c,
  transl_cond cond args k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_cond; intros.
  destruct cond; TailNoLabel.
  destruct (Int.eq_dec n Int.zero); TailNoLabel.
  destruct (Int64.eq_dec n Int64.zero); TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_op; intros. destruct op; TailNoLabel.
  destruct (Int.eq_dec n Int.zero); TailNoLabel.
  destruct (Int64.eq_dec n Int64.zero); TailNoLabel.
  destruct (Float.eq_dec n Float.zero); TailNoLabel.
  destruct (Float32.eq_dec n Float32.zero); TailNoLabel.
  destruct (normalize_addrmode_64 x) as [am' [delta|]]; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_setcc_label.
Qed.

Remark transl_load_label:
  forall chunk addr args dest k c,
  transl_load chunk addr args dest k = OK c ->
  tail_nolabel k c.
Proof.
  intros. unfold transl_load in H. monadInv H. destruct chunk; TailNoLabel.
Qed.

Remark transl_store_label:
  forall chunk addr args src k c,
  transl_store chunk addr args src k = OK c ->
  tail_nolabel k c.
Proof.
  intros. unfold transl_store in H. monadInv H. destruct chunk; TailNoLabel.
Qed.

Lemma transl_instr_label:
  forall f i ep k c,
  transl_instr f i ep k = OK c ->
  match i with Mlabel lbl => c = (Plabel lbl) :: k | _ => tail_nolabel k c end.
Proof.
Opaque loadind.
  unfold transl_instr; unfold Asmgen.transl_instr; intros; destruct i; TailNoLabel.
  eapply loadind_label; eauto.
  eapply storeind_label; eauto.
  eapply loadind_label; eauto.
  eapply tail_nolabel_trans. eapply loadind_label; eauto. TailNoLabel.
  eapply transl_op_label; eauto.
  eapply transl_load_label; eauto.
  eapply transl_store_label; eauto.
  destruct s0; TailNoLabel.
  destruct s0; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_jcc_label.
Qed.

Lemma transl_instr_label':
  forall lbl f i ep k c,
  transl_instr f i ep k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B).
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
Proof.
  unfold transl_code.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a).
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl tf.(fn_code) = None
  | Some c => exists tc, find_label lbl tf.(fn_code) = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  unfold transf_function, transl_code.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (code_size (fn_code x))); inv EQ0.
  monadInv EQ. repeat destr_in EQ1. simpl. eapply transl_code_label; eauto. rewrite transl_code'_transl_code in EQ0; eauto.
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tge tf lbl rs m = Next rs' m
  /\ transl_code_at_pc ge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2.
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Ptrofs.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. erewrite functions_transl; eauto. 
  split. rewrite Pregmap.gss. constructor; auto.
  rewrite Ptrofs.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. omega.
  generalize (transf_function_no_overflow _ _ H0). omega.
  intros. apply Pregmap.gso; auto.
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  unfold return_address_offset.
  intros. eapply Asmgenproof0.return_address_exists; eauto.
- intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply A). intros. subst c0. repeat constructor.
- intros. unfold transf_function in H0. monadInv H0.
  destruct (zlt Ptrofs.max_unsigned (code_size (fn_code x))); inv EQ0.
  monadInv EQ. repeat destr_in EQ1. rewrite transl_code'_transl_code in EQ0.
  exists x; exists true; split; auto. unfold fn_code. repeat constructor.
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
*)

 Inductive match_states: Mach.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree ms (Vptr sp Ptrofs.zero) rs)
        (AXP: ep = true -> rs#RAX = parent_sp (Mem.stack m))
        (SAMEPERM: forall b o k p, in_stack (Mem.stack m) b -> (Mem.perm m b o k p <-> Mem.perm m' b o k p))
        (SAMEADT: (Mem.stack m) = (Mem.stack m')),
      match_states (Mach.State s fb (Vptr sp Ptrofs.zero) c ms m)
                   (Asm.State rs m')
  | match_states_call:
      forall s fb ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp (Mem.stack m)) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = parent_ra init_ra s)
        (SAMEPERM: forall b o k p, in_stack (Mem.stack m) b -> (Mem.perm m b o k p <-> Mem.perm m' b o k p))
        (SAMEADT: (Mem.stack m) = (Mem.stack m')),
      match_states (Mach.Callstate s fb ms m)
                   (Asm.State rs m')
  | match_states_return:
      forall s ms m m2 m' rs
        (STACKS: match_stack ge s)
        (USB: Mem.unrecord_stack_block m = Some m2)
        (MEXT: Mem.extends m2 m')
        (AG: agree ms (parent_sp (Mem.stack m)) rs)
        (RA_VUNDEF: rs RA = Vundef)
        (ATPC: rs PC = parent_ra init_ra s)
        (SAMEPERM: forall b o k p, in_stack (Mem.stack m) b -> (Mem.perm m b o k p <-> Mem.perm m' b o k p))
        (SAMEADT: Mem.stack m2 = Mem.stack m'),
      match_states (Mach.Returnstate s ms m)
                   (Asm.State rs m').

Lemma exec_straight_steps:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight init_stk tge tf c rs1 m1' k rs2 m2'
    /\ agree ms2 (Vptr sp Ptrofs.zero) rs2
    /\ (it1_is_parent ep i = true -> rs2#RAX = parent_sp (Mem.stack m2))) ->
  forall (SAMEPERM: forall b o k p, in_stack (Mem.stack m2) b -> (Mem.perm m2 b o k p <-> Mem.perm m2' b o k p))
    (SAMEADT: (Mem.stack m2) = (Mem.stack m2')),
  exists st',
  plus (step init_stk) tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb (Vptr sp Ptrofs.zero) c ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H7.
  exploit H3; eauto. intros [rs2 [A [B C]]].
  exists (State rs2 m2'); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto. eapply exec_straight_at; eauto.
Qed.

Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
    match_stack ge s ->
    Mem.extends m2 m2' ->
    Genv.find_funct_ptr ge fb = Some (Internal f) ->
    Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
    transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
    it1_is_parent ep i = false ->
    (forall k c (TR: transl_instr f i ep k = OK c),
        exists jmp, exists k', exists rs2,
              exec_straight init_stk tge tf c rs1 m1' (jmp :: k') rs2 m2'
              /\ agree ms2 (Vptr sp Ptrofs.zero) rs2
              /\ exec_instr init_stk tge tf jmp rs2 m2' = goto_label tge tf lbl rs2 m2') ->
    forall (SAMEPERM: forall b o k p, in_stack (Mem.stack m2) b -> (Mem.perm m2 b o k p <-> Mem.perm m2' b o k p))
      (SAMEADT: (Mem.stack m2) = (Mem.stack m2')),
  exists st',
  plus (step init_stk) tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb (Vptr sp Ptrofs.zero) c' ms2 m2) st'.
Proof.
  intros s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c' H H0 H1 H2 H3 H4 H5.
  inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  traceEq.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the PPC side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except the
  transition from [Mach.Returnstate] to [Mach.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach.state) : nat :=
  match s with
  | Mach.State _ _ _ _ _ _ => 0%nat
  | Mach.Callstate _ _ _ _ => 0%nat
  | Mach.Returnstate _ _ _ => 1%nat
  end.

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Lemma Vnullptr_def:
  Vnullptr <> Vundef.
Proof.
  clear; unfold Vnullptr; destr.
Qed.

Hypothesis init_ra_not_vundef: init_ra <> Vundef.

Hypothesis init_ra_type: Val.has_type init_ra Tptr.

Hypothesis frame_size_correct:
  forall fb f,
    Genv.find_funct_ptr ge fb = Some (Internal f) ->
    0 < Mach.fn_stacksize f.

Lemma agree_undef_regs_parallel:
  forall l sp rs rs0,
    agree rs sp rs0 ->
    agree (Mach.undef_regs l rs) sp
    (undef_regs preg_of ## l rs0).
Proof.
  intros; eapply agree_undef_regs; eauto.
  intros. 
  rewrite undef_regs_other; auto.
  intros. intro; subst.
  rewrite preg_notin_charact  in H1.
  rewrite in_map_iff in H2.
  destruct H2 as (x & EQ & IN).
  apply H1 in IN.
  congruence.
Qed.

  Lemma exec_store_stack:
    forall F V (ge: _ F V) k m1 a rs1 rs l rs2 m2 sz,
      exec_store ge k m1 a rs1 rs l sz = Next rs2 m2 ->
      Mem.stack m2 = Mem.stack m1.
  Proof.
    intros.
    unfold exec_store in H; repeat destr_in H.
    unfold Mem.storev in Heqo; destr_in Heqo; inv Heqo.
    erewrite Mem.store_stack_blocks. 2: eauto.
    split; auto.
  Qed.

  Lemma exec_load_stack:
    forall F V (ge: _ F V) k m1 a rs1 rs rs2 m2 sz,
      exec_load ge k m1 a rs1 rs sz = Next rs2 m2 ->
      Mem.stack m2 = Mem.stack m1.
  Proof.
    intros.
    unfold exec_load in H; destr_in H.
  Qed.

  Lemma goto_label_stack:
    forall F V (ge: _ F V) f l m1 rs1 rs2 m2,
      goto_label ge f l rs1 m1 = Next rs2 m2 ->
      Mem.stack m2 = Mem.stack m1.
  Proof.
    intros.
    unfold goto_label in H; repeat destr_in H.
  Qed.

  Require Import AsmFacts.

  Lemma if_zeq:
    forall {T} a P (A B : T),
      (if zeq a a && P then A else B) = if P then A else B.
  Proof.
    intros.
    destruct zeq; try congruence. simpl; reflexivity.
  Qed.

  Lemma if_zeq':
    forall {T} a (A B : T),
      (if proj_sumbool (zeq a a) then A else B) = A.
  Proof.
    intros.
    destruct zeq; simpl; try congruence. 
  Qed.

  Lemma if_peq:
    forall {T} a P (A B : T),
      (if peq a a && P then A else B) = if P then A else B.
  Proof.
    intros.
    destruct peq; try congruence. simpl; reflexivity.
  Qed.

  Lemma if_forall_dec:
    forall {A P} (Pdec: forall x:A, {P x} + {~P x}) Q {T} (A B: T) x,
      Forall P x ->
    (if Forall_dec _ Pdec x && Q then A else B) = if Q then A else B.
  Proof.
    intros.
    destruct (Forall_dec _ Pdec x); auto. congruence.
  Qed.

  Lemma check_alloc_frame_correct:
    forall fi f,
      Mach.check_alloc_frame fi f ->
      exists x, check_alloc_frame fi = left x.
  Proof.
    unfold Mach.check_alloc_frame.
    intros fi f A.
    unfold check_alloc_frame.
    destruct zlt; auto. eauto. omega.
  Qed.

  Variable init_sg: signature.

  Lemma load_parent_pointer_correct:
    forall (tge: genv) fn (rd: ireg) x m1 (rs1: regset) s fb sp c f
      (PISP_DEF: exists bisp, parent_sp (Mem.stack m1) = Vptr bisp Ptrofs.zero)
      (FFP: Genv.find_funct_ptr ge fb = Some (Internal f))
      (RD: rd <> RSP)
      ms1
      (LP: call_stack_consistency ge init_sg init_stk (Mach.State s fb (Vptr sp Ptrofs.zero) c ms1 m1))
      m2 (EQSTK: Mem.stack m1 = Mem.stack m2),
      exists rs2 sp,
        exec_straight init_stk tge fn ((Pload_parent_pointer rd (Mach.fn_stacksize f)) :: x) rs1 m2 x rs2 m2 /\
        Mem.is_ptr (parent_sp (Mem.stack m1)) = Some sp /\
        rs2 rd = sp /\ forall r, data_preg r = true -> r <> rd -> rs2 r = rs1 r.
  Proof.
    intros.
    destruct PISP_DEF as (bisp & PISP_DEF).
    exists (nextinstr (rs1#rd <- (parent_sp (Mem.stack m1))) 
                 (Ptrofs.repr (instr_size ((Pload_parent_pointer rd (Mach.fn_stacksize f)))))), (Vptr bisp Ptrofs.zero).
    split; [|split].
    - constructor.
      + unfold exec_instr. simpl. destr. destr.
        rewrite <- EQSTK, PISP_DEF. simpl. auto.
        contradict Heqb. unfold check_top_frame. rewrite <- EQSTK.
        inv LP. inv CallStackConsistency. rewrite BLOCKS. rewrite FSIZE.
        rewrite FFP in FIND; inv FIND.
        unfold proj_sumbool.
        destr.
        destr. simpl. congruence.
        inv f. red in H2. simpl in *. destruct H2; congruence.
        unfold frame_info_of_size_and_pubrange in FRAME; repeat destr_in FRAME.
        exfalso; apply n; clear n.
        constructor; auto. red. split; auto.
      + rewrite nextinstr_pc. rewrite Pregmap.gso. auto. congruence.
    - rewrite PISP_DEF; reflexivity.
    - rewrite nextinstr_inv by congruence.
      rewrite Pregmap.gss. rewrite PISP_DEF. split; auto.
      intros.
      rewrite nextinstr_inv.
      + rewrite Pregmap.gso by congruence; auto.
      + intro; subst. contradict H; simpl; congruence.
  Qed.


  Lemma list_prefix_is_prefix:
  forall isg istk cs stk,
    list_prefix isg istk cs stk ->
    exists l, stk = l ++ istk.
Proof.
  induction 1; simpl; intros; eauto.
  subst. exists nil; reflexivity.
  destruct IHlist_prefix as (l & EQ); subst.
  exists ((Some f,r)::l); reflexivity.
Qed.

Lemma list_prefix_spec_istk:
  forall isg istk cs stk,
    list_prefix isg istk cs stk ->
    init_sp_stackinfo isg istk.
Proof.
  induction 1; simpl; intros; eauto. subst; auto.
Qed.

Lemma in_stack'_app:
  forall s1 s2 b,
    in_stack' (s1 ++ s2) b <-> in_stack' s1 b \/ in_stack' s2 b.
Proof.
  induction s1; simpl; intros; eauto.
  tauto.
  rewrite IHs1. tauto.
Qed.

Lemma init_sp_csc:
  forall b o
    (ISP: init_sp init_stk = Vptr b o)
    s stk
    (LP: list_prefix init_sg init_stk s stk),
  exists fi, in_stack' stk (b, fi).
Proof.
  intros b o ISP.
  unfold init_sp, current_sp, current_frame_sp in ISP. repeat destr_in ISP.
  intros.
  edestruct list_prefix_is_prefix as (l & EQ); eauto.
  apply list_prefix_spec_istk in LP.
  destruct stk. simpl in *. apply app_cons_not_nil in EQ. easy.
  simpl in *. subst.
  inv LP.
  exists f0.
  simpl in Heqo0. inv Heqo0.
  destruct l; simpl in EQ; inv EQ.
  left. red. simpl. red. rewrite Heql. left; reflexivity.
  right. rewrite in_stack'_app. right. left. red. simpl. red. rewrite Heql. left; reflexivity.
Qed.

Lemma init_sp_csc':
  forall 
    s stk
    (LP: list_prefix init_sg init_stk s stk),
  exists b,
    current_sp stk = Vptr b Ptrofs.zero.
Proof.
  intros.
  edestruct list_prefix_is_prefix as (l & EQ); eauto.
  exploit list_prefix_spec_istk; eauto. intro ISS. inv ISS.
  destruct l.
  - simpl. unfold current_frame_sp. simpl.
    inv PRIV. eauto.
  - simpl in *. unfold current_frame_sp. inv LP. inv STKEQ. simpl. inv INIT. 
    apply (f_equal (@length _)) in H1. rewrite app_length in H1.  simpl in H1. omega.
    simpl. rewrite BLOCKS. eauto.
Qed.

Lemma code_tail_code_size:
  forall a b sz,
    code_tail sz (a ++ b) b ->
    sz = code_size a.
Proof.
  intros a b sz.
  remember (a++b).
  intro CT; revert sz l b CT a Heql.
  induction 1; simpl; intros; eauto.
  apply (f_equal (@length _)) in Heql. rewrite app_length in Heql.
  destruct a; simpl in *; try omega.
  destruct a. simpl in *. subst. apply code_tail_no_bigger in CT. simpl in CT. omega. simpl in Heql.
  inv Heql.
  specialize (IHCT _ eq_refl). subst. simpl. omega.
Qed.

Lemma offsets_after_call_app:
  forall y z pos,
    offsets_after_call (y ++ z) pos =  offsets_after_call y pos ++ offsets_after_call z (pos + code_size y).
Proof.
  induction y; simpl; intros; eauto. rewrite Z.add_0_r. auto.
  rewrite ! IHy. destr. simpl. rewrite Z.add_assoc. reflexivity.
  simpl. rewrite Z.add_assoc. reflexivity.
Qed.

Lemma code_size_app:
  forall c1 c2,
    code_size (c1 ++ c2) = code_size c1 + code_size c2.
Proof.
  induction c1; simpl; intros; rewrite ? IHc1; omega.
Qed.

Lemma has_code_parent_ra_after_call:
  forall (init_ra_after_call: ra_after_call tge init_ra)
    s
    (HC: callstack_function_defined return_address_offset ge s),
    ra_after_call tge (parent_ra init_ra s).
Proof.
  intros init_ra_after_call s HC.
  destruct s; simpl. auto.
  destruct s; simpl.
  inv HC.
  split. congruence.
  intros b o EQ; inv EQ.
  edestruct functions_translated as (tf & FFP' & TF); eauto.
  rewrite FFP'. intros f EQ; inv EQ.
  red. simpl in TF. monadInv TF.
  red in RAU.
  specialize (fun tc => RAU _ tc EQ).
  monadInv EQ. repeat destr_in EQ1.
  monadInv EQ0. repeat destr_in EQ1. simpl in *. rewrite pred_dec_false. 2: inversion 1.
  destruct TAIL as (l & sg & ros & CODE). rewrite CODE in EQ.
  rewrite transl_code'_transl_code in EQ.
  edestruct transl_code_app as (ep2 & y & TC1 & TC2); eauto.
  monadInv TC2.
  simpl in EQ0. monadInv EQ0.
  specialize (RAU _ EQ1).
  assert (exists icall, x = icall :: x0 /\ is_call icall).
  {
    destr_in EQ2; monadInv EQ2; eexists; split; eauto; constructor.
  }
  destruct H as (icall & ICALL & ISCALL). subst.
  generalize (code_tail_code_size (Pallocframe (Mach.fn_stacksize trf) (fn_frame_pubrange trf) (fn_retaddr_ofs trf) :: y ++ icall :: nil) x0).
  simpl. rewrite app_ass. simpl. intro EQSZ; specialize (EQSZ _ RAU).
  rewrite offsets_after_call_app.
  apply in_app. right. simpl. rewrite pred_dec_true.
  left. rewrite EQSZ.
  rewrite code_size_app. simpl. omega. auto.
Qed.

Hypothesis init_ra_after_call: ra_after_call tge init_ra.

Theorem step_simulation:
  forall S1 t S2, Mach.step init_ra return_address_offset invalidate_frame2 ge S1 t S2 ->
             forall S1' (MS: match_states S1 S1')
               (HC: has_code return_address_offset ge S1)
               (CSC: call_stack_consistency ge init_sg init_stk S1),
  (exists S2', plus (step init_stk) tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS(* ; inv ANN *).

- (* Mlabel *)
  left; eapply exec_straight_steps; eauto; intros.
  unfold transl_instr in TR. monadInv TR. 
  econstructor; split. apply exec_straight_one. unfold exec_instr; simpl; eauto. auto.
  split. apply agree_nextinstr; auto. simpl; congruence.
  
- (* Mgetstack *)
  unfold load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  exploit loadind_correct; eauto. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. eapply agree_set_mreg; eauto. congruence.
  simpl; congruence.
    
- (* Msetstack *)
  unfold store_stack in H.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]].
  left; eapply exec_straight_steps; eauto.
  rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
  exploit storeind_correct; eauto.

  intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. eapply agree_undef_regs; eauto.
  simpl; intros. rewrite Q; auto with asmgen.
  rewrite_stack_blocks. auto.
  Local Transparent destroyed_by_setstack.
  destruct ty; simpl; intuition congruence.
  rewrite_stack_blocks.
  intros.
  repeat rewrite_perms. eauto.
  repeat rewrite_stack_blocks; eauto.

- (* Mgetparam *)
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H0. auto.
  intros [ra' [A B]]. (* rewrite (sp_val _ _ _ AG) in A. *)
  (* exploit (lessdef_parent_sp init_sp); eauto. clear B; intros B; subst parent'. *)
  (* exploit Mem.loadv_extends. eauto. eexact H1. auto. *)
  (* intros [v' [C D]]. *)
Opaque loadind.
  left; eapply exec_straight_steps; eauto; intros.
  assert (DIFF: negb (mreg_eq dst AX) = true -> IR RAX <> preg_of dst).
    intros. change (IR RAX) with (preg_of AX). red; intros.
    unfold proj_sumbool in H1. destruct (mreg_eq dst AX); try discriminate.
    elim n. eapply preg_of_injective; eauto.
  destruct ep; simpl in TR.
(* RAX contains parent *)
  exploit loadind_correct. eexact TR.
  instantiate (2 := rs0). rewrite AXP; eauto.
  intros [rs1 [P [Q R]]].
  exists rs1; split. eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
  simpl; intros. rewrite R; auto.
(* RAX does not contain parent *)
  monadInv TR.
  assert (exists bsp, parent_sp (Mem.stack m) = Vptr bsp Ptrofs.zero).
  {
    unfold Mem.loadv in H0; repeat destr_in H0. unfold Val.offset_ptr in Heqv0.
    destr_in Heqv0.
    exists b0; f_equal.
    unfold parent_sp, current_sp, current_frame_sp in Heqv1. repeat destr_in Heqv1.
  }
  exploit load_parent_pointer_correct. eauto. eauto.
  instantiate (1 := RAX). congruence. eauto.
  apply SAMEADT. intros (rs2 & sp & ESLoad & ISPTR & RS2SPEC & RS2OTHER).
  unfold Mem.is_ptr in ISPTR. destr_in ISPTR. inv ISPTR.
  exploit loadind_correct. eexact EQ. rewrite <- H3. eauto.
  intros [rs3 [S [T U]]].
  exists rs3; split;[|split].
  + eapply exec_straight_trans; eauto.
  + eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
  + simpl; intros. rewrite U; auto. 
  
- (* Mop *)
  assert (eval_operation tge (Vptr sp0 Ptrofs.zero) op rs##args m = Some v).
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].
  assert (S: Val.lessdef v (rs2 (preg_of res))) by (eapply Val.lessdef_trans; eauto).
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto.
  simpl; congruence.
  
- (* Mload *)
  assert (eval_addressing tge (Vptr sp0 Ptrofs.zero) addr rs##args = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  simpl; congruence.
  
- (* Mstore *)
  assert (eval_addressing tge (Vptr sp0 Ptrofs.zero) addr rs##args = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  intros. simpl in TR.
  exploit transl_store_correct; eauto. intros [rs2 [P Q]].
  exists rs2; split. eauto.
  split. eapply agree_undef_regs; eauto.
  simpl; congruence.
  repeat rewrite_stack_blocks; intros; repeat rewrite_perms; eauto.
  repeat rewrite_stack_blocks; eauto.

- (* Mcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: code_size tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct H0 as (fd' & FFPcalled).
  destruct ros as [rf|fid]; simpl in H; monadInv H6.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H0; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H7). intro CT1.
  set (sz:=(Ptrofs.repr (instr_size ((Pcall (inl x0) sig))))).
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs sz)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  unfold exec_instr; simpl. rewrite H6. simpl. rewrite pred_dec_true.
  exploit functions_translated. apply FFPcalled. intros (tf0 & FPPcalled' & TF). rewrite FPPcalled'. eauto. auto.
  econstructor; eauto.
  econstructor; eauto.
  apply Mem.extends_push. auto.
  repeat rewrite_stack_blocks. simpl.
  inv CSC. inv CallStackConsistency. simpl. unfold current_frame_sp. simpl. rewrite BLOCKS.
  eapply agree_exten; eauto. intros. Simplifs.
  Simplifs. rewrite <- H3. auto.
  repeat rewrite_stack_blocks; intros; repeat rewrite_perms; eauto.
  repeat rewrite_stack_blocks; eauto. f_equal; auto.

+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H7). intro CT1.
  set (sz:=(Ptrofs.repr (instr_size ((Pcall (inr fid) sig))))).
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs sz)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  unfold exec_instr; simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. simpl. rewrite pred_dec_true; auto.
  edestruct @Genv.find_funct_ptr_transf_partial as (tf0 & FFP' & TR). eauto. 2: rewrite FFP'. eauto. eauto.
  econstructor; eauto.
  econstructor; eauto.
  apply Mem.extends_push; auto.
  repeat rewrite_stack_blocks. inv CSC. inv CallStackConsistency. simpl. unfold current_frame_sp.
  simpl; rewrite BLOCKS.
  simpl. eapply agree_exten; eauto. intros. Simplifs.
  Simplifs. rewrite <- H3. auto.
  repeat rewrite_stack_blocks; intros; repeat rewrite_perms; eauto.
  repeat rewrite_stack_blocks; f_equal; eauto.

- (* Mtailcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: code_size tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  exploit Mem.loadbytesv_extends. eauto. 2: eexact H2. auto. simpl. intros [ra' [C D]].
  exploit (lessdef_parent_ra init_ra); eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. constructor. intros (m2_ & E & F).
  inv CSC. erewrite agree_sp in H13 by eauto. inv H13.
  exploit Mem.tailcall_stage_extends; eauto.
  inv CallStackConsistency. rewrite SAMEADT in H14.
  eapply Mem.free_top_tframe_no_perm'; eauto.
  assert (tf0 = f) by congruence. subst. rewrite Ptrofs.unsigned_zero. simpl.
  unfold frame_info_of_size_and_pubrange in FRAME; repeat destr_in FRAME. reflexivity.
  intros (m2' & TC & EXT).
    
  assert (CTF: check_top_frame m'0 (Some stk) (Mach.fn_stacksize f) = true).
  {
    unfold check_top_frame. rewrite <- SAMEADT.
    inv CallStackConsistency. rewrite FSIZE, BLOCKS.
    unfold proj_sumbool. destr. rewrite H6 in FIND0; inv FIND0.
    rewrite pred_dec_true. reflexivity.
    unfold frame_info_of_size_and_pubrange in FRAME; repeat destr_in FRAME. reflexivity.
    exfalso. apply n.
    constructor; auto.
    red; split; auto.
    simpl.
    unfold frame_info_of_size_and_pubrange in FRAME; repeat destr_in FRAME. simpl. f_equal. congruence. 
  }

inv CallStackConsistency. simpl.
edestruct init_sp_csc' as (bsp & EQsp). eauto.

rewrite H6 in FIND0; inv FIND0.


assert (CISIS: check_init_sp_in_stack init_stk m2').
{
  red. repeat rewrite_stack_blocks.
  rewrite <- SAMEADT, <- H14. simpl.
  destr. eapply init_sp_csc in Heqv; eauto. destruct Heqv. inversion 1; subst.
  eapply in_stack'_in_stack; eauto. right. eauto.
}

assert (IST: is_stack_top (Mem.stack m'0) stk).
{
  revert CTF. unfold check_top_frame.
  rewrite <- SAMEADT, <- H14. red. simpl.
  unfold get_frames_blocks. simpl. rewrite andb_true_iff. simpl.
  intros (A & B).
  unfold get_frame_blocks. rewrite BLOCKS.
  simpl. left. auto.
}

destruct H0 as (fd' & FFPcalled).
exploit functions_translated. apply FFPcalled. intros (tf1 & FPPcalled' & TF).

  destruct ros as [rf|fid]; simpl in H; monadInv H8.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H0; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H9). intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl. apply H6. eauto. eapply find_instr_tail; eauto.
  unfold exec_instr; simpl.
  replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  rewrite C. rewrite <- (sp_val _ _ _ AG). rewrite CTF.
  rewrite Ptrofs.unsigned_zero in E. simpl in E.
  generalize (frame_size_correct _ _ FIND). intros SEQ.
  destr.
  rewrite E, TC.
  rewrite pred_dec_true by auto.
  rewrite <- SAMEADT, <- H14. simpl; rewrite EQsp. simpl.
  eauto.
  
  apply star_one. eapply exec_step_internal.
  set (sz := (Ptrofs.repr
                   (instr_size
                      ((Pfreeframe ((Mach.fn_stacksize tf0)) (fn_retaddr_ofs tf0)))))) in *.
  transitivity (Val.offset_ptr rs0#PC sz). auto.
  rewrite <- H5. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  unfold exec_instr; simpl.
  rewrite nextinstr_inv. 2: congruence.
  rewrite (@Pregmap.gso _ x0 RA) by congruence.
  rewrite (@Pregmap.gso _ x0 RSP). 2: eapply ireg_of_not_rsp; eauto. rewrite H8. simpl. rewrite pred_dec_true by auto.
  rewrite FPPcalled'. eauto. traceEq.
  econstructor; eauto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  repeat rewrite_stack_blocks. simpl. rewrite <- H14. simpl. inversion 1; subst. rewrite EQsp. simpl.
  eapply agree_change_sp; eauto. congruence. constructor.
  (* Simplifs. rewrite Pregmap.gso; auto. *)
  (* generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence. *)
  repeat rewrite_stack_blocks; intros; repeat rewrite_perms; eauto.
  destr. apply SAMEPERM.  rewrite in_stack_cons in H10. destruct H10. easy. apply in_stack_tl.  rewrite EQ0. auto. 
  repeat rewrite_stack_blocks. rewrite SAMEADT. intros A B; rewrite A in B; inv B; auto.
  
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H9). intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  unfold exec_instr; unfold exec_instr; simpl. replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  rewrite C. rewrite <- (sp_val _ _ _ AG).
  rewrite Ptrofs.unsigned_zero in E. simpl in E.
  generalize (frame_size_correct _ _ FIND). intros SEQ.
  rewrite CTF, E, TC.
  destr.
  rewrite <- SAMEADT, <- H14. simpl; rewrite EQsp. simpl.
  apply pred_dec_true. auto.

  apply star_one. eapply exec_step_internal.
  set (sz := (Ptrofs.repr
                   (instr_size
                      (Pfreeframe ((Mach.fn_stacksize tf0)) (fn_retaddr_ofs tf0))))) in *.
  transitivity (Val.offset_ptr rs0#PC sz).
  auto. 
  rewrite <- H5. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  unfold exec_instr; simpl.
  unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. simpl. rewrite pred_dec_true; auto.
  edestruct @Genv.find_funct_ptr_transf_partial as (tf2 & FFP' & TR). eauto. 2: rewrite FFP'. eauto. eauto.
  traceEq.
  econstructor; eauto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  repeat rewrite_stack_blocks. simpl. rewrite <- H14. simpl. inversion 1. subst. rewrite EQsp. simpl.
  eapply agree_change_sp; eauto. congruence. constructor.
  repeat rewrite_stack_blocks; intros; repeat rewrite_perms; eauto.
  destr. apply SAMEPERM. rewrite in_stack_cons in H0. destruct H0. easy. apply in_stack_tl. rewrite EQ1; simpl; auto.
  repeat rewrite_stack_blocks. rewrite SAMEADT. intros A B; rewrite A in B; inv B; auto.

- (* Mbuiltin *)
  inv AT. monadInv H5.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H4); intro NOOV.
  exploit builtin_args_match; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto.
  apply Mem.extends_push; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  edestruct Mem.unrecord_stack_block_extends as (m3' & USB & EXT'); eauto.
  left. econstructor; split.
  + apply plus_one.
    eapply exec_step_builtin. eauto. eauto.
    eapply find_instr_tail; eauto.
    erewrite <- sp_val by eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved. eauto. auto.
    clear. induction res; simpl; intros; eauto. intro; subst.
    eapply preg_of_not_SP in H. congruence.
    eauto.
  + econstructor; eauto.
    * instantiate (2 := tf); instantiate (1 := x).
      unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss.
      rewrite undef_regs_other. rewrite set_res_other. rewrite undef_regs_other_2.
      rewrite <- H2. simpl. econstructor; eauto.
      eapply code_tail_next_int; eauto.
      rewrite preg_notin_charact. intros. auto with asmgen.
      auto with asmgen.
      simpl; intros. intuition congruence.
    * apply agree_nextinstr_nf. eapply agree_set_res; auto.
      eapply agree_undef_regs; eauto. intros; apply undef_regs_other_2; auto.
    * congruence.
    * repeat rewrite_stack_blocks; simpl; intros; repeat rewrite_perms; eauto.
      repeat rewrite_stack_blocks. rewrite in_stack_cons, <- SAMEADT; auto.
      repeat rewrite_stack_blocks. rewrite in_stack_cons; auto.
    * repeat rewrite_stack_blocks; eauto.

- (* Mgoto *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4.
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (State rs' m'); split.
  apply plus_one. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  unfold exec_instr; simpl; eauto.
  econstructor; eauto.
  eapply agree_exten; eauto with asmgen.
  congruence.
  
- (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps_goto; eauto.
  intros. simpl in TR.
  destruct (transl_cond_correct init_stk tge tf cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]].
  rewrite EC in B.
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  exists ((Pjcc c1 lbl)); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  unfold exec_instr; simpl. rewrite B. auto.
(* jcc; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct b1.
  (* first jcc jumps *)
  exists ((Pjcc c1 lbl)); exists ((Pjcc c2 lbl) :: k); exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  unfold exec_instr; simpl. rewrite TC1. auto.
  (* second jcc jumps *)
  exists ((Pjcc c2 lbl)); exists k; exists (nextinstr rs' (instr_size_in_ptrofs (Pjcc c1 lbl))).
  split. eapply exec_straight_trans. eexact A.
  eapply exec_straight_one. unfold exec_instr; simpl. rewrite TC1. auto. auto.
  split. eapply agree_exten; eauto.
  intros; Simplifs.
  unfold exec_instr; simpl. rewrite eval_testcond_nextinstr. rewrite TC2.
  destruct b2; auto || discriminate.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (andb_prop _ _ H3). subst.
  exists ((Pjcc2 c1 c2 lbl)); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  unfold exec_instr; simpl. rewrite TC1; rewrite TC2; auto.

- (* Mcond false *)
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  destruct (transl_cond_correct init_stk tge tf cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]].
  rewrite EC in B.
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. unfold exec_instr; simpl. rewrite B. eauto. auto.
  split. apply agree_nextinstr. eapply agree_exten; eauto.
  simpl; congruence.
(* jcc ; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (orb_false_elim _ _ H1); subst.
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  eapply exec_straight_two; unfold exec_instr. simpl. rewrite TC1. eauto. auto.
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2. eauto. auto. auto.
  split. apply agree_nextinstr. apply agree_nextinstr. eapply agree_exten; eauto.
  simpl; congruence.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  exists (nextinstr rs' (instr_size_in_ptrofs (Pjcc2 c1 c2 lbl))); split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. unfold exec_instr; simpl.
  rewrite TC1; rewrite TC2.
  destruct b1. simpl in *. subst b2. auto. auto.
  auto.
  split. apply agree_nextinstr. eapply agree_exten; eauto.
  rewrite H1; congruence.
  
- (* Mjumptable *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  set (rs1 := rs0 #RAX <- Vundef #RDX <- Vundef).
  exploit (find_label_goto_label f tf lbl rs1); eauto. 
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  eapply find_instr_tail; eauto.
  unfold exec_instr; simpl. rewrite <- H9.  unfold Mach.label in H0; unfold label; rewrite H0. eexact A.
  econstructor; eauto.
Transparent destroyed_by_jumptable.
  apply agree_undef_regs with rs0; auto. 
  simpl; intros. destruct H8. rewrite C by auto with asmgen. unfold rs1; Simplifs.
  congruence.
    
- (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inv AT.
  assert (NOOV: code_size tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  exploit Mem.loadbytesv_extends. eauto. 2: eexact H0. auto. simpl. intros [ra' [C D]].
  exploit (lessdef_parent_ra init_ra); eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. constructor. intros (m2' & E & F).
  inv CSC. erewrite agree_sp in H11; eauto. inv H11.
  exploit Mem.tailcall_stage_extends; eauto.
  inv CallStackConsistency. rewrite SAMEADT in H12.
  eapply Mem.free_top_tframe_no_perm'; eauto.
  assert (tf0 = f) by congruence. subst.
  unfold frame_info_of_size_and_pubrange in FRAME; repeat destr_in FRAME. reflexivity.
  intros (m3' & CS & EXT').
  monadInv H6.
  exploit code_tail_next_int; eauto. intro CT1.

  assert (CTF: check_top_frame m'0 (Some stk) (Mach.fn_stacksize f) = true).
  {
    unfold check_top_frame. rewrite <- SAMEADT.
    inv CallStackConsistency. rewrite FSIZE, BLOCKS.
    unfold proj_sumbool. destr. rewrite H in FIND0; inv FIND0.
    unfold frame_info_of_size_and_pubrange in FRAME; repeat destr_in FRAME.
    rewrite zeq_true. reflexivity.
    exfalso. apply n.
    constructor; auto.
    red; split; auto.
    simpl. symmetry. rewrite H in FIND0; inv FIND0.
    unfold frame_info_of_size_and_pubrange in FRAME; repeat destr_in FRAME. reflexivity.
  }

  inversion CallStackConsistency. subst.
  unfold invalidate_frame2 in H2.
  assert (Mem.stack m'' = (None, f0::r)::s0). repeat rewrite_stack_blocks.
  rewrite <- H11. intros AA; inv AA. simpl. reflexivity.
  edestruct (Mem.unrecord_stack_block_succeeds m'') as (m''' & USB & STKEQ). eauto.
  edestruct Mem.unrecord_stack_block_extends as (m4' & USB' & EXT''). 2: apply USB. eauto.
  rewrite FIND in FIND0; inv FIND0.
  edestruct init_sp_csc' as (bsp & EQsp). eauto.

  assert (CISIS: check_init_sp_in_stack init_stk m3').
  {
    red. repeat rewrite_stack_blocks.
    rewrite <- SAMEADT, <- H11. simpl.
    destr. eapply init_sp_csc in Heqv; eauto. destruct Heqv.
    intro AA; inv AA.
    rewrite in_stack_cons. right.
    eapply in_stack'_in_stack; eauto.
  }
  assert (IST: is_stack_top (Mem.stack m'0) stk).
  {
    revert CTF. unfold check_top_frame.
    rewrite <- SAMEADT, <- H11. red. simpl.
    unfold get_frames_blocks. simpl. rewrite andb_true_iff. simpl.
    intros (A & B).
    unfold get_frame_blocks. rewrite BLOCKS.
    simpl. left. auto.
  }

  left; econstructor; split.
  + eapply plus_left. eapply exec_step_internal. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    unfold exec_instr; simpl. rewrite C. rewrite <- (sp_val _ _ _ AG).
    rewrite Ptrofs.unsigned_zero in E; simpl in E.
    generalize (frame_size_correct _ _ FIND). intros SEQ.
    rewrite  E, CS, CTF. destr.
    rewrite <- SAMEADT, <- H11; simpl; rewrite EQsp; simpl; eauto.
    apply pred_dec_true; auto.

    apply star_one. eapply exec_step_internal.
    transitivity (Val.offset_ptr rs0#PC (instr_size_in_ptrofs (Pfreeframe (Mach.fn_stacksize tf0) (fn_retaddr_ofs tf0)))). 
    auto. rewrite <- H3. simpl. eauto.
    eapply functions_transl; eauto. 
    eapply find_instr_tail. unfold instr_size_in_ptrofs. 
    destruct (frame_size_correct fb tf0 FIND). eauto.
    unfold exec_instr; simpl. rewrite USB'. 
    rewrite pred_dec_true. rewrite pred_dec_true. eauto.
    red. repeat rewrite_stack_blocks. constructor; auto. 
    rewrite nextinstr_inv by congruence. rewrite Pregmap.gss.
    eapply has_code_parent_ra_after_call; eauto.
    inv HC; eauto.
    traceEq.
  +
    econstructor. auto. eauto. auto.
    apply agree_set_other; auto.
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    repeat rewrite_stack_blocks. simpl. rewrite <- H11. inversion 1; subst. simpl. rewrite EQsp. simpl.
    eapply agree_change_sp; eauto. congruence. constructor. 
    eauto. auto.
    repeat rewrite_stack_blocks; intros; repeat rewrite_perms; eauto.
    destr. apply SAMEPERM. rewrite in_stack_cons in H8. destruct H8. easy.
    rewrite EQ1. apply in_stack_tl. auto. 
    repeat rewrite_stack_blocks. simpl. congruence.

- (* internal function *)
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'.
  destruct (zlt Ptrofs.max_unsigned (code_size (fn_code x0))); inv EQ1.
  monadInv EQ0. repeat destr_in EQ2. rewrite transl_code'_transl_code in EQ1.
  inv H0.
  unfold store_stack in *.
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl.
  intros [m1' [C D]].
  exploit Mem.storev_extends. eexact D. eexact H2. eauto. eauto.
  intros [m3' [P Q]].
  exploit frame_size_correct. eauto. intros X.
  exploit Mem.record_stack_blocks_extends; eauto.
  + unfold in_frame. simpl. intros ? [?|[]]; subst.
    repeat rewrite_stack_blocks. intro IFF.
    eapply Mem.in_frames_valid in IFF. eapply Mem.fresh_block_alloc in C.
    congruence.
  + intros bb ffi o k0 p [AA|[]]; inv AA. repeat rewrite_perms. destr.
    unfold frame_info_of_size_and_pubrange in Heqo; repeat destr_in Heqo. simpl. auto.
  + repeat rewrite_stack_blocks. inv CSC. congruence.
  + repeat rewrite_stack_blocks. rewrite SAMEADT. omega.
  + intros (m1'' & CC & DD).
    left; econstructor; split.
    apply plus_one. econstructor; eauto.
    simpl. rewrite Ptrofs.unsigned_zero. simpl. eauto.
    unfold exec_instr; simpl. rewrite Heqo.
    change Mptr with (chunk_of_type Tptr).
    rewrite ATLR. erewrite agree_sp. 2: eauto.
    (* edestruct check_alloc_frame_correct. *)
    (* red. unfold frame_info_of_size_and_pubrange in Heqo; repeat destr_in Heqo.  *)
    (* eauto. rewrite H4. *)
    rewrite C.
  simpl in P. rewrite Ptrofs.add_zero_l in P. rewrite P. rewrite CC.
  apply pred_dec_true.
  inv CSC. rewrite <- SAMEADT; auto.
  econstructor; eauto.
  unfold nextinstr. rewrite Pregmap.gss. repeat rewrite Pregmap.gso; auto with asmgen.
  rewrite ATPC. simpl. constructor; eauto.
  unfold fn_code. eapply code_tail_next_int. simpl in g. simpl. omega.
  constructor.
  apply agree_nextinstr. eapply agree_change_sp; eauto.
Transparent destroyed_at_function_entry.
apply agree_undef_regs with rs0; eauto.
  simpl; intros. apply Pregmap.gso; auto with asmgen. tauto.
  congruence.
  constructor.
  repeat rewrite_stack_blocks. simpl. intros. rewrite EQ0. simpl. Simplifs.
  repeat rewrite_stack_blocks. setoid_rewrite in_stack_cons.
  intros EQ0 b o k p.
  intros; repeat rewrite_perms. destr.
  apply SAMEPERM. rewrite EQ0. rewrite in_stack_cons. right.
  destruct H0 as [IFR|INS]; eauto.
  red in IFR. simpl in IFR. intuition congruence.
  repeat rewrite_stack_blocks. rewrite SAMEADT.
  intros EQ5 EQ6; rewrite EQ5 in EQ6; inv EQ6. auto.

- (* external function *)
  exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B.
  exploit extcall_arguments_match; eauto.
  intros [args' [C D]].
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [P [Q [R S]]]]].
  inv CSC. inv TTNP.
  edestruct (Mem.unrecord_stack_block_succeeds m') as (m2 & USB & STKEQ). rewrite_stack_blocks. eauto.
  edestruct Mem.unrecord_stack_block_extends as (m3' & USB' & EXT'). 2: apply USB. eauto. subst.
  left; econstructor; split.
  apply plus_one. eapply exec_step_external; eauto.
  
  { (* rs SP Tint *)
    erewrite agree_sp by eauto. rewrite <- H2 in *. simpl in *.
    edestruct init_sp_csc' as (b & EQsp). eauto. rewrite EQsp. constructor.
  }
  { (* rs RA Tint *)
    rewrite ATLR.
    eapply parent_ra_type; eauto.
  }
  { (* rs SP not Vundef *)
    erewrite agree_sp by eauto.
    rewrite <- H2 in *. simpl in *.
    edestruct init_sp_csc' as (b & EQsp). eauto. rewrite EQsp. congruence.
  }
  { (* rs RA not Vundef *)
    rewrite ATLR.
    eapply parent_ra_def; eauto.
  }
  red. rewrite <- SAMEADT, <- H2. constructor; auto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  unfold loc_external_result.
  clear. destruct (loc_result (ef_sig ef)); simpl; try split;
           apply preg_of_not_SP.
  rewrite ATLR. eapply has_code_parent_ra_after_call; eauto. inv HC; auto.
  subst.
  econstructor; eauto.
  unfold loc_external_result.
  apply agree_set_other; auto.
  apply agree_set_other; auto. apply agree_set_pair; auto.
  apply agree_undef_nondata_regs.
  apply agree_undef_regs_parallel; auto.
  repeat rewrite_stack_blocks. auto.  
  simpl; intros; intuition subst; reflexivity.
  rewrite_stack_blocks. intros. repeat rewrite_perms. eauto. rewrite <- SAMEADT; eauto. auto.
  repeat rewrite_stack_blocks; eauto. congruence.
  
- (* return *)
  inv STACKS. rewrite USB in H; inv H. simpl in *.
  right. split. omega. split. auto.
  econstructor; eauto. rewrite ATPC; eauto.
  inv CSC. inv TTNP. rewrite <- H in *. simpl in *.
  rewrite H3 in CallStackConsistency. repeat destr_in CallStackConsistency.
  revert AG. simpl. unfold current_frame_sp. simpl. rewrite BLOCKS. auto.
  congruence.
  rewrite_stack_blocks.
  intros. repeat rewrite_perms. apply SAMEPERM.
  eapply in_stack_tl; eauto.
Qed.

End WITHINITSPRA.

Lemma transf_initial_states:
  forall st1, Mach.initial_state prog st1 ->
         exists st2, Asm.initial_state tprog st2 /\ match_states Vnullptr st1 st2
                /\ has_code return_address_offset ge st1 
                /\ call_stack_consistency
                    ge signature_main
                    ((Some (make_singleton_frame_adt (Genv.genv_next ge) 0 0),nil) :: nil)
                                               st1.
Proof.
  intros. inversion H. unfold ge0 in *.
  econstructor; split. 
  - econstructor.
    eapply (Genv.init_mem_transf_partial TRANSF); eauto.
    eauto.
    rewrite (match_program_main TRANSF).
    rewrite symbols_preserved. eauto.
  - replace (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Ptrofs.zero)
    with (Vptr fb Ptrofs.zero).
    + split. econstructor; eauto.
      * econstructor; eauto.
      * apply Mem.extends_refl.
      * split.
        -- repeat rewrite_stack_blocks. simpl.
           unfold current_frame_sp. simpl. rewrite Pregmap.gss. rewnb. auto.
        -- repeat rewrite_stack_blocks. simpl. unfold current_frame_sp.  simpl. congruence.
        -- repeat rewrite_stack_blocks. simpl. unfold Tptr. destruct Archi.ptr64; auto.
        -- intros. rewrite Regmap.gi. auto.
      * tauto.
      * split; constructor.
        -- constructor.
        -- repeat rewrite_stack_blocks. simpl. constructor.
           rewnb. fold ge. reflexivity.
           constructor. simpl. constructor; auto. 
           replace (size_arguments signature_main) with 0.
           replace (Stacklayout.fe_ofs_arg) with 0. intros; omega. reflexivity.
           reflexivity.
        -- red. rewrite_stack_blocks. constructor; auto.
    + unfold Genv.symbol_address.
      rewrite (match_program_main TRANSF).
      rewrite symbols_preserved.
      unfold ge; rewrite H1. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states Vnullptr st1 st2 -> Mach.final_state st1 r -> Asm.final_state st2 r.
Proof.
  intros. inv H0. inv H. constructor. auto.
  assert (r0 = AX).
  { unfold loc_result in H1; destruct Archi.ptr64; compute in H1; congruence. }
  subst r0.
  generalize (preg_val _ _ _ AX AG). rewrite H2. intros LD; inv LD. auto.
Qed.

Hypothesis frame_correct:
  forall (fb : block) (f : Mach.function),
    Genv.find_funct_ptr ge fb = Some (Internal f) ->
    0 < Mach.fn_stacksize f.

Theorem transf_program_correct:
  forward_simulation (Mach.semantics2 return_address_offset prog)
                     (Asm.semantics tprog
                                    ((Some (make_singleton_frame_adt (Genv.genv_next ge) 0 0), nil) :: nil)).
Proof.
  eapply forward_simulation_star
  with (measure := measure)
         (match_states := fun s1 s2 =>
                            match_states Vnullptr s1 s2 /\
                            has_code return_address_offset ge s1 /\
                            call_stack_consistency
                              ge signature_main
                              ((Some (make_singleton_frame_adt (Genv.genv_next ge) 0 0), nil) :: nil) s1).
  - apply senv_preserved.
  - eexact transf_initial_states.
  - simpl; intros s1 s2 r (MS & HC & CSC) FS.
    eapply transf_final_states; eauto.
  - simpl; intros s1 t s1' STEP s2 (MS & HC & CSC).
    exploit step_simulation. 5: eexact STEP. all: eauto.
    + inversion 1.
    + apply Val.Vnullptr_has_type.
    + split; inversion 1.
    + intros [(S2' & PLUS & MS')|(MES & TR & MS')].
      * left; eexists; split; eauto. split; auto.
        split.
        eapply has_code_step; eauto.
        eapply csc_step; eauto.
        apply invalidate_frame2_tl_stack.
        apply invalidate_frame2_top_no_perm.
      * right; repeat split; eauto.
        eapply has_code_step; eauto.
        eapply csc_step; eauto.
        apply invalidate_frame2_tl_stack.
        apply invalidate_frame2_top_no_perm.
Qed.

End PRESERVATION.
