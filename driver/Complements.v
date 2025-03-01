(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Corollaries of the main semantic preservation theorem. *)

Require Import Classical.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Behaviors.
Require Import Csyntax.
Require Import Csem.
Require Import Cstrategy.
Require Import Clight.
Require Import Cminor.
Require Import RTL.
Require Import Asm.
Require Import Compiler.
Require Import Errors.

(** * Preservation of whole-program behaviors *)

(** From the simulation diagrams proved in file [Compiler]. it follows that
  whole-program observable behaviors are preserved in the following sense.
  First, every behavior of the generated assembly code is matched by
  a behavior of the source C code. *)

Section WITHEXTERNALCALLS.
Local Existing Instance Events.symbols_inject_instance.
Context `{external_calls_prf: Events.ExternalCalls (symbols_inject_instance := Events.symbols_inject_instance) }.
Context {i64_helpers_correct_prf: SplitLongproof.I64HelpersCorrect mem}.
Context `{memory_model_x_prf: !Unusedglobproof.Mem.MemoryModelX mem}.

Theorem transf_c_program_preservation:
  forall p tp beh,
  transf_c_program p = OK tp ->
    let init_stk := mk_init_stk tp in
  program_behaves (Asm.semantics tp init_stk) beh ->
  exists beh', program_behaves (Csem.semantics (fn_stack_requirements tp) p) beh' /\ behavior_improves beh' beh.
Proof.
  intros. eapply backward_simulation_behavior_improves; eauto.
  apply transf_c_program_correct; auto.
Qed.

(** As a corollary, if the source C code cannot go wrong, the behavior of the
  generated assembly code is one of the possible behaviors of the source C code. *)

Theorem transf_c_program_is_refinement:
  forall p tp,
  transf_c_program p = OK tp ->
  (forall beh, program_behaves (Csem.semantics (fn_stack_requirements tp) p) beh -> not_wrong beh) ->
    let init_stk := mk_init_stk tp in
  (forall beh, program_behaves (Asm.semantics tp init_stk) beh -> program_behaves (Csem.semantics (fn_stack_requirements tp) p) beh).
Proof.
  intros. eapply backward_simulation_same_safe_behavior; eauto.
  apply transf_c_program_correct; auto.
Qed.

(** If we consider the C evaluation strategy implemented by the compiler,
  we get stronger preservation results. *)

Theorem transf_cstrategy_program_preservation:
  forall p tp,
    transf_c_program p = OK tp ->
    let init_stk := mk_init_stk tp in
  (forall beh, program_behaves (Cstrategy.semantics (fn_stack_requirements tp) p) beh ->
     exists beh', program_behaves (Asm.semantics tp init_stk) beh' /\ behavior_improves beh beh')
/\(forall beh, program_behaves (Asm.semantics tp init_stk) beh ->
     exists beh', program_behaves (Cstrategy.semantics (fn_stack_requirements tp) p) beh' /\ behavior_improves beh' beh)
/\(forall beh, not_wrong beh ->
     program_behaves (Cstrategy.semantics (fn_stack_requirements tp) p) beh -> program_behaves (Asm.semantics tp init_stk) beh)
/\(forall beh,
     (forall beh', program_behaves (Cstrategy.semantics (fn_stack_requirements tp) p) beh' -> not_wrong beh') ->
     program_behaves (Asm.semantics tp init_stk) beh ->
     program_behaves (Cstrategy.semantics (fn_stack_requirements tp) p) beh).
Proof.
  intros p tp.
  assert (WBT: forall p, well_behaved_traces (Cstrategy.semantics (fn_stack_requirements tp) p)).
    intros. eapply ssr_well_behaved. apply Cstrategy.semantics_strongly_receptive.
  intros. 
  assert (MATCH: match_prog p tp) by (apply transf_c_program_match; auto).
  intuition auto.
  eapply forward_simulation_behavior_improves; eauto.
    apply (proj1 (cstrategy_semantic_preservation _ _ MATCH)).
  exploit @backward_simulation_behavior_improves.
    apply (proj2 (cstrategy_semantic_preservation _ _ MATCH)).
    eauto.
  intros [beh1 [A B]]. exists beh1; split; auto. rewrite atomic_behaviors; auto.
  eapply forward_simulation_same_safe_behavior; eauto.
    apply (proj1 (cstrategy_semantic_preservation _ _ MATCH)).
  exploit @backward_simulation_same_safe_behavior.
    apply (proj2 (cstrategy_semantic_preservation _ _ MATCH)).
    intros. rewrite <- atomic_behaviors in H2; eauto. eauto.
    intros. rewrite atomic_behaviors; auto.
Qed.

(** We can also use the alternate big-step semantics for [Cstrategy]
  to establish behaviors of the generated assembly code. *)

Theorem bigstep_cstrategy_preservation:
  forall p tp,
    transf_c_program p = OK tp ->
    let init_stk := mk_init_stk tp in
  (forall t r,
     Cstrategy.bigstep_program_terminates (fn_stack_requirements tp) p t r ->
     program_behaves (Asm.semantics tp init_stk) (Terminates t r))
/\(forall T,
     Cstrategy.bigstep_program_diverges (fn_stack_requirements tp) p T ->
       program_behaves (Asm.semantics tp init_stk) (Reacts T)
    \/ exists t, program_behaves (Asm.semantics tp init_stk) (Diverges t) /\ traceinf_prefix t T).
Proof.
  intros p tp TP init_sp. 
  split.
  - intros t r BPT.
    eapply transf_cstrategy_program_preservation; eauto. red; auto.
    apply behavior_bigstep_terminates with (Cstrategy.bigstep_semantics (fn_stack_requirements tp) p); auto.
    apply Cstrategy.bigstep_semantics_sound.
  - intros T BPD.
    exploit (behavior_bigstep_diverges (Cstrategy.bigstep_semantics_sound (fn_stack_requirements tp) p)). eassumption.
    intros [A | [t [A B]]].
    + left. apply transf_cstrategy_program_preservation with p; auto. red; auto.
    + right; exists t; split; auto. apply transf_cstrategy_program_preservation with p; auto. red; auto.
Qed.

(** * Satisfaction of specifications *)

(** The second additional results shows that if all executions
  of the source C program satisfies a given specification
  (a predicate on the observable behavior of the program),
  then all executions of the produced Asm program satisfy
  this specification as well.

  We first show this result for specifications that are stable
  under the [behavior_improves] relation. *)

Section SPECS_PRESERVED.

Variable spec: program_behavior int -> Prop.

Hypothesis spec_stable:
  forall beh1 beh2, behavior_improves beh1 beh2 -> spec beh1 -> spec beh2.

Theorem transf_c_program_preserves_spec:
  forall p tp,
    transf_c_program p = OK tp ->
    let init_stk := mk_init_stk tp in
    (forall beh, program_behaves (Csem.semantics (fn_stack_requirements tp) p) beh -> spec beh) ->
    (forall beh, program_behaves (Asm.semantics tp init_stk) beh -> spec beh).
Proof.
  intros.
  exploit transf_c_program_preservation; eauto. intros [beh' [A B]].
  apply spec_stable with beh'; auto.
Qed.

End SPECS_PRESERVED.

(** As a corollary, we obtain preservation of safety specifications:
  specifications that exclude "going wrong" behaviors. *)

Section SAFETY_PRESERVED.

Variable spec: program_behavior int -> Prop.

Hypothesis spec_safety:
  forall beh, spec beh -> not_wrong beh.

Theorem transf_c_program_preserves_safety_spec:
  forall p tp,
    transf_c_program p = OK tp ->
    let init_stk := mk_init_stk tp in
    (forall beh, program_behaves (Csem.semantics (fn_stack_requirements tp) p) beh -> spec beh) ->
    (forall beh, program_behaves (Asm.semantics tp init_stk) beh -> spec beh).
Proof.
  intros. eapply transf_c_program_preserves_spec; eauto.
  intros. destruct H2. congruence. destruct H2 as [t [EQ1 EQ2]].
  subst beh1. elim (spec_safety _ H3).
Qed.

End SAFETY_PRESERVED.

(** We also have preservation of liveness specifications:
  specifications that assert the existence of a prefix of the observable
  trace satisfying some conditions. *)

Section LIVENESS_PRESERVED.

Variable spec: trace -> Prop.

Definition liveness_spec_satisfied {RETVAL: Type} (b: program_behavior RETVAL) : Prop :=
  exists t, behavior_prefix t b /\ spec t.

Theorem transf_c_program_preserves_liveness_spec:
  forall p tp,
    transf_c_program p = OK tp ->
    let init_stk := mk_init_stk tp in
    (forall beh, program_behaves (Csem.semantics (fn_stack_requirements tp) p) beh -> liveness_spec_satisfied beh) ->
    (forall beh, program_behaves (Asm.semantics tp init_stk) beh -> liveness_spec_satisfied beh).
Proof.
  intros. eapply transf_c_program_preserves_spec; eauto.
  intros. destruct H3 as [t1 [A B]]. destruct H2.
  subst. exists t1; auto.
  destruct H2 as [t [C D]]. subst.
  destruct A as [b1 E]. destruct D as [b2 F].
  destruct b1; simpl in E; inv E.
  exists t1; split; auto.
  exists (behavior_app t0 b2); apply behavior_app_assoc.
Qed.

End LIVENESS_PRESERVED.

End WITHEXTERNALCALLS.
 