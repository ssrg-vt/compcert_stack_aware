(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Observable events, execution traces, and semantics of external calls. *)

Require Import String.
Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.

(** * Events and traces *)

(** The observable behaviour of programs is stated in terms of
  input/output events, which represent the actions of the program
  that the external world can observe.  CompCert leaves much flexibility as to
  the exact content of events: the only requirement is that they
  do not expose memory states nor pointer values
  (other than pointers to global variables), because these
  are not preserved literally during compilation.  For concreteness,
  we use the following type for events.  Each event represents either:

- A system call (e.g. an input/output operation), recording the
  name of the system call, its parameters, and its result.

- A volatile load from a global memory location, recording the chunk
  and address being read and the value just read.

- A volatile store to a global memory location, recording the chunk
  and address being written and the value stored there.

- An annotation, recording the text of the annotation and the values
  of the arguments.

  The values attached to these events are of the following form.
  As mentioned above, we do not expose pointer values directly.
  Pointers relative to a global variable are shown with the name
  of the variable instead of the block identifier.
*)

Inductive eventval: Type :=
  | EVint: int -> eventval
  | EVlong: int64 -> eventval
  | EVfloat: float -> eventval
  | EVsingle: float32 -> eventval
  | EVptr_global: ident -> ptrofs -> eventval.

Inductive event: Type :=
  | Event_syscall: string -> list eventval -> eventval -> event
  | Event_vload: memory_chunk -> ident -> ptrofs -> eventval -> event
  | Event_vstore: memory_chunk -> ident -> ptrofs -> eventval -> event
  | Event_annot: string -> list eventval -> event.

(** The dynamic semantics for programs collect traces of events.
  Traces are of two kinds: finite (type [trace]) or infinite (type [traceinf]). *)

Definition trace := list event.

Definition E0 : trace := nil.

Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

CoInductive traceinf : Type :=
  | Econsinf: event -> traceinf -> traceinf.

Fixpoint Eappinf (t: trace) (T: traceinf) {struct t} : traceinf :=
  match t with
  | nil => T
  | ev :: t' => Econsinf ev (Eappinf t' T)
  end.

(** Concatenation of traces is written [**] in the finite case
  or [***] in the infinite case. *)

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).

Lemma E0_left: forall t, E0 ** t = t.
Proof. auto. Qed.

Lemma E0_right: forall t, t ** E0 = t.
Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall t1 t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eapp_E0_inv: forall t1 t2, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0.
Proof (@app_eq_nil event).

Lemma E0_left_inf: forall T, E0 *** T = T.
Proof. auto. Qed.

Lemma Eappinf_assoc: forall t1 t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

Hint Rewrite E0_left E0_right Eapp_assoc
             E0_left_inf Eappinf_assoc: trace_rewrite.

Opaque trace E0 Eapp Eappinf.

(** The following [traceEq] tactic proves equalities between traces
  or infinite traces. *)

Ltac substTraceHyp :=
  match goal with
  | [ H: (@eq trace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac decomposeTraceEq :=
  match goal with
  | [ |- (_ ** _) = (_ ** _) ] =>
      apply (f_equal2 Eapp); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac traceEq :=
  repeat substTraceHyp; autorewrite with trace_rewrite; decomposeTraceEq.

(** Bisimilarity between infinite traces. *)

CoInductive traceinf_sim: traceinf -> traceinf -> Prop :=
  | traceinf_sim_cons: forall e T1 T2,
      traceinf_sim T1 T2 ->
      traceinf_sim (Econsinf e T1) (Econsinf e T2).

Lemma traceinf_sim_refl:
  forall T, traceinf_sim T T.
Proof.
  cofix COINDHYP; intros.
  destruct T. constructor. apply COINDHYP.
Qed.

Lemma traceinf_sim_sym:
  forall T1 T2, traceinf_sim T1 T2 -> traceinf_sim T2 T1.
Proof.
  cofix COINDHYP; intros. inv H; constructor; auto.
Qed.

Lemma traceinf_sim_trans:
  forall T1 T2 T3,
  traceinf_sim T1 T2 -> traceinf_sim T2 T3 -> traceinf_sim T1 T3.
Proof.
  cofix COINDHYP;intros. inv H; inv H0; constructor; eauto.
Qed.

CoInductive traceinf_sim': traceinf -> traceinf -> Prop :=
  | traceinf_sim'_cons: forall t T1 T2,
      t <> E0 -> traceinf_sim' T1 T2 -> traceinf_sim' (t *** T1) (t *** T2).

Lemma traceinf_sim'_sim:
  forall T1 T2, traceinf_sim' T1 T2 -> traceinf_sim T1 T2.
Proof.
  cofix COINDHYP; intros. inv H.
  destruct t. elim H0; auto.
Transparent Eappinf.
Transparent E0.
  simpl.
  destruct t. simpl. constructor. apply COINDHYP; auto.
  constructor. apply COINDHYP.
  constructor. unfold E0; congruence. auto.
Qed.

(** An alternate presentation of infinite traces as
  infinite concatenations of nonempty finite traces. *)

CoInductive traceinf': Type :=
  | Econsinf': forall (t: trace) (T: traceinf'), t <> E0 -> traceinf'.

Program Definition split_traceinf' (t: trace) (T: traceinf') (NE: t <> E0): event * traceinf' :=
  match t with
  | nil => _
  | e :: nil => (e, T)
  | e :: t' => (e, Econsinf' t' T _)
  end.
Next Obligation.
  elimtype False. elim NE. auto.
Qed.
Next Obligation.
  red; intro. elim (H e). rewrite H0. auto.
Qed.

CoFixpoint traceinf_of_traceinf' (T': traceinf') : traceinf :=
  match T' with
  | Econsinf' t T'' NOTEMPTY =>
      let (e, tl) := split_traceinf' t T'' NOTEMPTY in
      Econsinf e (traceinf_of_traceinf' tl)
  end.

Remark unroll_traceinf':
  forall T, T = match T with Econsinf' t T' NE => Econsinf' t T' NE end.
Proof.
  intros. destruct T; auto.
Qed.

Remark unroll_traceinf:
  forall T, T = match T with Econsinf t T' => Econsinf t T' end.
Proof.
  intros. destruct T; auto.
Qed.

Lemma traceinf_traceinf'_app:
  forall t T NE,
  traceinf_of_traceinf' (Econsinf' t T NE) = t *** traceinf_of_traceinf' T.
Proof.
  induction t.
  intros. elim NE. auto.
  intros. simpl.
  rewrite (unroll_traceinf (traceinf_of_traceinf' (Econsinf' (a :: t) T NE))).
  simpl. destruct t. auto.
Transparent Eappinf.
  simpl. f_equal. apply IHt.
Qed.

(** Prefixes of traces. *)

Definition trace_prefix (t1 t2: trace) :=
  exists t3, t2 = t1 ** t3.

Definition traceinf_prefix (t1: trace) (T2: traceinf) :=
  exists T3, T2 = t1 *** T3.

Lemma trace_prefix_app:
  forall t1 t2 t,
  trace_prefix t1 t2 ->
  trace_prefix (t ** t1) (t ** t2).
Proof.
  intros. destruct H as [t3 EQ]. exists t3. traceEq.
Qed.

Lemma traceinf_prefix_app:
  forall t1 T2 t,
  traceinf_prefix t1 T2 ->
  traceinf_prefix (t ** t1) (t *** T2).
Proof.
  intros. destruct H as [T3 EQ]. exists T3. subst T2. traceEq.
Qed.

(** * Relating values and event values *)

Set Implicit Arguments.

Section EVENTVAL.

(** Symbol environment used to translate between global variable names and their block identifiers. *)
Variable ge: Senv.t.

(** Translation between values and event values. *)

Inductive eventval_match: eventval -> typ -> val -> Prop :=
  | ev_match_int: forall i,
      eventval_match (EVint i) Tint (Vint i)
  | ev_match_long: forall i,
      eventval_match (EVlong i) Tlong (Vlong i)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) Tfloat (Vfloat f)
  | ev_match_single: forall f,
      eventval_match (EVsingle f) Tsingle (Vsingle f)
  | ev_match_ptr: forall id b ofs,
      Senv.public_symbol ge id = true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match (EVptr_global id ofs) Tptr (Vptr b ofs).

Inductive eventval_list_match: list eventval -> list typ -> list val -> Prop :=
  | evl_match_nil:
      eventval_list_match nil nil nil
  | evl_match_cons:
      forall ev1 evl ty1 tyl v1 vl,
      eventval_match ev1 ty1 v1 ->
      eventval_list_match evl tyl vl ->
      eventval_list_match (ev1::evl) (ty1::tyl) (v1::vl).

(** Some properties of these translation predicates. *)

Lemma eventval_match_type:
  forall ev ty v,
  eventval_match ev ty v -> Val.has_type v ty.
Proof.
  intros. inv H; simpl; auto. unfold Tptr; destruct Archi.ptr64; auto.
Qed.

Lemma eventval_list_match_length:
  forall evl tyl vl, eventval_list_match evl tyl vl -> List.length vl = List.length tyl.
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma eventval_match_lessdef:
  forall ev ty v1 v2,
  eventval_match ev ty v1 -> Val.lessdef v1 v2 -> eventval_match ev ty v2.
Proof.
  intros. inv H; inv H0; constructor; auto.
Qed.

Lemma eventval_list_match_lessdef:
  forall evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, Val.lessdef_list vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_lessdef; eauto. eauto.
Qed.

(** Determinism *)

Lemma eventval_match_determ_1:
  forall ev ty v1 v2, eventval_match ev ty v1 -> eventval_match ev ty v2 -> v1 = v2.
Proof.
  intros. inv H; inv H0; auto. congruence.
Qed.

Lemma eventval_match_determ_2:
  forall ev1 ev2 ty v, eventval_match ev1 ty v -> eventval_match ev2 ty v -> ev1 = ev2.
Proof.
  intros. inv H; inv H0; auto.
  decEq. eapply Senv.find_symbol_injective; eauto.
Qed.

Lemma eventval_list_match_determ_2:
  forall evl1 tyl vl, eventval_list_match evl1 tyl vl ->
  forall evl2, eventval_list_match evl2 tyl vl -> evl1 = evl2.
Proof.
  induction 1; intros. inv H. auto. inv H1. f_equal; eauto.
  eapply eventval_match_determ_2; eauto.
Qed.

(** Validity *)

Definition eventval_valid (ev: eventval) : Prop :=
  match ev with
  | EVint _ => True
  | EVlong _ => True
  | EVfloat _ => True
  | EVsingle _ => True
  | EVptr_global id ofs => Senv.public_symbol ge id = true
  end.

Definition eventval_type (ev: eventval) : typ :=
  match ev with
  | EVint _ => Tint
  | EVlong _ => Tlong
  | EVfloat _ => Tfloat
  | EVsingle _ => Tsingle
  | EVptr_global id ofs => Tptr
  end.

Lemma eventval_match_receptive:
  forall ev1 ty v1 ev2,
  eventval_match ev1 ty v1 ->
  eventval_valid ev1 -> eventval_valid ev2 -> eventval_type ev1 = eventval_type ev2 ->
  exists v2, eventval_match ev2 ty v2.
Proof.
  intros. unfold eventval_type, Tptr in H2. remember Archi.ptr64 as ptr64.
  inversion H; subst ev1 ty v1; clear H; destruct ev2; simpl in H2; inv H2.
- exists (Vint i0); constructor.
- simpl in H1; exploit Senv.public_symbol_exists; eauto. intros [b FS].
  exists (Vptr b i1); rewrite H3. constructor; auto.
- exists (Vlong i0); constructor.
- simpl in H1; exploit Senv.public_symbol_exists; eauto. intros [b FS].
  exists (Vptr b i1); rewrite H3; constructor; auto.
- exists (Vfloat f0); constructor.
- destruct Archi.ptr64; discriminate.
- exists (Vsingle f0); constructor; auto.
- destruct Archi.ptr64; discriminate.
- exists (Vint i); unfold Tptr; rewrite H5; constructor.
- exists (Vlong i); unfold Tptr; rewrite H5; constructor.
- destruct Archi.ptr64; discriminate.
- destruct Archi.ptr64; discriminate.
- exploit Senv.public_symbol_exists. eexact H1. intros [b' FS].
  exists (Vptr b' i0); constructor; auto.
Qed.

Lemma eventval_match_valid:
  forall ev ty v, eventval_match ev ty v -> eventval_valid ev.
Proof.
  destruct 1; simpl; auto.
Qed.

Lemma eventval_match_same_type:
  forall ev1 ty v1 ev2 v2,
  eventval_match ev1 ty v1 -> eventval_match ev2 ty v2 -> eventval_type ev1 = eventval_type ev2.
Proof.
  destruct 1; intros EV; inv EV; auto.
Qed.

End EVENTVAL.

(** Invariance under changes to the global environment *)

Section EVENTVAL_INV.

Variables ge1 ge2: Senv.t.

Hypothesis public_preserved:
  forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id.

Lemma eventval_valid_preserved:
  forall ev, eventval_valid ge1 ev -> eventval_valid ge2 ev.
Proof.
  intros. destruct ev; simpl in *; auto. rewrite <- H; auto.
Qed.

Hypothesis symbols_preserved:
  forall id, Senv.find_symbol ge2 id = Senv.find_symbol ge1 id.

Lemma eventval_match_preserved:
  forall ev ty v,
  eventval_match ge1 ev ty v -> eventval_match ge2 ev ty v.
Proof.
  induction 1; constructor; auto.
  rewrite public_preserved; auto.
  rewrite symbols_preserved; auto.
Qed.

Lemma eventval_list_match_preserved:
  forall evl tyl vl,
  eventval_list_match ge1 evl tyl vl -> eventval_list_match ge2 evl tyl vl.
Proof.
  induction 1; constructor; auto. eapply eventval_match_preserved; eauto.
Qed.

End EVENTVAL_INV.

(** Compatibility with memory injections *)

Section EVENTVAL_INJECT.

Variable f: block -> option (block * Z).
Variable ge1 ge2: Senv.t.

Definition symbols_inject : Prop :=
   (forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id)
/\ (forall id b1 b2 delta,
     f b1 = Some(b2, delta) -> Senv.find_symbol ge1 id = Some b1 ->
     delta = 0 /\ Senv.find_symbol ge2 id = Some b2)
/\ (forall id b1,
     Senv.public_symbol ge1 id = true -> Senv.find_symbol ge1 id = Some b1 ->
     exists b2, f b1 = Some(b2, 0) /\ Senv.find_symbol ge2 id = Some b2)
/\ (forall b1 b2 delta,
     f b1 = Some(b2, delta) ->
     Senv.block_is_volatile ge2 b2 = Senv.block_is_volatile ge1 b1).

Hypothesis symb_inj: symbols_inject.

Lemma eventval_match_inject:
  forall ev ty v1 v2,
  eventval_match ge1 ev ty v1 -> Val.inject f v1 v2 -> eventval_match ge2 ev ty v2.
Proof.
  intros. inv H; inv H0; try constructor; auto.
  destruct symb_inj as (A & B & C & D). exploit C; eauto. intros [b3 [EQ FS]]. rewrite H4 in EQ; inv EQ.
  rewrite Ptrofs.add_zero. constructor; auto. rewrite A; auto.
Qed.

Lemma eventval_match_inject_2:
  forall ev ty v1,
  eventval_match ge1 ev ty v1 ->
  exists v2, eventval_match ge2 ev ty v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H; try (econstructor; split; eauto; constructor; fail).
  destruct symb_inj as (A & B & C & D). exploit C; eauto. intros [b2 [EQ FS]].
  exists (Vptr b2 ofs); split. econstructor; eauto.
  econstructor; eauto. rewrite Ptrofs.add_zero; auto.
Qed.

Lemma eventval_list_match_inject:
  forall evl tyl vl1, eventval_list_match ge1 evl tyl vl1 ->
  forall vl2, Val.inject_list f vl1 vl2 -> eventval_list_match ge2 evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_inject; eauto. eauto.
Qed.

End EVENTVAL_INJECT.

(** * Matching traces. *)

Section MATCH_TRACES.

Variable ge: Senv.t.

(** Matching between traces corresponding to single transitions.
  Arguments (provided by the program) must be equal.
  Results (provided by the outside world) can vary as long as they
  can be converted safely to values. *)

Inductive match_traces: trace -> trace -> Prop :=
  | match_traces_E0:
      match_traces nil nil
  | match_traces_syscall: forall id args res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_syscall id args res1 :: nil) (Event_syscall id args res2 :: nil)
  | match_traces_vload: forall chunk id ofs res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_vload chunk id ofs res1 :: nil) (Event_vload chunk id ofs res2 :: nil)
  | match_traces_vstore: forall chunk id ofs arg,
      match_traces (Event_vstore chunk id ofs arg :: nil) (Event_vstore chunk id ofs arg :: nil)
  | match_traces_annot: forall id args,
      match_traces (Event_annot id args :: nil) (Event_annot id args :: nil).

End MATCH_TRACES.

(** Invariance by change of global environment *)

Section MATCH_TRACES_INV.

Variables ge1 ge2: Senv.t.

Hypothesis public_preserved:
  forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id.

Lemma match_traces_preserved:
  forall t1 t2, match_traces ge1 t1 t2 -> match_traces ge2 t1 t2.
Proof.
  induction 1; constructor; auto; eapply eventval_valid_preserved; eauto.
Qed.

End MATCH_TRACES_INV.

(** An output trace is a trace composed only of output events,
  that is, events that do not take any result from the outside world. *)

Definition output_event (ev: event) : Prop :=
  match ev with
  | Event_syscall _ _ _ => False
  | Event_vload _ _ _ _ => False
  | Event_vstore _ _ _ _ => True
  | Event_annot _ _ => True
  end.

Fixpoint output_trace (t: trace) : Prop :=
  match t with
  | nil => True
  | ev :: t' => output_event ev /\ output_trace t'
  end.

(** * Semantics of volatile memory accesses *)

Section WITHMEMORYMODELOPS.
Context `{memory_model_ops: Mem.MemoryModelOps}.

Inductive volatile_load (ge: Senv.t):
                   memory_chunk -> mem -> block -> ptrofs -> trace -> val -> Prop :=
  | volatile_load_vol: forall chunk m b ofs id ev v,
      Senv.block_is_volatile ge b = Some true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) v ->
      volatile_load ge chunk m b ofs
                      (Event_vload chunk id ofs ev :: nil)
                      (Val.load_result chunk v)
  | volatile_load_nonvol: forall chunk m b ofs v,
      Senv.block_is_volatile ge b = Some false ->
      Mem.load chunk m b (Ptrofs.unsigned ofs) = Some v ->
      volatile_load ge chunk m b ofs E0 v.

Inductive volatile_store (ge: Senv.t):
                  memory_chunk -> mem -> block -> ptrofs -> val -> trace -> mem -> Prop :=
  | volatile_store_vol: forall chunk m b ofs id ev v,
      Senv.block_is_volatile ge b = Some true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) (Val.load_result chunk v) ->
      volatile_store ge chunk m b ofs v
                      (Event_vstore chunk id ofs ev :: nil)
                      m
  | volatile_store_nonvol: forall chunk m b ofs v m',
      Senv.block_is_volatile ge b = Some false ->
      Mem.store chunk m b (Ptrofs.unsigned ofs) v = Some m' ->
      volatile_store ge chunk m b ofs v E0 m'.

End WITHMEMORYMODELOPS.

(** * Semantics of external functions *)

(** For each external function, its behavior is defined by a predicate relating:
- the global symbol environment
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).
*)

Definition extcall_sem `{memory_model_ops: Mem.MemoryModelOps} : Type :=
  Senv.t -> list val -> mem -> trace -> val -> mem -> Prop.

(** We now specify the expected properties of this predicate. *)

Section WITHMEMORYMODEL.
Context `{memory_model_prf: Mem.MemoryModel}.

Definition loc_out_of_bounds (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Nonempty.

Definition loc_not_writable (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Writable.

Definition loc_unmapped (f: meminj) (b: block) (ofs: Z): Prop :=
  f b = None.

Definition loc_out_of_reach (f: meminj) (m: mem) (b: block) (ofs: Z): Prop :=
  forall b0 delta,
  f b0 = Some(b, delta) -> ~Mem.perm m b0 (ofs - delta) Max Nonempty.

Definition inject_separated (f f': meminj) (m1 m2: mem): Prop :=
  forall b1 b2 delta,
  f b1 = None -> f' b1 = Some(b2, delta) ->
  ~Mem.valid_block m1 b1 /\ ~Mem.valid_block m2 b2.

Definition meminj_preserves_globals' (ge: Senv.t) (f: block -> option (block * Z)) : Prop :=
     (forall id b, Senv.find_symbol ge id = Some b -> f b = Some(b, 0)) /\
     (forall b1 b2 delta, f b1 = Some (b2, delta) -> Senv.block_is_volatile ge b2 = Senv.block_is_volatile ge b1).

Lemma meminj_preserves_globals'_symbols_inject (ge: Senv.t) (f: block -> option (block * Z)):
  meminj_preserves_globals' ge f ->
  symbols_inject f ge ge.
Proof.
  unfold meminj_preserves_globals'.
  intros (A & B).
  repeat split; intros.
  + simpl in H0. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H0. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H0. exists b1; split; eauto.
  + eauto.
Qed.

Class SymbolsInject: Type :=
  {
    symbols_inject' (f: block -> option (block * Z)) (ge1 ge2: Senv.t):
      Prop;
    meminj_preserves_globals'_symbols_inject' ge f:
      meminj_preserves_globals' ge f ->
      symbols_inject' f ge ge;
    symbols_inject'_symbols_inject f ge1 ge2:
      symbols_inject' f ge1 ge2 ->
      symbols_inject f ge1 ge2
  }.

Program Definition meminj_preserves_globals'_instance:
  SymbolsInject :=
  {|
    symbols_inject' f ge1 ge2 :=
      meminj_preserves_globals' ge1 f /\ ge1 = ge2
  |}.
Next Obligation.
  apply meminj_preserves_globals'_symbols_inject.
  assumption.
Qed.

(* Needed by Unusedglobproof. *)
Program Definition symbols_inject_instance:
  SymbolsInject :=
  {|
    symbols_inject' := symbols_inject
  |}.
Next Obligation.
  apply meminj_preserves_globals'_symbols_inject.
  assumption.
Qed.

Context `{symbols_inject'_instance: SymbolsInject}.

Record extcall_properties (sem: extcall_sem) (sg: signature) : Prop :=
  mk_extcall_properties {

(** The return value of an external call must agree with its signature. *)
  ec_well_typed:
    forall ge vargs m1 t vres m2,
    sem ge vargs m1 t vres m2 ->
    Val.has_type vres (proj_sig_res sg);

(** The semantics is invariant under change of global environment that preserves symbols. *)
  ec_symbols_preserved:
    forall ge1 ge2 vargs m1 t vres m2,
    Senv.equiv ge1 ge2 ->
    sem ge1 vargs m1 t vres m2 ->
    sem ge2 vargs m1 t vres m2;

(** External calls cannot invalidate memory blocks.  (Remember that
  freeing a block does not invalidate its block identifier.) *)
  ec_valid_block:
    forall ge vargs m1 t vres m2 b,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b;

(** External calls cannot increase the max permissions of a valid block.
    They can decrease the max permissions, e.g. by freeing. *)
  ec_max_perm:
    forall ge vargs m1 t vres m2 b ofs p,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p;

(** External call cannot modify memory unless they have [Max, Writable]
   permissions. *)
  ec_readonly:
    forall ge vargs m1 t vres m2,
    sem ge vargs m1 t vres m2 ->
    Mem.unchanged_on (loc_not_writable m1) m1 m2;

(** External calls must commute with memory extensions, in the
  following sense. *)
  ec_mem_extends {perminj: InjectPerm}:
    forall ge vargs m1 t vres m2 m1' vargs',
    sem ge vargs m1 t vres m2 ->
    Mem.extends m1 m1' ->
    Val.lessdef_list vargs vargs' ->
    exists vres', exists m2',
       sem ge vargs' m1' t vres' m2'
    /\ Val.lessdef vres vres'
    /\ Mem.extends m2 m2'
    /\ Mem.unchanged_on (loc_out_of_bounds m1) m1' m2';

(** External calls must commute with memory injections,
  in the following sense. *)
  ec_mem_inject {perminj: InjectPerm}:
    forall ge1 ge2 vargs m1 t vres m2 f g m1' vargs',
    symbols_inject' f ge1 ge2 ->
    sem ge1 vargs m1 t vres m2 ->
    Mem.inject f g m1 m1' ->
    Val.inject_list f vargs vargs' ->
    exists f', exists vres', exists m2',
       sem ge2 vargs' m1' t vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' g m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1';

  (* ec_unchanged_on: *)
  (*   forall ge m1 m2 *)
  (*     (UNCH: Mem.unchanged_on (fun _ _ => True) m1 m2) *)
  (*     (SH: same_head (Mem.perm m1) (Mem.stack m1) (Mem.stack m2)) *)
  (*     (NB: Mem.nextblock m1 = Mem.nextblock m2) *)
  (*     args res t m1' *)
  (*     (SEM1: sem ge args m1 res t m1'), *)
  (*   exists m2', *)
  (*     sem ge args m2 res t m2' *)
  (*     /\ Mem.unchanged_on (fun _ _ => True) m1' m2' *)
  (*     /\ Mem.nextblock m1' = Mem.nextblock m2'; *)

  
(** External calls produce at most one event. *)
  ec_trace_length:
    forall ge vargs m t vres m',
    sem ge vargs m t vres m' -> (length t <= 1)%nat;

(** External calls must be receptive to changes of traces by another, matching trace. *)
  ec_receptive:
    forall ge vargs m t1 vres1 m1 t2,
    sem ge vargs m t1 vres1 m1 -> match_traces ge t1 t2 ->
    exists vres2, exists m2, sem ge vargs m t2 vres2 m2;

(** External calls must be deterministic up to matching between traces. *)
  ec_determ:
    forall ge vargs m t1 vres1 m1 t2 vres2 m2,
    sem ge vargs m t1 vres1 m1 -> sem ge vargs m t2 vres2 m2 ->
    match_traces ge t1 t2 /\ (t1 = t2 -> vres1 = vres2 /\ m1 = m2);

  ec_unchanged_on_private_stack:
    forall ge vargs m1 t vres m2,
      sem ge vargs m1 t vres m2 ->
      Mem.unchanged_on
        (fun b o => ~ stack_access (Mem.stack m1) b o (o+1))
        m1 m2;

  ec_perm_frames:
    forall ge args m1 t res m2,
      sem ge args m1 t res m2 ->
      forall b o k p,
        in_stack (Mem.stack m1) b ->
        Mem.perm m2 b o k p <-> Mem.perm m1 b o k p;

  ec_perm_unchanged:
    forall ge args m1 t res m2,
      sem ge args m1 t res m2 ->
      forall b o k p,
        Mem.valid_block m1 b ->
        (forall p, Mem.perm m1 b o k p -> ~ perm_order p Freeable) ->
        Mem.perm m2 b o k p <-> Mem.perm m1 b o k p;
  
  ec_stack_blocks:
    forall ge vargs m1 t vres m2,
      sem ge vargs m1 t vres m2 ->
      Mem.stack m1 = Mem.stack m2;
}.


(** ** Semantics of volatile loads *)

Inductive volatile_load_sem (chunk: memory_chunk) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_load_sem_intro: forall b ofs m t v,
      volatile_load ge chunk m b ofs t v ->
      volatile_load_sem chunk ge (Vptr b ofs :: nil) m t v m.

Lemma volatile_load_preserved:
  forall ge1 ge2 chunk m b ofs t v,
  Senv.equiv ge1 ge2 ->
  volatile_load ge1 chunk m b ofs t v ->
  volatile_load ge2 chunk m b ofs t v.
Proof.
  intros. destruct H as (_ & A & B & C). inv H0; constructor; auto.
  rewrite C; auto.
  rewrite A; auto.
  eapply eventval_match_preserved; eauto.
  rewrite C; auto.
Qed.

Lemma volatile_load_extends{perminj: InjectPerm}:
  forall ge chunk m b ofs t v m',
  volatile_load ge chunk m b ofs t v ->
  Mem.extends m m' ->
  exists v', volatile_load ge chunk m' b ofs t v' /\ Val.lessdef v v'.
Proof.
  intros. inv H.
  econstructor; split; eauto. econstructor; eauto.
  exploit Mem.load_extends; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
Qed.

Lemma volatile_load_inject {perminj: InjectPerm}:
  forall ge1 ge2 f g chunk m b ofs t v b' ofs' m',
  symbols_inject f ge1 ge2 ->
  volatile_load ge1 chunk m b ofs t v ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  Mem.inject f g m m' ->
  exists v', volatile_load ge2 chunk m' b' ofs' t v' /\ Val.inject f v v'.
Proof.
  intros until m'; intros SI VL VI MI. generalize SI; intros (A & B & C & D).
  inv VL.
- (* volatile load *)
  inv VI. exploit B; eauto. intros [U V]. subst delta.
  exploit eventval_match_inject_2; eauto. intros (v2 & X & Y).
  rewrite Ptrofs.add_zero. exists (Val.load_result chunk v2); split.
  constructor; auto.
  erewrite D; eauto.
  apply Val.load_result_inject. auto.
- (* normal load *)
  exploit Mem.loadv_inject; eauto. simpl; eauto. simpl; intros (v2 & X & Y).
  exists v2; split; auto.
  constructor; auto.
  inv VI. erewrite D; eauto.
Qed.

Lemma volatile_load_receptive:
  forall ge chunk m b ofs t1 t2 v1,
  volatile_load ge chunk m b ofs t1 v1 -> match_traces ge t1 t2 ->
  exists v2, volatile_load ge chunk m b ofs t2 v2.
Proof.
  intros. inv H; inv H0.
  exploit eventval_match_receptive; eauto. intros [v' EM].
  exists (Val.load_result chunk v'). constructor; auto.
  exists v1; constructor; auto.
Qed.

Lemma volatile_load_ok:
  forall chunk,
  extcall_properties (volatile_load_sem chunk)
                     (mksignature (Tptr :: nil) (Some (type_of_chunk chunk)) cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- unfold proj_sig_res; simpl. inv H. inv H0. apply Val.load_result_type.
  eapply Mem.load_type; eauto.
(* symbols *)
- inv H0. constructor. eapply volatile_load_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* max perms *)
- inv H; auto.
(* readonly *)
- inv H. apply Mem.unchanged_on_refl.
(* mem extends *)
- inv H. inv H1. inv H6. inv H4.
  exploit volatile_load_extends; eauto. intros [v' [A B]].
  exists v'; exists m1'; intuition. constructor; auto.
(* mem injects *)
- apply symbols_inject'_symbols_inject in H.
  inv H0. inv H2. inv H7. inversion H5; subst.
  exploit volatile_load_inject; eauto. intros [v' [A B]].
  exists f; exists v'; exists m1'; intuition. constructor; auto.
  red; intros. congruence.
(* trace length *)
- inv H; inv H0; simpl; omega.
(* receptive *)
- inv H. exploit volatile_load_receptive; eauto. intros [v2 A].
  exists v2; exists m1; constructor; auto.
(* determ *)
- inv H; inv H0. inv H1; inv H7; try congruence.
  assert (id = id0) by (eapply Senv.find_symbol_injective; eauto). subst id0.
  split. constructor.
  eapply eventval_match_valid; eauto.
  eapply eventval_match_valid; eauto.
  eapply eventval_match_same_type; eauto.
  intros EQ; inv EQ.
  assert (v = v0) by (eapply eventval_match_determ_1; eauto). subst v0.
  auto.
  split. constructor. intuition congruence.
- inv H. inv H0; apply Mem.unchanged_on_refl.
- inv H. tauto.
- inv H. tauto.
- inv H; inv H0; auto.
Qed.

(** ** Semantics of volatile stores *)

Inductive volatile_store_sem (chunk: memory_chunk) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_store_sem_intro: forall b ofs m1 v t m2,
      volatile_store ge chunk m1 b ofs v t m2 ->
      volatile_store_sem chunk ge (Vptr b ofs :: v :: nil) m1 t Vundef m2.

Lemma volatile_store_preserved:
  forall ge1 ge2 chunk m1 b ofs v t m2,
  Senv.equiv ge1 ge2 ->
  volatile_store ge1 chunk m1 b ofs v t m2 ->
  volatile_store ge2 chunk m1 b ofs v t m2.
Proof.
  intros. destruct H as (_ & A & B & C). inv H0; constructor; auto.
  rewrite C; auto.
  rewrite A; auto.
  eapply eventval_match_preserved; eauto.
  rewrite C; auto.
Qed.

Lemma volatile_store_readonly:
  forall ge chunk1 m1 b1 ofs1 v t m2,
  volatile_store ge chunk1 m1 b1 ofs1 v t m2 ->
  Mem.unchanged_on (loc_not_writable m1) m1 m2.
Proof.
  intros. inv H.
  apply Mem.unchanged_on_refl.
  eapply Mem.store_unchanged_on; eauto.
  exploit Mem.store_valid_access_3; eauto. intros [P Q].
  intros. unfold loc_not_writable. red; intros. elim H2.
  apply Mem.perm_cur_max. apply P. auto.
Qed.

Lemma volatile_store_extends {perminj: InjectPerm}:
  forall ge chunk m1 b ofs v t m2 m1' v',
    volatile_store ge chunk m1 b ofs v t m2 ->
    Mem.extends m1 m1' ->
    Val.lessdef v v' ->
    exists m2',
      volatile_store ge chunk m1' b ofs v' t m2'
      /\ Mem.extends m2 m2'
      /\ Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'.
Proof.
  intros. inv H.
  - econstructor; split. econstructor; eauto.
    eapply eventval_match_lessdef; eauto. apply Val.load_result_lessdef; auto.
    split; auto with mem.
  - exploit Mem.store_within_extends; eauto. intros [m2' [A B]].
    exists m2'; repeat (split; auto).
    + econstructor; eauto.
    + eapply Mem.store_unchanged_on; eauto.
      unfold loc_out_of_bounds; intros.
      assert (Mem.perm m1 b i Max Nonempty).
      { apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
        exploit Mem.store_valid_access_3. eexact H3. intros [P Q]. eauto. }
      tauto.
Qed.

Lemma volatile_store_inject {perminj: InjectPerm}:
  forall ge1 ge2 f g chunk m1 b ofs v t m2 m1' b' ofs' v',
  symbols_inject f ge1 ge2 ->
  volatile_store ge1 chunk m1 b ofs v t m2 ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  Val.inject f v v' ->
  Mem.inject f g m1 m1' ->
  exists m2',
       volatile_store ge2 chunk m1' b' ofs' v' t m2'
    /\ Mem.inject f g m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'.
Proof.
  intros until v'; intros SI VS AI VI MI.
  generalize SI; intros (P & Q & R & S).
  inv VS.
- (* volatile store *)
  inv AI. exploit Q; eauto. intros [A B]. subst delta.
  rewrite Ptrofs.add_zero. exists m1'; split.
  constructor; auto. erewrite S; eauto.
  eapply eventval_match_inject; eauto. apply Val.load_result_inject. auto.
  intuition auto with mem.
- (* normal store *)
  inversion AI; subst.
  assert (Mem.storev chunk m1 (Vptr b ofs) v = Some m2). simpl; auto.
  exploit Mem.storev_mapped_inject; eauto. intros [m2' [A B]].
  exists m2'; repeat (split; auto).
  + constructor; auto. erewrite S; eauto.
  + eapply Mem.store_unchanged_on; eauto.
    unfold loc_unmapped; intros. inv AI; congruence.
  + eapply Mem.store_unchanged_on; eauto.
    unfold loc_out_of_reach; intros. red; intros. simpl in A.
    assert (EQ: Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) = Ptrofs.unsigned ofs + delta)
      by (eapply Mem.address_inject; eauto with mem).
    rewrite EQ in *.
    eelim H3; eauto.
    exploit Mem.store_valid_access_3. eexact H0. intros [X Y].
    apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
    apply X. omega.
Qed.

Lemma volatile_store_receptive:
  forall ge chunk m b ofs v t1 m1 t2,
  volatile_store ge chunk m b ofs v t1 m1 -> match_traces ge t1 t2 -> t1 = t2.
Proof.
  intros. inv H; inv H0; auto.
Qed.

Lemma volatile_store_ok:
  forall chunk,
  extcall_properties (volatile_store_sem chunk)
                     (mksignature (Tptr :: type_of_chunk chunk :: nil) None cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- unfold proj_sig_res; simpl. inv H; constructor.
(* symbols preserved *)
- inv H0. constructor. eapply volatile_store_preserved; eauto.
(* valid block *)
- inv H. inv H1. auto. eauto with mem.
(* perms *)
- inv H. inv H2. auto. eauto with mem.
(* readonly *)
- inv H. eapply volatile_store_readonly; eauto.
(* mem extends*)
- inv H. inv H1. inv H6. inv H7. inv H4.
  exploit volatile_store_extends; eauto. intros [m2' [A [B C]]].
  exists Vundef; exists m2'; intuition. constructor; auto.
(* mem inject *)
- apply symbols_inject'_symbols_inject in H.
  inv H0. inv H2. inv H7. inv H8. inversion H5; subst.
  exploit volatile_store_inject; eauto. intros [m2' [A [B [C D]]]].
  exists f; exists Vundef; exists m2'; intuition. constructor; auto. red; intros; congruence.
(* trace length *)
- inv H; inv H0; simpl; omega.
(* receptive *)
- assert (t1 = t2). inv H. eapply volatile_store_receptive; eauto.
  subst t2; exists vres1; exists m1; auto.
(* determ *)
- inv H; inv H0. inv H1; inv H8; try congruence.
  assert (id = id0) by (eapply Senv.find_symbol_injective; eauto). subst id0.
  assert (ev = ev0) by (eapply eventval_match_determ_2; eauto). subst ev0.
  split. constructor. auto.
  split. constructor. intuition congruence.
- inv H. inv H0. apply Mem.unchanged_on_refl.
  eapply Mem.store_unchanged_on. eauto.
  intros. intro A; apply A; clear A.
  apply Mem.store_valid_access_3 in H1. destruct H1 as (A & B & C).
  eapply stack_access_inside. apply C. constructor. omega. omega.
- inv H.  inv H1. tauto.
  split; intros. eapply Mem.perm_store_2; eauto. eapply Mem.perm_store_1; eauto.
- inv H. inv H2. tauto.
  split; intros. eapply Mem.perm_store_2; eauto. eapply Mem.perm_store_1; eauto.
- inv H. inv H0. auto.
  symmetry; eapply Mem.store_stack_blocks; eauto.
Qed.

(** ** Semantics of dynamic memory allocation (malloc) *)

Inductive extcall_malloc_sem (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_malloc_sem_intro: forall sz m m' b m'',
      Mem.alloc m (- size_chunk Mptr) (Ptrofs.unsigned sz) = (m', b) ->
      Mem.store Mptr m' b (- size_chunk Mptr) (Vptrofs sz) = Some m'' ->
      extcall_malloc_sem ge (Vptrofs sz :: nil) m E0 (Vptr b Ptrofs.zero) m''.

Lemma extcall_malloc_ok:
  extcall_properties extcall_malloc_sem
                     (mksignature (Tptr :: nil) (Some Tptr) cc_default).
Proof.
  assert (UNCHANGED:
    forall (P: block -> Z -> Prop) m lo hi v m' b m'',
    Mem.alloc m lo hi = (m', b) ->
    Mem.store Mptr m' b lo v = Some m'' ->
    Mem.unchanged_on P m m'').
  {
    intros.
    apply Mem.unchanged_on_implies with (fun b1 ofs1 => b1 <> b).
    apply Mem.unchanged_on_trans with m'. 
    eapply Mem.alloc_unchanged_on; eauto.
    eapply Mem.store_unchanged_on; eauto.
    intros. eapply Mem.valid_not_valid_diff; eauto with mem.
  }
  constructor; intros.
(* well typed *)
- inv H. unfold proj_sig_res, Tptr; simpl. destruct Archi.ptr64; auto.
(* symbols preserved *)
- inv H0; econstructor; eauto.
(* valid block *)
- inv H. eauto with mem.
(* perms *)
- inv H. exploit Mem.perm_alloc_inv. eauto. eapply Mem.perm_store_2; eauto.
  rewrite dec_eq_false. auto.
  apply Mem.valid_not_valid_diff with m1; eauto with mem.
(* readonly *)
- inv H. eapply UNCHANGED; eauto.
(* mem extends *)
- inv H. inv H1. inv H7.
  assert (SZ: v2 = Vptrofs sz).
  { unfold Vptrofs in *. destruct Archi.ptr64; inv H5; auto. } 
  subst v2.
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.
  intros [m3' [A B]].
  exploit Mem.store_within_extends. eexact B. eauto. eauto.
  intros [m2' [C D]].
  exists (Vptr b Ptrofs.zero); exists m2'; intuition.
  econstructor; eauto.
  eapply UNCHANGED; eauto.
(* mem injects *)
- inv H0. inv H2. inv H8.
  assert (SZ: v' = Vptrofs sz).
  { unfold Vptrofs in *. destruct Archi.ptr64; inv H6; auto. } 
  subst v'.
  exploit Mem.alloc_parallel_inject; eauto. apply Zle_refl. apply Zle_refl.
  intros [f' [m3' [b' [ALLOC [A [B [C D]]]]]]].
  exploit Mem.store_mapped_inject. eexact A. eauto. eauto.
  instantiate (1 := Vptrofs sz). unfold Vptrofs; destruct Archi.ptr64; constructor.
  rewrite Zplus_0_r. intros [m2' [E G]].
  exists f'; exists (Vptr b' Ptrofs.zero); exists m2'; intuition auto.
  econstructor; eauto.
  econstructor. eauto. auto.
  eapply UNCHANGED; eauto.
  eapply UNCHANGED; eauto.
  red; intros. destruct (eq_block b1 b).
  subst b1. rewrite C in H2. inv H2. eauto with mem.
  rewrite D in H2 by auto. congruence.
(* trace length *)
- inv H; simpl; omega.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
- inv H. simple inversion H0.
  assert (EQ2: sz0 = sz).
  { unfold Vptrofs in H4; destruct Archi.ptr64 eqn:SF.
    rewrite <- (Ptrofs.of_int64_to_int64 SF sz0), <- (Ptrofs.of_int64_to_int64 SF sz). congruence.
    rewrite <- (Ptrofs.of_int_to_int SF sz0), <- (Ptrofs.of_int_to_int SF sz). congruence.
  }
  subst. 
  split. constructor. intuition congruence.
- inv H.
  eapply Mem.unchanged_on_trans. eapply Mem.alloc_unchanged_on. eauto.
  eapply Mem.store_unchanged_on. eauto. intros.
  intro A; apply A.
  exploit Mem.invalid_block_stack_access. eapply Mem.fresh_block_alloc; eauto.
  eauto.
- inv H.  
  assert (b <> b0).
  intro; subst.
  eapply Mem.in_frames_valid in H0. eapply Mem.fresh_block_alloc in H0; eauto.
  split; intros.
  eapply Mem.perm_alloc_4; eauto.
  eapply Mem.perm_store_2; eauto.
  eapply Mem.perm_store_1; eauto.
  eapply Mem.perm_alloc_1; eauto.
- inv H.  
  assert (b <> b0).  intro; subst.
  eapply Mem.fresh_block_alloc in H0; eauto.
  split; intros.
  eapply Mem.perm_alloc_4; eauto.
  eapply Mem.perm_store_2; eauto.
  eapply Mem.perm_store_1; eauto.
  eapply Mem.perm_alloc_1; eauto.
- inv H.
  rewrite  (Mem.store_stack_blocks _ _ _ _ _ _ H1).
  symmetry; eapply Mem.alloc_stack_blocks; eauto.
Qed.

(** ** Semantics of dynamic memory deallocation (free) *)

Inductive extcall_free_sem (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_free_sem_intro: forall b lo sz m m',
      Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) = Some (Vptrofs sz) ->
      Ptrofs.unsigned sz > 0 ->
      Mem.free m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) = Some m' ->
      (* ~ in_stack (Mem.stack m) b -> *)
      extcall_free_sem ge (Vptr b lo :: nil) m E0 Vundef m'.

(* Lemma extcall_free_ok: *)
(*   extcall_properties extcall_free_sem *)
(*                      (mksignature (Tptr :: nil) None cc_default). *)
(* Proof. *)
(*   constructor; intros. *)
(* (* well typed *) *)
(* - inv H. unfold proj_sig_res. simpl. auto. *)
(* (* symbols preserved *) *)
(* - inv H0; econstructor; eauto. *)
(* (* valid block *) *)
(* - inv H. eauto with mem. *)
(* (* perms *) *)
(* - inv H. eapply Mem.perm_free_3; eauto. *)
(* (* readonly *) *)
(* - inv H. eapply Mem.free_unchanged_on; eauto. *)
(*   intros. red; intros. elim H3. *)
(*   apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem. *)
(*   eapply Mem.free_range_perm; eauto. *)
(* (* mem extends *) *)
(* - inv H. inv H1. inv H8. inv H6. *)
(*   exploit Mem.load_extends; eauto. intros [v' [A B]]. *)
(*   assert (v' = Vptrofs sz). *)
(*   { unfold Vptrofs in *; destruct Archi.ptr64; inv B; auto. } *)
(*   subst v'. *)
(*   exploit Mem.free_parallel_extends; eauto. *)
(*   admit. *)
(*   intros [m2' [C D]]. *)
(*   exists Vundef; exists m2'. *)
(*   repeat *)
(*     match goal with *)
(*         |- _ /\ _ => *)
(*         split; try now auto *)
(*     end. *)
(*   econstructor; eauto. *)
(*   (* eapply Mem.not_in_frames_extends; eauto. *) *)
(*   eapply Mem.free_unchanged_on; eauto. *)
(*   unfold loc_out_of_bounds; intros. *)
(*   assert (Mem.perm m1 b i Max Nonempty). *)
(*   { apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem. *)
(*     eapply Mem.free_range_perm. eexact H4. eauto. } *)
(*   tauto. *)
(* (* mem inject *) *)
(* - inv H0. inv H2. inv H7. inv H9. *)
(*   exploit Mem.load_inject; eauto. intros [v' [A B]]. *)
(*   assert (v' = Vptrofs sz). *)
(*   { unfold Vptrofs in *; destruct Archi.ptr64; inv B; auto. } *)
(*   subst v'. *)
(*   assert (P: Mem.range_perm m1 b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) Cur Freeable). *)
(*     eapply Mem.free_range_perm; eauto. *)
(*   exploit Mem.address_inject; eauto. *)
(*     apply Mem.perm_implies with Freeable; auto with mem. *)
(*     apply P. instantiate (1 := lo). *)
(*     generalize (size_chunk_pos Mptr); omega. *)
(*   intro EQ. *)
(*   exploit Mem.free_parallel_inject; eauto. admit. intros (m2' & C & D). *)
(*   exists f, Vundef, m2'; split. *)
(*   apply extcall_free_sem_intro with (sz := sz) (m' := m2'). *)
(*     rewrite EQ. rewrite <- A. f_equal. omega. *)
(*     auto. *)
(*     rewrite ! EQ. rewrite <- C. f_equal; omega. *)
(*   split. auto. *)
(*   split. auto. *)
(*   split. eapply Mem.free_unchanged_on; eauto. unfold loc_unmapped. intros; congruence. *)
(*   split. eapply Mem.free_unchanged_on; eauto. unfold loc_out_of_reach. *)
(*     intros. red; intros. eelim H2; eauto. *)
(*     apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem. *)
(*     apply P. omega. *)
(*   split. auto. *)
(*   red; intros. congruence. *)
(* - inv SEM1. *)
(*   exploit Mem.load_unchanged_on. apply UNCH. 2: apply H. simpl; auto. intro LOAD2. *)
(*   edestruct (Mem.unchanged_on_free _ _ UNCH _ _ _ _ H1) as (m2' & FREE' & UNCH'). *)
(*   eexists; repeat apply conj; eauto. *)
(*   econstructor; eauto. *)
(*   apply Mem.nextblock_free in H1. apply Mem.nextblock_free in FREE'. congruence. *)
(* (* trace length *) *)
(* - inv H; simpl; omega. *)
(* (* receptive *) *)
(* - assert (t1 = t2). inv H; inv H0; auto. subst t2. *)
(*   exists vres1; exists m1; auto. *)
(* (* determ *) *)
(* - inv H; inv H0. *)
(*   assert (EQ1: Vptrofs sz0 = Vptrofs sz) by congruence. *)
(*   assert (EQ2: sz0 = sz). *)
(*   { unfold Vptrofs in EQ1; destruct Archi.ptr64 eqn:SF. *)
(*     rewrite <- (Ptrofs.of_int64_to_int64 SF sz0), <- (Ptrofs.of_int64_to_int64 SF sz). congruence. *)
(*     rewrite <- (Ptrofs.of_int_to_int SF sz0), <- (Ptrofs.of_int_to_int SF sz). congruence. *)
(*   } *)
(*   subst sz0. *)
(*   split. constructor. intuition congruence. *)
(* -  inv H. eapply Mem.free_unchanged_on. eauto. *)
(*    intros. intro A; apply A; clear A. *)
(*    red. *)
(*    rewrite Mem.not_in_frames_no_frame_info; auto. *)
(* - inv H. *)
(*   symmetry; eapply Mem.free_stack_blocks; eauto. *)
(* Qed. *)

(** ** Semantics of [memcpy] operations. *)

Inductive extcall_memcpy_sem (sz al: Z) (ge: Senv.t):
                        list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_memcpy_sem_intro: forall bdst odst bsrc osrc m bytes m',
      al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz >= 0 -> (al | sz) ->
      (sz > 0 -> (al | Ptrofs.unsigned osrc)) ->
      (sz > 0 -> (al | Ptrofs.unsigned odst)) ->
      bsrc <> bdst \/ Ptrofs.unsigned osrc = Ptrofs.unsigned odst
                   \/ Ptrofs.unsigned osrc + sz <= Ptrofs.unsigned odst
                   \/ Ptrofs.unsigned odst + sz <= Ptrofs.unsigned osrc ->
      Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz = Some bytes ->
      Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes = Some m' ->
      extcall_memcpy_sem sz al ge (Vptr bdst odst :: Vptr bsrc osrc :: nil) m E0 Vundef m'.


Lemma extcall_memcpy_ok:
  forall sz al,
  extcall_properties (extcall_memcpy_sem sz al)
                     (mksignature (Tptr :: Tptr :: nil) None cc_default).
Proof.
  intros. constructor.
- (* return type *)
  intros. inv H. constructor.
- (* change of globalenv *)
  intros. inv H0. econstructor; eauto.
- (* valid blocks *)
  intros. inv H. eauto with mem.
- (* perms *)
  intros. inv H. eapply Mem.perm_storebytes_2; eauto.
- (* readonly *)
  intros. inv H. eapply Mem.storebytes_unchanged_on; eauto.
  intros; red; intros. elim H8.
  apply Mem.perm_cur_max. eapply Mem.storebytes_range_perm; eauto.
- (* extensions *)
  intros. inv H.
  inv H1. inv H11. inv H13. inv H10. inv H12.
  exploit Mem.loadbytes_length; eauto. intros LEN.
  exploit Mem.loadbytes_extends; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_within_extends; eauto. intros [m2' [C D]].
  exists Vundef; exists m2'.
  split. econstructor; eauto.
  split. constructor.
  split. auto.
  eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_bounds; intros.
  assert (Mem.perm m1 bdst i Max Nonempty).
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm; eauto.
  erewrite list_forall2_length; eauto.
  tauto.
- (* injections *)
  intros until 1.
  apply symbols_inject'_symbols_inject in H.
  intros. inv H0. inv H2. inv H12. inv H14. inv H12. inv H15.
  destruct (zeq sz 0).
+ (* special case sz = 0 *)
  assert (bytes = nil).
  { exploit (Mem.loadbytes_empty m1 bsrc (Ptrofs.unsigned osrc) sz). omega. congruence. }
  subst.
  destruct (Mem.range_perm_storebytes m1' b2 (Ptrofs.unsigned (Ptrofs.add odst (Ptrofs.repr delta))) nil)
  as [m2' SB].
  simpl. red; intros; omegaContradiction.
  apply lo_ge_hi_stack_access. simpl; omega.
  exists f, Vundef, m2'.
  split. econstructor; eauto.
  intros; omegaContradiction.
  intros; omegaContradiction.
  right; omega.
  apply Mem.loadbytes_empty. omega.
  split. constructor.
  split. eapply Mem.storebytes_empty_inject; eauto.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped; intros.
  congruence.
  split. eapply Mem.storebytes_unchanged_on; eauto.
  simpl; intros; omegaContradiction.
  split. apply inject_incr_refl.
  red; intros; congruence.
+ (* general case sz > 0 *)
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (RPSRC: Mem.range_perm m1 bsrc (Ptrofs.unsigned osrc) (Ptrofs.unsigned osrc + sz) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m1 bdst (Ptrofs.unsigned odst) (Ptrofs.unsigned odst + sz) Cur Nonempty).
    replace sz with (Z_of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply nat_of_Z_eq. omega.
  assert (PSRC: Mem.perm m1 bsrc (Ptrofs.unsigned osrc) Cur Nonempty).
    apply RPSRC. omega.
  assert (PDST: Mem.perm m1 bdst (Ptrofs.unsigned odst) Cur Nonempty).
    apply RPDST. omega.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [m2' [C D]].
  exists f; exists Vundef; exists m2'.
  split. econstructor; try rewrite EQ1; try rewrite EQ2; eauto.
  intros; eapply Mem.aligned_area_inject with (m := m1); eauto.
  intros; eapply Mem.aligned_area_inject with (m := m1); eauto.
  eapply Mem.disjoint_or_equal_inject with (m := m1); eauto.
  apply Mem.range_perm_max with Cur; auto.
  apply Mem.range_perm_max with Cur; auto. omega.
  split. constructor.
  split. auto.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped; intros.
  congruence.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_reach; intros. red; intros.
  eelim H2; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm; eauto.
  erewrite list_forall2_length; eauto.
  omega.
  split. apply inject_incr_refl.
  red; intros; congruence.
- (* trace length *)
  intros; inv H. simpl; omega.
- (* receptive *)
  intros.
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
- (* determ *)
  intros; inv H; inv H0. split. constructor. intros; split; congruence.
- intros. inv H.
  eapply Mem.storebytes_unchanged_on; eauto.
  simpl; intros. intro A; apply A; clear A.
  eapply stack_access_inside; eauto. eapply Mem.storebytes_stack_access. eauto. omega. omega.
- intros. inv H.
  split; first [ now (eapply Mem.perm_storebytes_1; eauto) | now (eapply Mem.perm_storebytes_2; eauto)].
- intros. inv H.
  split; first [ now (eapply Mem.perm_storebytes_1; eauto) | now (eapply Mem.perm_storebytes_2; eauto)].
- intros; inv H.
  symmetry; eapply Mem.storebytes_stack_blocks; eauto.
Qed.

(** ** Semantics of annotations. *)

Inductive extcall_annot_sem (text: string) (targs: list typ) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_sem_intro: forall vargs m args,
      eventval_list_match ge args targs vargs ->
      extcall_annot_sem text targs ge vargs m (Event_annot text args :: E0) Vundef m.

Lemma extcall_annot_ok:
  forall text targs,
  extcall_properties (extcall_annot_sem text targs)
                     (mksignature targs None cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- inv H. simpl. auto.
(* symbols *)
- destruct H as (_ & A & B & C). inv H0. econstructor; eauto.
  eapply eventval_list_match_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H. apply Mem.unchanged_on_refl.
(* mem extends *)
- inv H.
  exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_lessdef; eauto.
(* mem injects *)
- apply symbols_inject'_symbols_inject in H.
  inv H0.
  exists f; exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_inject; eauto.
  red; intros; congruence.
(* trace length *)
- inv H; simpl; omega.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto.
  exists vres1; exists m1; congruence.
(* determ *)
- inv H; inv H0.
  assert (args = args0). eapply eventval_list_match_determ_2; eauto. subst args0.
  split. constructor. auto.
- inv H; apply Mem.unchanged_on_refl.
- inv H; tauto.
- inv H; tauto.
- inv H; auto.
Qed.

Inductive extcall_annot_val_sem (text: string) (targ: typ) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_val_sem_intro: forall varg m arg,
      eventval_match ge arg targ varg ->
      extcall_annot_val_sem text targ ge (varg :: nil) m (Event_annot text (arg :: nil) :: E0) varg m.

Lemma extcall_annot_val_ok:
  forall text targ,
  extcall_properties (extcall_annot_val_sem text targ)
                     (mksignature (targ :: nil) (Some targ) cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- inv H. unfold proj_sig_res; simpl. eapply eventval_match_type; eauto.
(* symbols *)
- destruct H as (_ & A & B & C). inv H0. econstructor; eauto.
  eapply eventval_match_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H. apply Mem.unchanged_on_refl.
(* mem extends *)
- inv H. inv H1. inv H6.
  exists v2; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_match_lessdef; eauto.
(* mem inject *)
- apply symbols_inject'_symbols_inject in H.
  inv H0. inv H2. inv H7.
  exists f; exists v'; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_match_inject; eauto.
  red; intros; congruence.
(* trace length *)
- inv H; simpl; omega.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
- inv H; inv H0.
  assert (arg = arg0). eapply eventval_match_determ_2; eauto. subst arg0.
  split. constructor. auto.
- inv H; apply Mem.unchanged_on_refl.
- inv H; tauto.
- inv H; tauto.
- inv H; auto.
Qed.

Inductive extcall_debug_sem (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_debug_sem_intro: forall vargs m,
      extcall_debug_sem ge vargs m E0 Vundef m.

Lemma extcall_debug_ok:
  forall targs,
  extcall_properties extcall_debug_sem
                     (mksignature targs None cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- inv H. simpl. auto.
(* symbols *)
- inv H0. econstructor; eauto.
(* valid blocks *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H. apply Mem.unchanged_on_refl.
(* mem extends *)
- inv H.
  exists Vundef; exists m1'; intuition.
  econstructor; eauto.
(* mem injects *)
- apply symbols_inject'_symbols_inject in H.
  inv H0.
  exists f; exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  red; intros; congruence.
(* trace length *)
- inv H; simpl; omega.
(* receptive *)
- inv H; inv H0. exists Vundef, m1; constructor.
(* determ *)
- inv H; inv H0.
  split. constructor. auto.
- inv H; apply Mem.unchanged_on_refl.
- inv H; tauto.
- inv H; tauto.
- inv H; auto.
Qed.

End WITHMEMORYMODEL.

(** ** Semantics of external functions. *)

(** For functions defined outside the program ([EF_external],
  [EF_builtin] and [EF_runtime]), we do not define their
  semantics, but only assume that it satisfies
  [extcall_properties]. *)

Class ExternalCallsOps (mem: Type) `{memory_model_ops: Mem.MemoryModelOps mem}: Type :=
{
  external_functions_sem: String.string -> signature -> extcall_sem;
  builtin_functions_sem: String.string -> signature -> extcall_sem;
  runtime_functions_sem: String.string -> signature -> extcall_sem;
  inline_assembly_sem: String.string -> signature -> extcall_sem
}.
Global Arguments ExternalCallsOps _ {_}.

Class ExternalCallsProps mem `{external_calls_ops: ExternalCallsOps mem}
      {symbols_inject'_instance: SymbolsInject}
      {memory_model_prf: Mem.MemoryModel mem}
: Prop :=
{
  external_functions_properties:
    forall id sg, extcall_properties (external_functions_sem id sg) sg;

  builtin_functions_properties:
    forall id sg, extcall_properties (builtin_functions_sem id sg) sg;

  runtime_functions_properties:
    forall id sg, extcall_properties (runtime_functions_sem id sg) sg;

(** We treat inline assembly similarly. *)

  inline_assembly_properties:
    forall id sg, extcall_properties (inline_assembly_sem id sg) sg
}.
Global Arguments ExternalCallsProps _ {_ _ _ _}.

Class EnableBuiltins mem `{ExternalCallsOps mem}: Type :=
  {
    cc_enable_external_as_builtin: bool
  }.
Global Arguments EnableBuiltins _ { _ _ }.

Definition builtin_enabled `{enable_builtin_instance: EnableBuiltins} (ec: external_function): Prop :=
  match ec with
	| EF_external _ _ => if cc_enable_external_as_builtin then True else False
	| _ => True
	end.

Hint Unfold builtin_enabled.

Class ExternalCalls
      mem
      `{memory_model_ops: !Mem.MemoryModelOps mem}
      `{external_calls_ops: !ExternalCallsOps mem}
      `{memory_model_prf: !Mem.MemoryModel mem}
      `{enable_builtins_instance: !EnableBuiltins mem}
      `{symbols_inject_instance: SymbolsInject}
      `{external_calls_props: !ExternalCallsProps mem}
  : Type :=
  {
  }.
Global Arguments ExternalCalls mem { memory_model_ops external_calls_ops memory_model_prf enable_builtins_instance symbols_inject_instance external_calls_props }.

(** ** Combined semantics of external calls *)

(** Combining the semantics given above for the various kinds of external calls,
  we define the predicate [external_call] that relates:
- the external function being invoked
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).

This predicate is used in the semantics of all CompCert languages. *)

Section WITHEXTERNALCALLS.

Context `{external_calls_prf: ExternalCalls}.

Definition external_call (ef: external_function): extcall_sem :=
  match ef with
  | EF_external name sg  => external_functions_sem name sg
  | EF_builtin name sg   => builtin_functions_sem name sg
  | EF_runtime name sg   => runtime_functions_sem name sg
  | EF_vload chunk       => volatile_load_sem chunk
  | EF_vstore chunk      => volatile_store_sem chunk
  | EF_malloc            => extcall_malloc_sem
  (* | EF_free              => extcall_free_sem *)
  | EF_memcpy sz al      => extcall_memcpy_sem sz al
  | EF_annot txt targs   => extcall_annot_sem txt targs
  | EF_annot_val txt targ => extcall_annot_val_sem txt targ
  | EF_inline_asm txt sg clb => inline_assembly_sem txt sg
  | EF_debug kind txt targs => extcall_debug_sem
  end.

Theorem external_call_spec:
  forall ef,
  extcall_properties (external_call ef) (ef_sig ef).
Proof.
  intros. unfold external_call, ef_sig; destruct ef.
  apply external_functions_properties.
  apply builtin_functions_properties.
  apply runtime_functions_properties.
  apply volatile_load_ok.
  apply volatile_store_ok.
  apply extcall_malloc_ok.
  (* apply extcall_free_ok. *)
  apply extcall_memcpy_ok.
  apply extcall_annot_ok.
  apply extcall_annot_val_ok.
  apply inline_assembly_properties.
  apply extcall_debug_ok.
Qed.

Definition external_call_well_typed ef := ec_well_typed (external_call_spec ef).
Definition external_call_symbols_preserved ef := ec_symbols_preserved (external_call_spec ef).
Definition external_call_valid_block ef := ec_valid_block (external_call_spec ef).
Definition external_call_max_perm ef := ec_max_perm (external_call_spec ef).
Definition external_call_readonly ef := ec_readonly (external_call_spec ef).
Definition external_call_mem_extends {perminj: InjectPerm} ef := ec_mem_extends (external_call_spec ef).
Definition external_call_mem_inject_gen {perminj: InjectPerm} ef := ec_mem_inject (external_call_spec ef).
Definition external_call_trace_length ef := ec_trace_length (external_call_spec ef).
Definition external_call_receptive ef := ec_receptive (external_call_spec ef).
Definition external_call_determ ef := ec_determ (external_call_spec ef).
Definition external_call_unchanged_on ef := ec_unchanged_on_private_stack (external_call_spec ef).
Definition external_call_stack_blocks ef := ec_stack_blocks (external_call_spec ef).

Definition ec_get_frame_info (sem: extcall_sem) :=
  forall ge vargs m1 t vres m2,
    sem ge vargs m1 t vres m2 ->
    forall b, get_frame_info (Mem.stack m1) b = get_frame_info (Mem.stack m2) b.
Lemma external_call_get_frame_info ef : ec_get_frame_info (external_call ef).
Proof.
  red; intros.
  erewrite external_call_stack_blocks. reflexivity. eauto.
Qed.

(** Corollary of [external_call_valid_block]. *)

Lemma external_call_nextblock:
  forall ef ge vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 ->
  Ple (Mem.nextblock m1) (Mem.nextblock m2).
Proof.
  intros. destruct (plt (Mem.nextblock m2) (Mem.nextblock m1)).
  exploit external_call_valid_block; eauto. intros.
  eelim Plt_strict; eauto.
  unfold Plt, Ple in *; zify; omega.
Qed.

(** Special case of [external_call_mem_inject_gen] (for backward compatibility) *)

Definition meminj_preserves_globals (F V: Type) (ge: Genv.t F V) (f: block -> option (block * Z)) : Prop :=
     (forall id b, Genv.find_symbol ge id = Some b -> f b = Some(b, 0))
  /\ (forall b gv, Genv.find_var_info ge b = Some gv -> f b = Some(b, 0))
  /\ (forall b1 b2 delta gv, Genv.find_var_info ge b2 = Some gv -> f b1 = Some(b2, delta) -> b2 = b1).

Lemma meminj_preserves_globals_symbols_inject'
 (F V: Type) (ge: Genv.t F V)  (f: block -> option (block * Z)):
  meminj_preserves_globals ge f ->
  symbols_inject' f ge ge.
Proof.
  intros H.
  apply meminj_preserves_globals'_symbols_inject'.
  destruct H as (A & B & C).
  split; auto.
  simpl; unfold Genv.block_is_volatile.
  intros b1 b2 delta H.
  destruct (Genv.find_var_info ge b1) as [gv1|] eqn:V1.
  * exploit B; eauto. intros EQ; rewrite EQ in H; inv H. rewrite V1; auto.
  * destruct (Genv.find_var_info ge b2) as [gv2|] eqn:V2; auto.
    exploit C; eauto. intros EQ; subst b2. congruence.
Qed.

Lemma external_call_mem_inject {perminj: InjectPerm}:
  forall ef F V (ge: Genv.t F V) vargs m1 t vres m2 f g m1' vargs',
  meminj_preserves_globals ge f ->
  external_call ef ge vargs m1 t vres m2 ->
  Mem.inject f g m1 m1' ->
  Val.inject_list f vargs vargs' ->
  exists f', exists vres', exists m2',
     external_call ef ge vargs' m1' t vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' g m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1'.
Proof.
  intros. eapply external_call_mem_inject_gen with (ge1 := ge); eauto.
  eapply meminj_preserves_globals_symbols_inject' ; eauto.
Qed.

(** Corollaries of [external_call_determ]. *)

Lemma external_call_match_traces:
  forall ef ge vargs m t1 vres1 m1 t2 vres2 m2,
  external_call ef ge vargs m t1 vres1 m1 ->
  external_call ef ge vargs m t2 vres2 m2 ->
  match_traces ge t1 t2.
Proof.
  intros. exploit external_call_determ. eexact H. eexact H0. tauto.
Qed.

Lemma external_call_deterministic:
  forall ef ge vargs m t vres1 m1 vres2 m2,
  external_call ef ge vargs m t vres1 m1 ->
  external_call ef ge vargs m t vres2 m2 ->
  vres1 = vres2 /\ m1 = m2.
Proof.
  intros. exploit external_call_determ. eexact H. eexact H0. intuition.
Qed.

(** * Evaluation of builtin arguments *)

Section EVAL_BUILTIN_ARG.

Variable A: Type.
Variable ge: Senv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Inductive eval_builtin_arg: builtin_arg A -> val -> Prop :=
  | eval_BA: forall x,
      eval_builtin_arg (BA x) (e x)
  | eval_BA_int: forall n,
      eval_builtin_arg (BA_int n) (Vint n)
  | eval_BA_long: forall n,
      eval_builtin_arg (BA_long n) (Vlong n)
  | eval_BA_float: forall n,
      eval_builtin_arg (BA_float n) (Vfloat n)
  | eval_BA_single: forall n,
      eval_builtin_arg (BA_single n) (Vsingle n)
  | eval_BA_loadstack: forall chunk ofs v,
      Mem.loadv chunk m (Val.offset_ptr sp ofs) = Some v ->
      eval_builtin_arg (BA_loadstack chunk ofs) v
  | eval_BA_addrstack: forall ofs,
      eval_builtin_arg (BA_addrstack ofs) (Val.offset_ptr sp ofs)
  | eval_BA_loadglobal: forall chunk id ofs v,
      Mem.loadv chunk m (Senv.symbol_address ge id ofs) = Some v ->
      eval_builtin_arg (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal: forall id ofs,
      eval_builtin_arg (BA_addrglobal id ofs) (Senv.symbol_address ge id ofs)
  | eval_BA_splitlong: forall hi lo vhi vlo,
      eval_builtin_arg hi vhi -> eval_builtin_arg lo vlo ->
      eval_builtin_arg (BA_splitlong hi lo) (Val.longofwords vhi vlo).

Definition eval_builtin_args (al: list (builtin_arg A)) (vl: list val) : Prop :=
  list_forall2 eval_builtin_arg al vl.

Lemma eval_builtin_arg_determ:
  forall a v, eval_builtin_arg a v -> forall v', eval_builtin_arg a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  f_equal; eauto.
Qed.

Lemma eval_builtin_args_determ:
  forall al vl, eval_builtin_args al vl -> forall vl', eval_builtin_args al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_builtin_arg_determ.
Qed.

End EVAL_BUILTIN_ARG.

Hint Constructors eval_builtin_arg: barg.

(** Invariance by change of global environment. *)

Section EVAL_BUILTIN_ARG_PRESERVED.

Variables A F1 V1 F2 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eval_builtin_arg_preserved:
  forall a v, eval_builtin_arg ge1 e sp m a v -> eval_builtin_arg ge2 e sp m a v.
Proof.
  assert (EQ: forall id ofs, Senv.symbol_address ge2 id ofs = Senv.symbol_address ge1 id ofs).
  { unfold Senv.symbol_address; simpl; intros. rewrite symbols_preserved; auto. }
  induction 1; eauto with barg. rewrite <- EQ in H; eauto with barg. rewrite <- EQ; eauto with barg.
Qed.

Lemma eval_builtin_args_preserved:
  forall al vl, eval_builtin_args ge1 e sp m al vl -> eval_builtin_args ge2 e sp m al vl.
Proof.
  induction 1; constructor; auto; eapply eval_builtin_arg_preserved; eauto.
Qed.

End EVAL_BUILTIN_ARG_PRESERVED.

(** Compatibility with the "is less defined than" relation. *)

Section EVAL_BUILTIN_ARG_LESSDEF.

Variable A: Type.
Variable ge: Senv.t.
Variables e1 e2: A -> val.
Variable sp: val.
Variables m1 m2: mem.
Context {perminj: InjectPerm}.
Hypothesis env_lessdef: forall x, Val.lessdef (e1 x) (e2 x).
Hypothesis mem_extends: Mem.extends m1 m2.

Lemma eval_builtin_arg_lessdef:
  forall a v1, eval_builtin_arg ge e1 sp m1 a v1 ->
  exists v2, eval_builtin_arg ge e2 sp m2 a v2 /\ Val.lessdef v1 v2.
Proof.
  induction 1.
- exists (e2 x); auto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_extends; eauto. intros (v' & P & Q). exists v'; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_extends; eauto. intros (v' & P & Q). exists v'; eauto with barg.
- econstructor; eauto with barg.
- destruct IHeval_builtin_arg1 as (vhi' & P & Q).
  destruct IHeval_builtin_arg2 as (vlo' & R & S).
  econstructor; split; eauto with barg. apply Val.longofwords_lessdef; auto.
Qed.

Lemma eval_builtin_args_lessdef:
  forall al vl1, eval_builtin_args ge e1 sp m1 al vl1 ->
  exists vl2, eval_builtin_args ge e2 sp m2 al vl2 /\ Val.lessdef_list vl1 vl2.
Proof.
  induction 1.
- econstructor; split. constructor. auto.
- exploit eval_builtin_arg_lessdef; eauto. intros (v1' & P & Q).
  destruct IHlist_forall2 as (vl' & U & V).
  exists (v1'::vl'); split; constructor; auto.
Qed.


End EVAL_BUILTIN_ARG_LESSDEF.

Section EVAL_BUILTIN_ARG_LESSDEF'.

  Variable A : Type.
  Variable ge : Senv.t.
  Variables rs1 rs2 : A -> val.
  Hypothesis rs_lessdef: forall a, Val.lessdef (rs1 a) (rs2 a).
  Variables sp sp' : val.
  Hypothesis sp_lessdef: Val.lessdef sp sp'.
  Variable m : mem.
  Context {perminj: InjectPerm}.

  Lemma eval_builtin_arg_lessdef':
  forall arg v v'
    (EBA: eval_builtin_arg ge rs1 sp m arg v)
    (EBA': eval_builtin_arg ge rs2 sp' m arg v'),
    Val.lessdef v v'.
  Proof.
    induction arg; intros; inv EBA; inv EBA'; subst; auto.
    - intros. exploit Mem.loadv_extends. apply Mem.extends_refl. apply H2.
      2: rewrite H3.
      apply Val.offset_ptr_lessdef; auto.
      intros (v2 & B & C). inv B. auto.
    - intros; apply Val.offset_ptr_lessdef; auto.
    - intros. exploit Mem.loadv_extends. apply Mem.extends_refl. apply H3.
      2: rewrite H4. auto. intros (v2 & B & C). inv B. auto.
    - apply Val.longofwords_lessdef. eauto. eauto.
  Qed.

  Lemma eval_builtin_args_lessdef':
    forall args vl vl'
      (EBA: eval_builtin_args ge rs1 sp m args vl)
      (EBA': eval_builtin_args ge rs2 sp' m args vl'),
      Val.lessdef_list vl vl'.
  Proof.
    induction args; simpl; intros. inv EBA; inv EBA'. constructor.
    inv EBA; inv EBA'. constructor; auto.
    eapply eval_builtin_arg_lessdef'; eauto.
  Qed.

End EVAL_BUILTIN_ARG_LESSDEF'.

Section EVAL_BUILTIN_ARG_LESSDEF''.

  Variable A : Type.
  Variable ge : Senv.t.
  Variables rs1 rs2 : A -> val.
  Hypothesis rs_lessdef: forall a, Val.lessdef (rs1 a) (rs2 a).
  Variables sp sp' : val.
  Hypothesis sp_lessdef: Val.lessdef sp sp'.
  Variables m m' : mem.
  Context {perminj: InjectPerm}.
  Hypotheses MEXT:  Mem.extends m m'.


  Lemma eval_builtin_arg_lessdef'':
  forall arg v
    (EBA: eval_builtin_arg ge rs1 sp m arg v),
  exists v', eval_builtin_arg ge rs2 sp' m' arg v' /\
        Val.lessdef v v'.
  Proof.
    induction arg; intros; inv EBA; subst; auto;
      try now (eexists; split; [ constructor | auto ]).
    - exploit Mem.loadv_extends. eauto. eauto. apply Val.offset_ptr_lessdef; try eassumption. eauto.
      intros (v2 & B & C).
      eexists; split. constructor. eauto. eauto.
    - eexists; split; [ constructor; eauto | eauto ]. intros; apply Val.offset_ptr_lessdef; auto.
    - exploit Mem.loadv_extends. eauto. eauto. auto.
      intros (v2 & B & C).
      eexists; split. constructor. eauto. eauto.
    - apply IHarg1 in H1. apply IHarg2 in H3.
      decompose [ex and] H1.
      decompose [ex and] H3.
      eexists; split; [ constructor; eauto | eauto ].
      apply Val.longofwords_lessdef. eauto. eauto.
  Qed.

  Lemma eval_builtin_args_lessdef'':
    forall args vl
      (EBA: eval_builtin_args ge rs1 sp m args vl),
    exists vl',
      eval_builtin_args ge rs2 sp' m' args vl' /\
      Val.lessdef_list vl vl'.
  Proof.
    induction args; simpl; intros. inv EBA. eexists; split; eauto. constructor.
    inv EBA.
    exploit IHargs; eauto. intros (vl' & EBA & LD).
    exploit eval_builtin_arg_lessdef''; eauto.
    intros (v' & EBA1 & L).
    eexists; split.
    constructor; eauto. eauto.
  Qed.

End EVAL_BUILTIN_ARG_LESSDEF''.


Section EVAL_BUILTIN_ARG_INJECT.

Variable A: Type.
Variable ge1 ge2: Senv.t.
Variables e1 e2: A -> val.
Variables sp1 sp2: val.
Variables m1 m2: mem.

Variable j: meminj.
Variable g: frameinj.

Hypothesis sp_inject: Val.inject j sp1 sp2.
Hypothesis env_inject: forall x, Val.inject j (e1 x) (e2 x).
Context {perminj: InjectPerm}.
Hypothesis mem_extends: Mem.inject j g m1 m2.

Hypothesis senv_preserved:
  forall s b,
    Senv.find_symbol ge1 s = Some b ->
    Senv.find_symbol ge2 s = Some b.

Hypothesis senv_inject:
  forall s b,
    Senv.find_symbol ge1 s = Some b ->
    j b = Some (b,0).

Lemma senv_preserved_symbol_address:
  forall s o,
    Val.inject j (Senv.symbol_address ge1 s o) (Senv.symbol_address ge2 s o).
Proof.
  unfold Senv.symbol_address.
  intros.
  destruct (Senv.find_symbol ge1 s) eqn:FS; auto.
  exploit senv_preserved. eauto. intro B; rewrite B.
  econstructor; eauto. rewrite Ptrofs.add_zero. auto.
Qed.

Lemma eval_builtin_arg_inject:
  forall a v1, eval_builtin_arg ge1 e1 sp1 m1 a v1 ->
  exists v2, eval_builtin_arg ge2 e2 sp2 m2 a v2 /\ Val.inject j v1 v2.
Proof.
  induction 1.
- exists (e2 x); auto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_inject; eauto. apply Val.offset_ptr_inject. eauto.
  intros (v' & P & Q). exists v'; eauto with barg.
- econstructor; split; eauto with barg.
  apply Val.offset_ptr_inject; eauto.
- exploit Mem.loadv_inject; eauto. apply senv_preserved_symbol_address.
  intros (v' & P & Q). exists v'; eauto with barg.
- econstructor; split; eauto with barg.
  apply senv_preserved_symbol_address.
- destruct IHeval_builtin_arg1 as (vhi' & P & Q).
  destruct IHeval_builtin_arg2 as (vlo' & R & S).
  econstructor; split; eauto with barg. apply Val.longofwords_inject; auto.
Qed.

Lemma eval_builtin_args_inject:
  forall al vl1, eval_builtin_args ge1 e1 sp1 m1 al vl1 ->
  exists vl2, eval_builtin_args ge2 e2 sp2 m2 al vl2 /\ Val.inject_list j vl1 vl2.
Proof.
  induction 1.
- econstructor; split. constructor. auto.
- exploit eval_builtin_arg_inject; eauto. intros (v1' & P & Q).
  destruct IHlist_forall2 as (vl' & U & V).
  exists (v1'::vl'); split; constructor; auto.
Qed.

End EVAL_BUILTIN_ARG_INJECT.

Lemma eval_builtin_arg_push:
  forall {A} ge (e: A -> val) sp m a v,
    eval_builtin_arg ge e sp m a v <->
    eval_builtin_arg ge e sp (Mem.push_new_stage m) a v.
Proof.
  intros A ge0 e sp m a v; split; induction 1; econstructor; eauto;
    repeat rewrite ? Mem.push_new_stage_loadv in *; eauto.
  rewrite Mem.push_new_stage_loadv in H. eauto.
  rewrite Mem.push_new_stage_loadv in H. eauto.
Qed.

Lemma eval_builtin_args_push:
  forall {A} ge (e: A -> val) sp m al vl,
    eval_builtin_args ge e sp m al vl <->
    eval_builtin_args ge e sp (Mem.push_new_stage m) al vl.
Proof.
  unfold eval_builtin_args.
  intros; apply list_forall2_iff.
  intros; apply eval_builtin_arg_push.
Qed.


  Lemma store_perm:
    forall chunk m b' o' v m',
      Mem.store chunk m b' o' v = Some m' ->
      forall b o k p,
        Mem.perm m' b o k p <-> Mem.perm m b o k p.
  Proof.
    split; intros.
    eapply Mem.perm_store_2; eauto.
    eapply Mem.perm_store_1; eauto.
  Qed.


  Lemma storev_perm:
    forall chunk m addr v m',
      Mem.storev chunk m addr v = Some m' ->
      forall b o k p,
        Mem.perm m' b o k p <-> Mem.perm m b o k p.
  Proof.
    intros. destruct addr; simpl in *; try congruence.
    eapply store_perm; eauto.
  Qed.

  Lemma free_perm:
    forall m b lo hi m',
      Mem.free m b lo hi = Some m' ->
      forall b' o k p,
        Mem.perm m' b' o k p <-> if peq b b' && zle lo o && zlt o hi then False else Mem.perm m b' o k p.
  Proof.
    intros.
    destr.
    - rewrite ! andb_true_iff in Heqb0. intuition.
      destruct zlt; simpl in *; try congruence.
      destruct zle; simpl in *; try congruence.
      destruct peq; simpl in *; try congruence.
      subst.
      eapply Mem.perm_free_2; eauto.
    - rewrite ! andb_false_iff in Heqb0.
      split; intros.
      + eapply Mem.perm_free_3; eauto.
      + eapply Mem.perm_free_1; eauto.
        destruct Heqb0. destruct H1. destruct peq; simpl in *; try congruence. auto.
        destruct zle; simpl in *; try congruence. right. left. omega.
        destruct zlt; simpl in *; try congruence. right. right. omega.
  Qed.

  Lemma alloc_perm:
    forall m lo hi m' b,
      Mem.alloc m lo hi = (m',b) ->
      forall b' o k p,
        Mem.perm m' b' o k p <-> if peq b b' then lo <= o < hi else Mem.perm m b' o k p.
  Proof.
    split; intros.
    eapply Mem.perm_alloc_inv in H0; eauto. destr_in H0; subst; destr.
    destr_in H0. subst.
    eapply Mem.perm_implies. eapply Mem.perm_alloc_2; eauto. constructor.
    eapply Mem.perm_alloc_1; eauto.
  Qed.

  Lemma record_perm:
    forall m fi m',
      Mem.record_stack_blocks m fi = Some m' ->
      forall b o k p,
        Mem.perm m' b o k p <-> Mem.perm m b o k p.
  Proof.
    split; intros.
    eapply Mem.record_stack_block_perm; eauto.
    eapply Mem.record_stack_block_perm'; eauto.
  Qed.


  Lemma unrecord_perm:
    forall m m',
      Mem.unrecord_stack_block m = Some m' ->
      forall b o k p,
        Mem.perm m' b o k p <-> Mem.perm m b o k p.
  Proof.
    split; intros.
    eapply Mem.unrecord_stack_block_perm; eauto.
    eapply Mem.unrecord_stack_block_perm'; eauto.
  Qed.

  Lemma extcall_perm:
    forall ef ge args m1 t res m2,
      external_call ef ge args m1 t res m2 ->
      forall b o k p,
        in_stack (Mem.stack m1) b ->
        Mem.perm m2 b o k p <-> Mem.perm m1 b o k p.
  Proof.
    intros.
    erewrite ec_perm_frames; eauto. 2: apply external_call_spec. tauto.
  Qed.

  Lemma drop_perm_perm:
    forall m b lo hi p m',
      Mem.drop_perm m b lo hi p = Some m' ->
      forall b' o k p',
        Mem.perm m' b' o k p' <-> (Mem.perm m b' o k p' /\( b = b' -> lo <= o < hi -> perm_order p p')).
  Proof.
    intros.
    split.
    intros PERM.
    split.
    eapply Mem.perm_drop_4; eauto. intros; subst.
    eapply Mem.perm_drop_2; eauto.
    intros (A & B).
    destruct (peq b b').
    2: eapply Mem.perm_drop_3; eauto.
    subst.
    trim B; auto.
    destruct (zle lo o).
    destruct (zlt o hi). trim B. omega.
    eapply Mem.perm_implies.
    eapply Mem.perm_drop_1; eauto. auto.
    eapply Mem.perm_drop_3; eauto. right; right. omega.
    eapply Mem.perm_drop_3; eauto. right; left. omega.
  Qed.

End WITHEXTERNALCALLS.

Hint Constructors eval_builtin_arg: barg.


Ltac rewrite_perms_fw :=
  match goal with
  | H1: Mem.record_stack_blocks _ _ = Some ?m |- Mem.perm ?m _ _ _ _ =>
    eapply (Mem.record_stack_block_perm' _ _ _ H1)
  | H1: Mem.alloc _ _ _ = (?m,_) |- Mem.perm ?m _ _ _ _ =>
    first [
        apply Mem.perm_implies; [apply (Mem.perm_alloc_2 _ _ _ _ _ H1) | try constructor]
      |  apply (Mem.perm_alloc_1 _ _ _ _ _ H1)
      ]
  | H1: Mem.store _ _ _ _ _ = Some ?m |- Mem.perm ?m _ _ _ _ =>
    apply (Mem.perm_store_1 _ _ _ _ _ _ H1)
  | H1: Mem.storev _ _ _ _ = Some ?m |- Mem.perm ?m _ _ _ _ =>
    apply (Mem.perm_store_1 _ _ _ _ _ _ H1)
  end.

Arguments Genv.init_mem_stack {mem memory_model_ops _ _ _ _}.

Ltac rewrite_stack_blocks :=
  match goal with
  | H:Mem.alloc _ _ _ = (?m, _) |- context [ Mem.stack ?m ] => rewrite (Mem.alloc_stack_blocks _ _ _ _ _ H)
  | H:Mem.store _ _ _ _ _ = Some ?m |- context [ Mem.stack ?m ] => rewrite (Mem.store_stack_blocks _ _ _ _ _ _ H)
  | H:Mem.storebytes _ _ _ _ = Some ?m |- context [ Mem.stack ?m ] => rewrite (Mem.storebytes_stack_blocks _ _ _ _ _ H)
  | H:Mem.storev _ _ _ _ = Some ?m |- context [ Mem.stack ?m ] => rewrite (Mem.storev_stack _ _ _ _ _ H)
  | H:external_call _ _ _ _ _ _ ?m |- context [ Mem.stack ?m ] => rewrite <- (external_call_stack_blocks _ _ _ _ _ _ _ H)
  | H:Mem.free_list _ _ = Some ?m |- context [ Mem.stack ?m ] => rewrite (Mem.free_list_stack_blocks _ _ _ H)
  | H:Mem.free _ _ _ _ = Some ?m |- context [ Mem.stack ?m ] => rewrite (Mem.free_stack_blocks _ _ _ _ _ H)
  | H:Mem.drop_perm _ _ _ _ _ = Some ?m |- context [ Mem.stack ?m ] => rewrite (Mem.drop_perm_stack _ _ _ _ _ _ H)
  | H: context[ Mem.stack (Mem.push_new_stage ?m)] |- _ => rewrite Mem.push_new_stage_stack in H; inv H
  | |- context[ Mem.stack (Mem.push_new_stage ?m)] => rewrite Mem.push_new_stage_stack
  | H: Genv.init_mem _ = Some ?m |- context [Mem.stack ?m] => rewrite (Genv.init_mem_stack _ _ H)
  | H:Mem.record_stack_blocks _ _ = Some ?m |- context [ Mem.stack ?m ] =>
    let f := fresh "f" in
    let r := fresh "r" in
    let EQ1 := fresh "EQ1" in
    let EQ2 := fresh "EQ2" in
    destruct (Mem.record_stack_blocks_stack_eq _ _ _ H) as (f & r & EQ1 & EQ2); rewrite EQ2; revert EQ1
  | H:Mem.unrecord_stack_block ?m1 = Some ?m
    |- context [ Mem.stack ?m ] =>
    let f := fresh "f" in
    let EQ := fresh "EQ" in
    destruct (Mem.unrecord_stack _ _ H) as (f, EQ); replace (Mem.stack m) with (tl (Mem.stack m1))
      by (rewrite EQ; reflexivity)
  | H: Mem.tailcall_stage ?m1 = Some ?m2
    |- context [Mem.stack ?m2] =>
    let f := fresh "f" in
    let r := fresh "r" in
    let EQ1 := fresh "EQ1" in
    let EQ2 := fresh "EQ2" in
    destruct (Mem.tailcall_stage_stack _ _ H) as (f & r & EQ1 & EQ2); rewrite EQ2;
    revert EQ1
  | H: Mem.record_init_sp ?m1 = Some ?m2 |- context [ Mem.stack ?m2 ] =>
    rewrite (Mem.record_init_sp_stack _ _ H)
  end.

Ltac rewrite_perms_bw H :=
  match type of H with
    Mem.perm ?m2 _ _ _ _ =>
    match goal with
    | H1: Mem.record_stack_blocks _ _ = Some ?m |- _ =>
      apply (Mem.record_stack_block_perm _ _ _ H1) in H
    | H1: Mem.alloc _ _ _ = (?m,_) |- _ =>
      apply (Mem.perm_alloc_inv _ _ _ _ _ H1) in H
    | H1: Mem.store _ _ _ _ _ = Some ?m |- _ =>
      apply (Mem.perm_store_2 _ _ _ _ _ _ H1) in H
    | H1: Mem.storev _ _ _ _ = Some ?m |- _ =>
      apply (Mem.perm_store_2 _ _ _ _ _ _ H1) in H
    end
  end.

Arguments Genv.init_mem_genv_next {mem memory_model_ops _ _ _}.

Ltac rewnb :=
  repeat
    match goal with
    | H: Mem.store _ _ _ _ _ = Some ?m |- context [Mem.nextblock ?m] =>
      rewrite (Mem.nextblock_store _ _ _ _ _ _ H)
    | H: Mem.storev _ _ _ _ = Some ?m |- context [Mem.nextblock ?m] =>
      rewrite (Mem.storev_nextblock _ _ _ _ _ H)
    | H: Mem.free _ _ _ _ = Some ?m |- context [Mem.nextblock ?m] =>
      rewrite (Mem.nextblock_free _ _ _ _ _ H)
    | H: Mem.drop_perm _ _ _ _ _ = Some ?m |- context [Mem.nextblock ?m] =>
      rewrite (Mem.nextblock_drop _ _ _ _ _ _ H)
    | H: Mem.alloc _ _ _ = (?m,_) |- context [Mem.nextblock ?m] =>
      rewrite (Mem.nextblock_alloc _ _ _ _ _ H)
    | H: Mem.record_stack_blocks _ _ = Some ?m |- context [Mem.nextblock ?m] =>
      rewrite (Mem.record_stack_block_nextblock _ _ _ H)
    | H: Mem.unrecord_stack_block _ = Some ?m |- context [Mem.nextblock ?m] =>
      rewrite (Mem.unrecord_stack_block_nextblock _ _ H)
    | |- context [ Mem.nextblock (Mem.push_new_stage ?m) ] => rewrite Mem.push_new_stage_nextblock
    | H: external_call _ _ _ ?m1 _ _ ?m2 |- Plt _ (Mem.nextblock ?m2) =>
      eapply Plt_Ple_trans; [ | apply external_call_nextblock in H; exact H ]
    | H: external_call _ _ _ ?m1 _ _ ?m2 |- Ple _ (Mem.nextblock ?m2) =>
      eapply Ple_trans; [ | apply external_call_nextblock in H; exact H ]
    | H: Genv.init_mem _ = Some ?m |- context [Mem.nextblock ?m] =>
      rewrite <- (Genv.init_mem_genv_next _ _ H)
    | H: Mem.tailcall_stage ?m1 = Some ?m2 |- context [ Mem.nextblock ?m2] =>
      rewrite (Mem.tailcall_stage_nextblock _ _ H)
    | H: Mem.record_init_sp ?m1 = Some ?m2 |- context [ Mem.nextblock ?m2] =>
      rewrite (Mem.record_init_sp_nextblock_eq _ _ H)
    end.



Arguments store_perm {mem memory_model_ops _}.
Arguments storev_perm {mem memory_model_ops _}.
Arguments free_perm {mem memory_model_ops _}.
Arguments drop_perm_perm {mem memory_model_ops _}.
Arguments alloc_perm {mem memory_model_ops _}.
Arguments record_perm {mem memory_model_ops _}.
Arguments unrecord_perm {mem memory_model_ops _}.
Arguments extcall_perm {mem memory_model_ops external_calls_ops memory_model_prf symbols_inject_instance0 external_calls_props}.

  Ltac rewrite_perms :=
    match goal with
    | H : Mem.store _ _ _ _ _ = Some ?m |- context [Mem.perm ?m _ _ _ _] =>
      rewrite (store_perm _ _ _ _ _ _ H)
    | H : Mem.storev _ _ _ _ = Some ?m |- context [Mem.perm ?m _ _ _ _] =>
      rewrite (storev_perm _ _ _ _ _ H)
    | H: Mem.free _ _ _ _ = Some ?m |- context [Mem.perm ?m _ _ _ _] =>
      rewrite (free_perm _ _ _ _ _ H)
    | H: Mem.drop_perm _ _ _ _ _ = Some ?m |- context [Mem.perm ?m _ _ _ _] =>
      rewrite (drop_perm_perm _ _ _ _ _ _ H)
    | H: Mem.alloc _ _ _ = (?m,_) |- context [Mem.perm ?m _ _ _ _] =>
      rewrite (alloc_perm _ _ _ _ _ H)
    | H: Mem.record_stack_blocks _ _ = Some ?m |- context [Mem.perm ?m _ _ _ _] =>
      rewrite (record_perm _ _ _ H)
    | H: Mem.unrecord_stack_block _ = Some ?m |- context [Mem.perm ?m _ _ _ _] =>
      rewrite (unrecord_perm _ _ H)
    | |- context [Mem.perm (Mem.push_new_stage _) _ _ _ _] =>
      rewrite (Mem.push_new_stage_perm)
    | H: external_call _ ?ge ?args ?m1 ?t ?res ?m2 |- context [Mem.perm ?m2 ?b _ _ _] =>
      rewrite (extcall_perm _ _ _ _ _ _ _ H)
    | H: Mem.tailcall_stage ?m1 = Some ?m2 |- context [ Mem.perm ?m2 _ _ _ _ ] =>
      rewrite (Mem.tailcall_stage_perm _ _ H)
    | H: Mem.record_init_sp ?m1 = Some ?m2 |- context [ Mem.perm ?m2 _ _ _ _ ] =>
      rewrite (Mem.record_init_sp_perm _ _ H)
    end.
