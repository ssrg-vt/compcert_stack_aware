(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Jan 9, 2018 *)
(* ******************* *)

Require Import Axioms Coqlib Errors Maps AST Linking.
Require Import Integers Floats Values Memory.
Require Import FlatAsmGlobenv Sect.
Require Events.


Section WITHEXTERNALCALLS.

Context `{external_calls_prf: Events.ExternalCalls}.

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
  | eval_BA_loadglobal: forall chunk id ofs v o,
      Senv.symbol_address ge id ofs = Some o ->
      Mem.loadv chunk m (flatptr o) = Some v ->
      eval_builtin_arg (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal: forall id ofs o,
      (Senv.symbol_address ge id ofs) = Some o -> 
      eval_builtin_arg (BA_addrglobal id ofs) (flatptr o)
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

End WITHEXTERNALCALLS.