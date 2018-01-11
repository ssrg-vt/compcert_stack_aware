(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Jan 9, 2018 *)
(* ******************* *)

Require Import Axioms Coqlib Errors Maps AST Linking.
Require Import Integers Floats Values Memory.
Require Import FlatAsmGlobenv Sect.

(** * Arguments and results to builtin functions *)

Inductive builtin_arg (A: Type) : Type :=
  | BA (x: A)
  | BA_int (n: int)
  | BA_long (n: int64)
  | BA_float (f: float)
  | BA_single (f: float32)
  | BA_loadstack (chunk: memory_chunk) (ofs: ptrofs)
  | BA_addrstack (ofs: ptrofs)
  | BA_loadglobal (chunk: memory_chunk) (gloc: sect_label) (ofs: ptrofs)
  | BA_addrglobal (gloc: sect_label) (ofs: ptrofs)
  | BA_splitlong (hi lo: builtin_arg A).


Section WITHEXTERNALCALLS.

Context `{memory_model_ops: Mem.MemoryModelOps}.

(** * Evaluation of builtin arguments *)

Section EVAL_BUILTIN_ARG.

Variable F: Type.
Variable I: Type.
Variable A: Type.
Variable ge: Genv.t F I.
Variable e: A -> val.
Variable sp: val.
Variable m:mem. 

Inductive eval_builtin_arg: builtin_arg A -> val -> Prop :=
  | eval_BA: forall x,
      eval_builtin_arg (BA A x) (e x)
  | eval_BA_int: forall n,
      eval_builtin_arg (BA_int A n) (Vint n)
  | eval_BA_long: forall n,
      eval_builtin_arg (BA_long A n) (Vlong n)
  | eval_BA_float: forall n,
      eval_builtin_arg (BA_float A n) (Vfloat n)
  | eval_BA_single: forall n,
      eval_builtin_arg (BA_single A n) (Vsingle n)
  | eval_BA_loadstack: forall chunk ofs v,
      Mem.loadv chunk m (Val.offset_ptr sp ofs) = Some v ->
      eval_builtin_arg (BA_loadstack A chunk ofs) v
  | eval_BA_addrstack: forall ofs,
      eval_builtin_arg (BA_addrstack A ofs) (Val.offset_ptr sp ofs)
  | eval_BA_loadglobal: forall chunk gloc ofs v o,
      Genv.get_label_offset ge gloc ofs = Some o ->
      Mem.loadv chunk m (flatptr o) = Some v ->
      eval_builtin_arg (BA_loadglobal A chunk gloc ofs) v
  | eval_BA_addrglobal: forall gloc ofs o,
      (Genv.get_label_offset ge gloc ofs) = Some o -> 
      eval_builtin_arg (BA_addrglobal A gloc ofs) (flatptr o)
  | eval_BA_splitlong: forall hi lo vhi vlo,
      eval_builtin_arg hi vhi -> eval_builtin_arg lo vlo ->
      eval_builtin_arg (BA_splitlong A hi lo) (Val.longofwords vhi vlo).

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