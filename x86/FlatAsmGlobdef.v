Require Import Coqlib Integers Floats Memory.
Require Import Segment.

(** Initialization data for global variables. *)

Inductive init_data: Type :=
  | Init_int8: int -> init_data
  | Init_int16: int -> init_data
  | Init_int32: int -> init_data
  | Init_int64: int64 -> init_data
  | Init_float32: float32 -> init_data
  | Init_float64: float -> init_data
  | Init_space: Z -> init_data
  | Init_addrof:  seglabel -> ptrofs -> init_data.  (**r address of symbol + offset *)

Definition init_data_size (i: init_data) : Z :=
  match i with
  | Init_int8 _ => 1
  | Init_int16 _ => 2
  | Init_int32 _ => 4
  | Init_int64 _ => 8
  | Init_float32 _ => 4
  | Init_float64 _ => 8
  | Init_addrof _ _ => if Archi.ptr64 then 8 else 4
  | Init_space n => Zmax n 0
  end.

Fixpoint init_data_list_size (il: list init_data) {struct il} : Z :=
  match il with
  | nil => 0
  | i :: il' => init_data_size i + init_data_list_size il'
  end.

Lemma init_data_size_pos:
  forall i, init_data_size i >= 0.
Proof.
  destruct i; simpl; try xomega. destruct Archi.ptr64; omega.
Qed.

Lemma init_data_list_size_pos:
  forall il, init_data_list_size il >= 0.
Proof.
  induction il; simpl. omega. generalize (init_data_size_pos a); omega.
Qed.


(** Information attached to global variables. *)

Record globvar (V: Type) : Type := mkglobvar {
  gvar_info: V;                    (**r language-dependent info, e.g. a type *)
  gvar_init: list init_data;       (**r initialization data *)
  gvar_readonly: bool;             (**r read-only variable? (const) *)
  gvar_volatile: bool              (**r volatile variable? *)
}.

Definition perm_globvar {V} (gv: globvar V) : permission :=
  if gv.(gvar_volatile V) then Nonempty
  else if gv.(gvar_readonly V) then Readable
  else Writable.

Inductive globdef (F V: Type) : Type :=
  | Gfun (f: F)
  | Gvar (v: globvar V).

Arguments Gfun [F V].
Arguments Gvar [F V].

