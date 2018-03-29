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

(** Global environments are a component of the dynamic semantics of
  all languages involved in the compiler.  A global environment
  maps symbol names (names of functions and of global variables)
  to the corresponding memory addresses.  It also maps memory addresses
  of functions to the corresponding function descriptions.

  Global environments, along with the initial memory state at the beginning
  of program execution, are built from the program of interest, as follows:
- A distinct memory address is assigned to each function of the program.
  These function addresses use negative numbers to distinguish them from
  addresses of memory blocks.  The associations of function name to function
  address and function address to function description are recorded in
  the global environment.
- For each global variable, a memory block is allocated and associated to
  the name of the variable.

  These operations reflect (at a high level of abstraction) what takes
  place during program linking and program loading in a real operating
  system. *)

Require Recdef.
Require Import Zwf.
Require Import Axioms Coqlib Errors Maps AST Linking.
Require Import Integers Floats Values Memory.
Require Import Segment.
Require Import FlatAsmGlobdef.

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

Local Open Scope pair_scope.
Local Open Scope error_monad_scope.

Set Implicit Arguments.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module Genv.

(** * Global environments *)

Section GENV.

Variable F: Type.  (**r The type of function descriptions *)
Variable I: Type.  (**r The type of instructions *)

(** The type of global environments. *)

Record t: Type := mkgenv {
  genv_defs: block -> ptrofs -> option F;                 (**r mapping offsets -> function defintions *)
  genv_instrs: block -> ptrofs -> option I;           (**r mapping offset -> instructions *)
  genv_internal_codeblock : block -> bool;
  genv_segblocks: segid_type -> block;
}.

(** ** Lookup functions *)

(** [find_funct_ptr ge ofs] returns the function description associated with
    the given address. *)

Definition find_funct (ge: t) (v:val) : option F :=
  match v with
  | Vptr b ofs => genv_defs ge b ofs
  | _ => None
  end.

Definition label_to_ptr (smap: segid_type -> block) (l:seglabel) : val :=
  Vptr (smap (fst l)) (snd l).


Definition symbol_address ge l ofs := 
  label_to_ptr (genv_segblocks ge) (offset_seglabel l ofs).


Lemma symbol_address_offset : forall ge ofs1 b s ofs,
    symbol_address ge s Ptrofs.zero = Vptr b ofs ->
    symbol_address ge s ofs1 = Vptr b (Ptrofs.add ofs ofs1).
Proof.
  unfold symbol_address. intros. destruct s.
  simpl in *. unfold label_to_ptr in *. inv H.
  rewrite Ptrofs.add_zero. auto.
Qed.

(* Definition get_label_offset (ge: t) (l:seglabel) (ofs:ptrofs): option ptrofs := *)
(*   get_sect_label_offset (genv_smap ge) l ofs. *)

(* Definition get_label_offset0 ge l := *)
(*   get_sect_label_offset0 (genv_smap ge) l. *)

(* Definition get_label_addr (ge: t) (l:sect_label) (ofs:ptrofs) : val := *)
(*   get_sect_label_addr (genv_smap ge) l ofs. *)

(* Definition get_label_addr0 ge l := *)
(*   get_sect_label_addr0 (genv_smap ge) l. *)

(* (** Translate a section block to an offset in the flat memory space *) *)
(* Definition get_block_offset (ge: t) (sb:sect_block) (ofs:ptrofs): option ptrofs := *)
(*   get_sect_block_offset (genv_smap ge) sb ofs. *)

(* Definition get_block_offset0 ge sb := *)
(*   get_sect_block_offset0 (genv_smap ge) sb. *)


(** Find an instruction at an offset *)
Definition find_instr (ge: t) (v:val) : option I :=
  match v with
  | Vptr b ofs => (genv_instrs ge b ofs)
  | _ => None
  end.

End GENV.

End Genv.