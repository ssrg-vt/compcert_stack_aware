(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Jan 9, 2018 *)
(* ******************* *)

Require Import Coqlib Maps Integers Values AST.

(** * Segments *)

Definition segid_type := ident.
  
(** A segment occupies a region of memory *)
Record segment : Type := mkSegment
{
  segid : segid_type;
  segsize : ptrofs;
}.

(** Label to an offset in a segment *)
Definition seglabel: Type := segid_type * ptrofs.

Definition offset_seglabel (l:seglabel) (ofs:ptrofs) : seglabel :=
  match l with
  | (s,o) => (s, Ptrofs.add o ofs)
  end.

Lemma offset_seglabel_zero : forall l,
  offset_seglabel l Ptrofs.zero = l.
Proof.
  intros l. destruct l. simpl. rewrite Ptrofs.add_zero. auto.
Qed.

(* (** Get the address of a label in a section *) *)
(* Definition get_sect_label_addr0 smap l := *)
(*   match (get_sect_label_offset0 smap l) with *)
(*   | None => Vundef *)
(*   | Some ofs' => flatptr ofs' *)
(*   end. *)
  
(* Definition get_sect_label_addr (smap:section_map) (l:sect_label) (ofs:ptrofs) : val := *)
(*   Val.offset_ptr (get_sect_label_addr0 smap l) ofs. *)


(* (** Get the range of a section *) *)
(* Definition get_section_range (smap:section_map) (s:section) : option (ptrofs * ptrofs) := *)
(*   match PTree.get (section_id s) smap with *)
(*   | None => None *)
(*   | Some ofs => Some (ofs, Ptrofs.add ofs (section_size s)) *)
(*   end. *)


(** * Blocks in a segment *)

Record segblock:Type := mkSegBlock
{
  segblock_id: segid_type;
  segblock_start : ptrofs;  (**r The begining of the block relative to the starting point of the segment *)
  segblock_size : ptrofs;
}.

Definition segblock_to_label (sb: segblock) : seglabel :=
  (segblock_id sb,  segblock_start sb).

(** Get the offset of a block in a section *)
Definition offset_segblock (sb:segblock) (ofs:ptrofs) : seglabel :=
  offset_seglabel (segblock_to_label sb) ofs.

(* (** Get the address of a block *) *)
(* Definition get_segblock_addr b sb ofs : val := *)
(*   get_sect_label_addr smap (sect_block_to_label sb) ofs. *)

(* Definition get_sect_block_addr0 smap sb : val := *)
(*   get_sect_label_addr0 smap (sect_block_to_label sb). *)

(* (** Get the range of a block *) *)
(* Definition get_sect_block_range (smap:section_map) (sb:sect_block) : option (ptrofs * ptrofs) := *)
(*   match PTree.get (sect_block_id sb) smap with *)
(*   | None => None *)
(*   | Some ofs => Some (Ptrofs.add ofs (sect_block_start sb),  *)
(*                       Ptrofs.add ofs (Ptrofs.add (sect_block_start sb) (sect_block_size sb))) *)
(*   end. *)

(* Lemma get_sect_label_offset0_offset : forall sm s ofs ofs', *)
(*   get_sect_label_offset0 sm s = Some ofs ->  *)
(*   get_sect_label_offset sm s ofs' = Some (Ptrofs.add ofs' ofs). *)
(* Proof. *)
(*   unfold get_sect_label_offset. intros. *)
(*   rewrite H. rewrite Ptrofs.add_commut. auto. *)
(* Qed. *)

(* Lemma get_sect_label_offset_incr : forall sm s ofs1 ofs1' ofs2, *)
(*     get_sect_label_offset sm s ofs1 = Some ofs1' -> *)
(*     get_sect_label_offset sm s (Ptrofs.add ofs1 ofs2) = Some (Ptrofs.add ofs1' ofs2). *)
(* Proof. *)
(*   unfold get_sect_label_offset in *. intros. *)
(*   destruct (get_sect_label_offset0 sm s). *)
(*   - inv H. rewrite Ptrofs.add_assoc. auto. *)
(*   - congruence. *)
(* Qed. *)

(* Lemma get_sect_lbl_offset_to_addr : forall sm l ofs ofs', *)
(*     get_sect_label_offset sm l ofs = Some ofs' -> *)
(*     get_sect_label_addr sm l ofs = (flatptr ofs'). *)
(* Proof. *)
(*   intros. unfold get_sect_label_addr. *)
(*   unfold get_sect_label_offset in H. unfold get_sect_label_addr0. *)
(*   destruct (get_sect_label_offset0 sm l); try congruence. *)
(*   inv H; auto. *)
(* Qed. *)
 