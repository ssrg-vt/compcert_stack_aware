(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Jan 9, 2018 *)
(* ******************* *)

Require Import Coqlib Maps Integers Values AST.

(** * Flat memory *)
(** The block id of the flat memory *)
Definition mem_block := 1%positive.

Definition flatptr (ofs:ptrofs) := 
  Vptr mem_block ofs.


(** * Sections *)

(** A section occupies a region of memory *)
Record section : Type :=
{
  section_id : ident;
  section_size : ptrofs;
}.

(** Label to an offset in a section *)
Definition sect_label: Type := ident * ptrofs.

(** Mapping from section ids to their offsets in memory *)
Definition section_map := PTree.t ptrofs.

(** Get the offset of a label in a section *)
Definition get_sect_label_offset (smap:section_map) (l:sect_label) (ofs:ptrofs) : option ptrofs :=
  match PTree.get (fst l) smap with
  | None => None
  | Some ss => Some (Ptrofs.add (Ptrofs.add ss (snd l)) ofs)
  end.

Definition get_sect_label_offset0 smap l :=
  get_sect_label_offset smap l Ptrofs.zero.

(** Get the address of a label in a section *)
Definition get_sect_label_addr (smap:section_map) (l:sect_label) (ofs:ptrofs) : val :=
  match (get_sect_label_offset smap l ofs) with
  | None => Vundef
  | Some ofs' => flatptr ofs'
  end.

Definition get_sect_label_addr0 smap l :=
  get_sect_label_addr smap l Ptrofs.zero.

(** Get the range of a section *)
Definition get_section_range (smap:section_map) (s:section) : option (ptrofs * ptrofs) :=
  match PTree.get (section_id s) smap with
  | None => None
  | Some ofs => Some (ofs, Ptrofs.add ofs (section_size s))
  end.


(** * Section blocks *)

(** A block in a section *)
Record sect_block:Type := mkSectBlock
{
  sect_block_id: ident;
  sect_block_start : ptrofs;  (**r The begining of the block relative to the starting point of the section *)
  sect_block_size : ptrofs;
}.

Definition sect_block_to_label (sb: sect_block) : sect_label :=
  (sect_block_id sb,  sect_block_start sb).

(** Get the offset of a block in a section *)
Definition get_sect_block_offset (smap:section_map) (sb:sect_block) (ofs:ptrofs) : option ptrofs :=
  get_sect_label_offset smap (sect_block_to_label sb) ofs.

Definition get_sect_block_offset0 smap sb :=
  get_sect_block_offset smap sb Ptrofs.zero.

(** Get the address of a block *)
Definition get_sect_block_addr smap sb ofs : val :=
  match (get_sect_block_offset smap sb ofs) with
  | None => Vundef
  | Some ofs' => flatptr ofs'
  end.

Definition get_sect_block_addr0 smap sb : val :=
  get_sect_block_addr smap sb Ptrofs.zero.

(** Get the range of a block *)
Definition get_sect_block_range (smap:section_map) (sb:sect_block) : option (ptrofs * ptrofs) :=
  match PTree.get (sect_block_id sb) smap with
  | None => None
  | Some ofs => Some (Ptrofs.add ofs (sect_block_start sb), 
                      Ptrofs.add ofs (Ptrofs.add (sect_block_start sb) (sect_block_size sb)))
  end.

