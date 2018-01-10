(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Jan 9, 2018 *)
(* ******************* *)

Require Import Coqlib Maps Integers Values AST.

(* A section occupies a region of memory *)
Record section : Type :=
{
  section_id : ident;
  section_size : ptrofs;
}.

(* A block in a section *)
Record sect_block:Type := mkSectBlock
{
  sect_block_id: ident;
  sect_block_start : ptrofs;  (* The begining of the block relative to the starting point of the section *)
  sect_block_size : ptrofs;
}.

(* Mapping from section ids to their offsets in memory *)
Definition section_map := PTree.t ptrofs.

(* Get the offset of a region in a section *)
Definition get_sect_block_ofs (smap:section_map) (sb:sect_block) : option ptrofs :=
  match PTree.get (sect_block_id sb) smap with
  | None => None
  | Some ofs => Some (Ptrofs.add ofs (sect_block_start sb))
  end.

(* Get the range of a section *)
Definition get_section_range (smap:section_map) (s:section) : option (ptrofs * ptrofs) :=
  match PTree.get (section_id s) smap with
  | None => None
  | Some ofs => Some (ofs, Ptrofs.add ofs (section_size s))
  end.

(* Get the range of a block *)
Definition get_sect_block_range (smap:section_map) (sb:sect_block) : option (ptrofs * ptrofs) :=
  match PTree.get (sect_block_id sb) smap with
  | None => None
  | Some ofs => Some (Ptrofs.add ofs (sect_block_start sb), 
                      Ptrofs.add ofs (Ptrofs.add (sect_block_start sb) (sect_block_size sb)))
  end.

(* Label to an offset in a section *)
Definition sect_label: Type := ident * ptrofs.


(* The block id of the flat memory *)
Definition mem_block := 1%positive.

Definition flatptr (ofs:ptrofs) := 
  Vptr mem_block ofs.

(* (* Mapping from identifiers for global variables (functions) to *)
(*    regions in the data (code) section *) *)
(* Definition globids_mapping := positive -> option sect_block.
 *)