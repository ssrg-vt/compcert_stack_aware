Require Import Coqlib Maps Integers Values.

Definition sect_id:Type := positive.

(* A block of locations (offsets and sizes) in a section *)
Definition sect_block:Type := sect_id * Z * Z.

Definition section_map := PTree.t Z.

(* The block id of the flat memory *)
Definition mem_block := 1%positive.

Definition flatptr (ofs:Z) := 
  Vptr mem_block (Ptrofs.repr ofs).


(* (* Mapping from identifiers for global variables (functions) to *)
(*    regions in the data (code) section *) *)
(* Definition globids_mapping := positive -> option sect_block.
 *)