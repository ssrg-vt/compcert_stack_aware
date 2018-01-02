Require Import Coqlib Integers Values.

Definition sect_id:Type := positive.

(* A block of locations (offsets and sizes) in a section *)
Definition sect_block:Type := sect_id * Z * Z.

Definition section_map := sect_id -> option Z.

(* The block id of the flat memory *)
Definition mem_block := 1%positive.

Definition flatptr (ofs:Z) := 
  Vptr mem_block (Ptrofs.repr ofs).