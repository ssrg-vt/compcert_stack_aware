(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Feb 28, 2018 *)
(* ******************* *)

(** Injection from memory blocks to section lables **)

Require Import Coqlib Integers Maps Values.
Require Import Memtype Memory.
Require Import Sect.
Require Import Globalenvs FlatAsmGlobenv FlatAsmgen.


Record match_sm_inj (ge: Asm.genv) (gm: GID_MAP_TYPE) (sm: section_map) (mj: meminj) : Type :=
  mkMatchSMInj {
      agree_sm_inj : forall b id sid ofs ofs', 
        Genv.find_symbol ge id = Some b ->
        gm id = Some (sid,ofs) -> PTree.get sid sm = Some ofs' -> 
        mj b = Some (mem_block, Ptrofs.unsigned (Ptrofs.add ofs ofs'));
      agree_instr : 
        Genv.find_symbol ge id = Some b ->
        
    }.
