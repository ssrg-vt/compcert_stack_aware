(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Jan 9, 2018 *)
(* ******************* *)

Require Import Coqlib Integers AST Maps.
Require Import Asm FlatAsm Segment.
Require Import Errors.
Require Import FlatAsmBuiltin FlatAsmGlobdef.
Require Import Memtype.
Import ListNotations.


Local Open Scope error_monad_scope.

(** Translation from CompCert Assembly (RawAsm) to FlatAsm *)

Definition alignw:Z := 8.

Definition stack_segid: segid_type := 1%positive.
Definition data_segid:  segid_type := 2%positive.
Definition code_segid:  segid_type := 3%positive.
Definition extfuns_segid: segid_type := 4%positive.

Definition data_label (ofs:Z) : seglabel := (data_segid, Ptrofs.repr ofs).
Definition code_label (ofs:Z) : seglabel := (code_segid, Ptrofs.repr ofs).
Definition extfun_label (ofs:Z) : seglabel := (extfuns_segid, Ptrofs.repr ofs).

Definition GID_MAP_TYPE := ident -> option seglabel.
Definition LABEL_MAP_TYPE := ident -> Asm.label -> option seglabel.

Definition default_gid_map : GID_MAP_TYPE := fun id => None.
Definition default_label_map : LABEL_MAP_TYPE :=
  fun id l => None.

Definition update_gid_map (id:ident) (l:seglabel) (map:GID_MAP_TYPE) : GID_MAP_TYPE :=
  fun id' => if peq id id' then Some l else (map id').

Definition update_label_map (id:ident) (l:Asm.label) (tl:seglabel) (map:LABEL_MAP_TYPE) : LABEL_MAP_TYPE :=
  fun id' l' => if peq id id' then (if peq l l' then Some tl else (map id' l')) else (map id' l').


Section WITH_GID_MAP.

(** A mapping from global identifiers their locations in sections 
    (i.e. pairs of section ids and offsets) *)
Variable gid_map : GID_MAP_TYPE.

(** * Translation of global variables *)

(** Translation init data *)
Definition transl_init_data (idata: AST.init_data) : res init_data :=
  match idata with 
  | AST.Init_int8 x => OK (Init_int8 x)
  | AST.Init_int16 x => OK (Init_int16 x)
  | AST.Init_int32 x => OK (Init_int32 x)
  | AST.Init_int64 x => OK (Init_int64 x)
  | AST.Init_float32 f => OK (Init_float32 f)
  | AST.Init_float64 f => OK (Init_float64 f)
  | AST.Init_space s => OK (Init_space s)
  | AST.Init_addrof id ofs =>
    match gid_map id with
    | None => Error (MSG "Transation of init data failed: unknown global id" :: nil)
    | Some l => OK (Init_addrof l ofs)
    end
  end.

Fixpoint transl_init_data_list (l : list AST.init_data) : res (list init_data) :=
  match l with 
  | nil => OK nil
  | (i::l1) =>
    do i' <- transl_init_data i;
    do l1' <- transl_init_data_list l1;
    OK (i'::l1')
  end.

(** Translation of a global variable *)
Definition transl_gvar {V:Type} (gvar : AST.globvar V) : res (globvar V) :=
  do idata <- transl_init_data_list (AST.gvar_init gvar);
  OK (
      mkglobvar
        V
        (AST.gvar_info gvar)
        idata
        (AST.gvar_readonly gvar)
        (AST.gvar_volatile gvar)).

(** Translation of global variables *)
Fixpoint transl_globvars (gdefs : list (ident * option (AST.globdef Asm.fundef unit)))
                         : res (list (ident * option FlatAsm.gdef * segblock)) :=
  match gdefs with
  | nil => OK nil
  | ((id, None) :: gdefs') =>
    transl_globvars gdefs'
  | ((_, Some (AST.Gfun _)) :: gdefs') =>
    transl_globvars gdefs'
  | ((id, Some (AST.Gvar v)) :: gdefs') =>
    match gid_map id with
    | None => Error (MSG "Translation of a global variable fails: no address for the variable" :: nil)
    | Some (sid,ofs) =>
      let sz := AST.init_data_list_size (AST.gvar_init v) in
      let sblk := mkSegBlock sid ofs (Ptrofs.repr sz) in
      do tgdefs' <- transl_globvars gdefs';
      do v' <- transl_gvar v;
      OK ((id, Some (Gvar v'), sblk) :: tgdefs')
    end
  end.

(* Fixpoint transl_globvars (ofs:Z) (gdefs : list (ident * option (AST.globdef Asm.fundef unit))) *)
(*                          : res (Z * list (ident * option FlatAsm.gdef * segblock)) := *)
(*   match gdefs with *)
(*   | nil => OK (ofs, nil) *)
(*   | ((id, None) :: gdefs') => *)
(*     transl_globvars ofs gdefs' *)
(*   | ((_, Some (AST.Gfun _)) :: gdefs') => *)
(*     transl_globvars ofs gdefs' *)
(*   | ((id, Some (AST.Gvar v)) :: gdefs') => *)
(*     let sz := AST.init_data_list_size (AST.gvar_init v) in *)
(*     let sblk := mkSegBlock data_segid (Ptrofs.repr ofs) (Ptrofs.repr sz) in *)
(*     let nofs := ofs+sz in *)
(*     do (fofs, tgdefs') <- transl_globvars nofs gdefs'; *)
(*     do v' <- transl_gvar v; *)
(*     OK (fofs, ((id, Some (Gvar v'), sblk) :: tgdefs')) *)
(*   end. *)


(** * Translation of instructions *)

(** Translation of addressing modes *)
Definition transl_addr_mode (m: Asm.addrmode) : res FlatAsm.addrmode :=
  match m with
  | Asm.Addrmode b ofs const =>
    do const' <-
    match const with
    | inl disp => OK (inl disp)
    | inr (id, ofs') => 
      match gid_map id with
      | None => Error (MSG "An id in addressing mode is undefined" :: nil)
      | Some l => OK (inr (l, ofs'))
      end
    end;
    OK (Addrmode b ofs const')
  end.

(** Translation of builtin arguments *)
Fixpoint transl_builtin_arg {A:Type} (arg: AST.builtin_arg A) : res (builtin_arg A) :=
  match arg with
  | AST.BA x => OK (BA A x)
  | AST.BA_int n => OK (BA_int A n)
  | AST.BA_long n => OK (BA_long A n)
  | AST.BA_float f => OK (BA_float A f)
  | AST.BA_single f => OK (BA_single A f)
  | AST.BA_loadstack chunk ofs => OK (BA_loadstack A chunk ofs)
  | AST.BA_addrstack ofs => OK (BA_addrstack A ofs)
  | AST.BA_loadglobal chunk id ofs => 
    match (gid_map id) with
    | None => Error (MSG "translation of builtin arg failed" :: nil)
    | Some l => OK (BA_loadglobal A chunk l ofs)
    end
  | AST.BA_addrglobal id ofs => 
    match (gid_map id) with
    | None => Error (MSG "translation of builtin arg failed" :: nil)
    | Some l => OK (BA_addrglobal A l ofs)
    end
  | AST.BA_splitlong hi lo => 
    do hi' <- transl_builtin_arg hi;
    do lo' <- transl_builtin_arg lo;
    OK (BA_splitlong A hi' lo')
  end.

Fixpoint transl_builtin_args {A:Type} (args: list (AST.builtin_arg A)) : res (list (builtin_arg A)) :=
  match args with
  | nil => OK nil
  | a::args1 =>
    do a'<- transl_builtin_arg a;
    do args' <- transl_builtin_args args1;
    OK (a'::args')
  end.


Section WITH_LABEL_MAP.
(** A mapping from labels in functions to their offsets in the code section *)
Variable label_map : LABEL_MAP_TYPE.

Fixpoint transl_tbl (fid:ident) (tbl: list Asm.label) : res (list seglabel) :=
  match tbl with
  | nil => OK nil
  | l::tbl' =>
    match (label_map fid l) with
    | None => Error (MSG "Unknown label in the jump table" :: nil)
    | Some tl => 
      do rtbl <- transl_tbl fid tbl';
      OK (tl :: rtbl)
    end
  end.

(** Translation of an instruction *)
Definition transl_instr' (fid : ident) (i:Asm.instruction) : res FlatAsm.instruction :=
  match i with
  (** Moves *)
  | Asm.Pmov_rr rd r1 => OK (Pmov_rr rd r1)
  | Asm.Pmovl_ri rd n => OK (Pmovl_ri rd n)
  | Asm.Pmovq_ri rd n => OK (Pmovq_ri rd n)
  | Asm.Pmov_rs rd id => 
    match (gid_map id) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " source id undefined" :: nil)
    | Some l => OK (Pmov_rs rd l)
    end
  | Asm.Pmovl_rm rd a =>
    do a' <- transl_addr_mode a; OK (Pmovl_rm rd a')
  | Asm.Pmovq_rm rd a =>
    do a' <- transl_addr_mode a; OK (Pmovq_rm rd a')
  | Asm.Pmovl_mr a rs =>
    do a' <- transl_addr_mode a; OK (Pmovl_mr a' rs)
  | Asm.Pmovq_mr a rs =>
    do a' <- transl_addr_mode a; OK (Pmovq_mr a' rs)
  | Asm.Pmovsd_ff rd r1 =>  OK (Pmovsd_ff rd r1)
  | Asm.Pmovsd_fi rd n => OK (Pmovsd_fi rd n)
  | Asm.Pmovsd_fm rd a => 
    do a' <- transl_addr_mode a; OK (Pmovsd_fm rd a')
  | Asm.Pmovsd_mf a r1 =>
    do a' <- transl_addr_mode a; OK (Pmovsd_mf a' r1)
  | Asm.Pmovss_fi rd n => OK (Pmovss_fi rd n)
  | Asm.Pmovss_fm rd a => 
    do a' <- transl_addr_mode a; OK (Pmovss_fm rd a')
  | Asm.Pmovss_mf a r1 =>
    do a' <- transl_addr_mode a; OK (Pmovss_mf a' r1)
  | Asm.Pfldl_m a =>
    do a' <- transl_addr_mode a; OK (Pfldl_m a')
  | Asm.Pfstpl_m a =>              
    do a' <- transl_addr_mode a; OK (Pfstpl_m a')
  | Asm.Pflds_m a =>               
    do a' <- transl_addr_mode a; OK (Pflds_m a')
  | Asm.Pfstps_m a =>              
    do a' <- transl_addr_mode a; OK (Pfstps_m a')
  | Asm.Pxchg_rr r1 r2 =>  OK (Pxchg_rr r1 r2)
  (** Moves with conversion *)
  | Asm.Pmovb_mr a rs =>
    do a' <- transl_addr_mode a; OK (Pmovb_mr a' rs)
  | Asm.Pmovw_mr a rs =>
    do a' <- transl_addr_mode a; OK (Pmovw_mr a' rs)
  | Asm.Pmovzb_rr rd rs    => OK (Pmovzb_rr rd rs)
  | Asm.Pmovzb_rm rd a     =>
    do a' <- transl_addr_mode a; OK (Pmovzb_rm rd a')
  | Asm.Pmovsb_rr rd rs    => OK (Pmovsb_rr rd rs)
  | Asm.Pmovsb_rm rd a     =>
    do a' <- transl_addr_mode a; OK (Pmovsb_rm rd a')
  | Asm.Pmovzw_rr rd rs    => OK (Pmovzw_rr rd rs)
  | Asm.Pmovzw_rm rd a     =>
    do a' <- transl_addr_mode a; OK (Pmovzw_rm rd a')
  | Asm.Pmovsw_rr rd rs    => OK (Pmovsw_rr rd rs)
  | Asm.Pmovsw_rm rd a     =>
    do a' <- transl_addr_mode a; OK (Pmovsw_rm rd a')
  | Asm.Pmovzl_rr rd rs    => OK (Pmovzl_rr rd rs)
  | Asm.Pmovsl_rr rd rs    => OK (Pmovsl_rr rd rs)
  | Asm.Pmovls_rr rd       => OK (Pmovls_rr rd)
  | Asm.Pcvtsd2ss_ff rd r1 => OK (Pcvtsd2ss_ff rd r1)
  | Asm.Pcvtss2sd_ff rd r1 => OK (Pcvtss2sd_ff rd r1)
  | Asm.Pcvttsd2si_rf rd r1=> OK (Pcvttsd2si_rf rd r1)
  | Asm.Pcvtsi2sd_fr rd r1 => OK (Pcvtsi2sd_fr rd r1)
  | Asm.Pcvttss2si_rf rd r1=> OK (Pcvttss2si_rf rd r1)
  | Asm.Pcvtsi2ss_fr rd r1 => OK (Pcvtsi2ss_fr rd r1)
  | Asm.Pcvttsd2sl_rf rd r1=> OK (Pcvttsd2sl_rf rd r1)
  | Asm.Pcvtsl2sd_fr rd r1 => OK (Pcvtsl2sd_fr rd r1)
  | Asm.Pcvttss2sl_rf rd r1=> OK (Pcvttss2sl_rf rd r1)
  | Asm.Pcvtsl2ss_fr rd r1 => OK (Pcvtsl2ss_fr rd r1)
  (** Integer arithmetic *)
  | Asm.Pleal rd a       => 
    do a' <- transl_addr_mode a; OK (Pleal rd a')     
  | Asm.Pleaq rd a       => 
    do a' <- transl_addr_mode a; OK (Pleaq rd a')    
  | Asm.Pnegl rd         => OK (Pnegl rd)       
  | Asm.Pnegq rd         => OK (Pnegq rd)       
  | Asm.Paddl_ri rd n    => OK (Paddl_ri rd n)
  | Asm.Paddq_ri rd n    => OK (Paddq_ri rd n)  
  | Asm.Psubl_rr rd r1   => OK (Psubl_rr rd r1) 
  | Asm.Psubq_rr rd r1   => OK (Psubq_rr rd r1) 
  | Asm.Pimull_rr rd r1  => OK (Pimull_rr rd r1)
  | Asm.Pimulq_rr rd r1  => OK (Pimulq_rr rd r1)
  | Asm.Pimull_ri rd n   => OK (Pimull_ri rd n) 
  | Asm.Pimulq_ri rd n   => OK (Pimulq_ri rd n) 
  | Asm.Pimull_r r1      => OK (Pimull_r r1)    
  | Asm.Pimulq_r r1      => OK (Pimulq_r r1)    
  | Asm.Pmull_r r1       => OK (Pmull_r r1)     
  | Asm.Pmulq_r r1       => OK (Pmulq_r r1)     
  | Asm.Pcltd            => OK (Pcltd)
  | Asm.Pcqto            => OK (Pcqto)          
  | Asm.Pdivl r1         => OK (Pdivl r1)
  | Asm.Pdivq r1         => OK (Pdivq r1)       
  | Asm.Pidivl r1        => OK (Pidivl r1)      
  | Asm.Pidivq r1        => OK (Pidivq r1)      
  | Asm.Pandl_rr rd r1   => OK (Pandl_rr rd r1) 
  | Asm.Pandq_rr rd r1   => OK (Pandq_rr rd r1) 
  | Asm.Pandl_ri rd n    => OK (Pandl_ri rd n)  
  | Asm.Pandq_ri rd n    => OK (Pandq_ri rd n)  
  | Asm.Porl_rr rd r1    => OK (Porl_rr rd r1)  
  | Asm.Porq_rr rd r1    => OK (Porq_rr rd r1)  
  | Asm.Porl_ri rd n     => OK (Porl_ri rd n)   
  | Asm.Porq_ri rd n     => OK (Porq_ri rd n)   
  | Asm.Pxorl_r rd       => OK (Pxorl_r rd)               
  | Asm.Pxorq_r rd           => OK (Pxorq_r rd)
  | Asm.Pxorl_rr rd r1       => OK (Pxorl_rr rd r1)
  | Asm.Pxorq_rr rd r1       => OK (Pxorq_rr rd r1  )
  | Asm.Pxorl_ri rd n        => OK (Pxorl_ri rd n   )
  | Asm.Pxorq_ri rd n        => OK (Pxorq_ri rd n   )
  | Asm.Pnotl rd             => OK (Pnotl rd        )
  | Asm.Pnotq rd             => OK (Pnotq rd        )
  | Asm.Psall_rcl rd         => OK (Psall_rcl rd    )
  | Asm.Psalq_rcl rd         => OK (Psalq_rcl rd    )
  | Asm.Psall_ri rd n        => OK (Psall_ri rd n   )
  | Asm.Psalq_ri rd n        => OK (Psalq_ri rd n   )
  | Asm.Pshrl_rcl rd         => OK (Pshrl_rcl rd    )
  | Asm.Pshrq_rcl rd         => OK (Pshrq_rcl rd    )
  | Asm.Pshrl_ri rd n        => OK (Pshrl_ri rd n   )
  | Asm.Pshrq_ri rd n        => OK (Pshrq_ri rd n   )
  | Asm.Psarl_rcl rd         => OK (Psarl_rcl rd    )
  | Asm.Psarq_rcl rd         => OK (Psarq_rcl rd    )
  | Asm.Psarl_ri rd n        => OK (Psarl_ri rd n   )
  | Asm.Psarq_ri rd n        => OK (Psarq_ri rd n   )
  | Asm.Pshld_ri rd r1 n     => OK (Pshld_ri rd r1 n)
  | Asm.Prorl_ri rd n        => OK (Prorl_ri rd n   )
  | Asm.Prorq_ri rd n        => OK (Prorq_ri rd n   )  
  | Asm.Pcmpl_rr r1 r2       => OK (Pcmpl_rr r1 r2  )
  | Asm.Pcmpq_rr r1 r2       => OK (Pcmpq_rr r1 r2  )
  | Asm.Pcmpl_ri r1 n        => OK (Pcmpl_ri r1 n   )
  | Asm.Pcmpq_ri r1 n        => OK (Pcmpq_ri r1 n   )
  | Asm.Ptestl_rr r1 r2      => OK (Ptestl_rr r1 r2 )
  | Asm.Ptestq_rr r1 r2      => OK (Ptestq_rr r1 r2 )
  | Asm.Ptestl_ri r1 n       => OK (Ptestl_ri r1 n  )
  | Asm.Ptestq_ri r1 n       => OK (Ptestq_ri r1 n  )
  | Asm.Pcmov c rd r1        => OK (Pcmov c rd r1   )
  | Asm.Psetcc c rd          => OK (Psetcc c rd     ) 
  (** Floating-point arithmetic *)
  | Asm.Paddd_ff rd r1       => OK (Paddd_ff rd r1   )
  | Asm.Psubd_ff rd r1       => OK (Psubd_ff rd r1   )
  | Asm.Pmuld_ff rd r1       => OK (Pmuld_ff rd r1   )
  | Asm.Pdivd_ff rd r1       => OK (Pdivd_ff rd r1   )
  | Asm.Pnegd rd             => OK (Pnegd rd         )
  | Asm.Pabsd rd             => OK (Pabsd rd         )
  | Asm.Pcomisd_ff r1 r2     => OK (Pcomisd_ff r1 r2 )
  | Asm.Pxorpd_f rd	     => OK (Pxorpd_f rd    )    
  | Asm.Padds_ff rd r1       => OK (Padds_ff rd r1   )
  | Asm.Psubs_ff rd r1       => OK (Psubs_ff rd r1   )
  | Asm.Pmuls_ff rd r1       => OK (Pmuls_ff rd r1   )
  | Asm.Pdivs_ff rd r1       => OK (Pdivs_ff rd r1   )
  | Asm.Pnegs rd             => OK (Pnegs rd         )
  | Asm.Pabss rd             => OK (Pabss rd         )
  | Asm.Pcomiss_ff r1 r2     => OK (Pcomiss_ff r1 r2 )
  | Asm.Pxorps_f rd	     => OK (Pxorps_f rd      ) 	           
  (** Branches and calls *)
  | Asm.Pjmp_l l        => 
    match (label_map fid l) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown label" :: nil)
    | Some tl => OK (Pjmp_l tl)
    end
  | Asm.Pjmp (inr symb) sg =>
    match (gid_map symb) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown symbol" :: nil)
    | Some l => OK (Pjmp_s l sg)
    end
  | Asm.Pjmp (inl r) sg => OK (Pjmp_r r sg)
  | Asm.Pjcc c l =>
    match (label_map fid l) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown label" :: nil)
    | Some tl => OK (Pjcc c tl)
    end
  | Asm.Pjcc2 c1 c2 l =>
    match (label_map fid l) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown label" :: nil)
    | Some tl => OK (Pjcc2 c1 c2 tl)
    end
  | Asm.Pjmptbl r tbl =>
    do tbl' <- transl_tbl fid tbl; OK (Pjmptbl r tbl')
  | Asm.Pcall (inr symb) sg => 
    match (gid_map symb) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown symbol" :: nil)
    | Some l => OK (Pcall_s l sg)
    end
  | Asm.Pcall (inl r) sg => OK (Pcall_r r sg)
  | Asm.Pret => OK (Pret)
  (** Saving and restoring registers *)
  | Asm.Pmov_rm_a rd a   =>
    do a' <- transl_addr_mode a; OK (Pmov_rm_a rd a')
  | Asm.Pmov_mr_a a rs   =>
    do a' <- transl_addr_mode a; OK (Pmov_mr_a a' rs)
  | Asm.Pmovsd_fm_a rd a =>
    do a' <- transl_addr_mode a; OK (Pmovsd_fm_a rd a')
  | Asm.Pmovsd_mf_a a r1 =>
    do a' <- transl_addr_mode a; OK (Pmovsd_mf_a a' r1)
  (** Pseudo-instructions *)
  | Asm.Plabel l => 
    match (label_map fid l) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown label" :: nil)
    | Some tl => OK (Plabel tl)
    end
  | Asm.Pallocframe sz rng ofs_ra => Error (MSG "There should not be allocframe instructions anymore." :: nil)
  | Asm.Pfreeframe sz ofs_ra => Error (MSG "There should not be freeframe instructions anymore." :: nil)
  | Asm.Pload_parent_pointer rd z => Error (MSG "There should not be loadparentpointer instructions anymore." :: nil)
  | Asm.Pbuiltin ef args res =>
    do args' <- transl_builtin_args args;
    OK (Pbuiltin ef args' res)
  (** Instructions not generated by [Asmgen] -- TO CHECK *)
  (* | Padcl_ri rd n *)
  (* | Padcl_rr rd r2 *)
  (* | Paddl_mi a n *)
  (* | Paddl_rr rd r2 *)
  (* | Pbsfl rd r1 *)
  (* | Pbsfq rd r1 *)
  (* | Pbsrl rd r1 *)
  (* | Pbsrq rd r1 *)
  (* | Pbswap64 rd *)
  (* | Pbswap32 rd *)
  (* | Pbswap16 rd *)
  (* | Pcfi_adjust n *)
  (* | Pfmadd132 rd r2 r3 *)
  (* | Pfmadd213 rd r2 r3 *)
  (* | Pfmadd231 rd r2 r3 *)
  (* | Pfmsub132 rd r2 r3 *)
  (* | Pfmsub213 rd r2 r3 *)
  (* | Pfmsub231 rd r2 r3 *)
  (* | Pfnmadd132 rd r2 r3 *)
  (* | Pfnmadd213 rd r2 r3 *)
  (* | Pfnmadd231 rd r2 r3 *)
  (* | Pfnmsub132 rd r2 r3 *)
  (* | Pfnmsub213 rd r2 r3 *)
  (* | Pfnmsub231 rd r2 r3 *)
  (* | Pmaxsd rd r2 *)
  (* | Pminsd rd r2 *)
  (* | Pmovb_rm rd a *)
  (* | Pmovsq_mr  a rs *)
  (* | Pmovsq_rm rd a *)
  (* | Pmovsb *)
  (* | Pmovsw *)
  (* | Pmovw_rm rd ad *)
  (* | Prep_movsl *)
  (* | Psbbl_rr rd r2 *)
  (* | Psqrtsd rd r1 *)
  (* | Psubl_ri rd n *)
  (* | Psubq_ri rd n. *) 
  | _ => 
    Error (MSG (Asm.instr_to_string i) :: MSG " not supported" :: nil)
  end.

Definition transl_instr (ofs:Z) (fid: ident) (sid:segid_type) (i:Asm.instruction) : res FlatAsm.instr_with_info :=
    let sz := instr_size i in
    let sblk := mkSegBlock sid (Ptrofs.repr ofs) (Ptrofs.repr sz) in
    do instr <- transl_instr' fid i;
    OK (instr, sblk).

(** Translation of a sequence of instructions in a function *)
Fixpoint transl_instrs (fid:ident) (sid:segid_type) (ofs:Z) (instrs: list Asm.instruction) : res (Z * list instr_with_info) :=
  match instrs with
  | nil => OK (ofs, nil)
  | i::instrs' =>
    let sz := instr_size i in
    let nofs := ofs+sz in
    do instr <- transl_instr ofs fid sid i;
    do (fofs, tinstrs') <- transl_instrs fid sid nofs instrs';
    OK (fofs, instr :: tinstrs')
  end.

(** Tranlsation of a function *)
Definition transl_fun (fid: ident) (f:Asm.function) : res function :=
  match gid_map fid with
  | None => Error (MSG "Translation of function fails: no address for this function" :: nil)
  | Some (sid, ofs) =>
    let ofs' := Ptrofs.unsigned ofs in
    do (fofs, code') <- transl_instrs fid sid ofs' (Asm.fn_code f);
      if zle fofs Ptrofs.max_unsigned then
        (let sz := (Asm.code_size (Asm.fn_code f))  in
         let sblk := mkSegBlock sid ofs (Ptrofs.repr sz) in
         OK (mkfunction (Asm.fn_sig f) code' sblk))
      else
        Error (MSG "The size of the function exceeds limit" ::nil)
  end.


Definition transl_globdef (id:ident) (def: option (AST.globdef Asm.fundef unit)) 
  : res (option ((ident * option FlatAsm.gdef * segblock) * code)) :=
  match def with
  | None => OK None
  | Some (AST.Gvar v) =>
    match gid_map id with
    | None => Error (MSG "Translation of a global variable fails: no address for the variable" :: nil)
    | Some (sid,ofs) =>
      let sz := AST.init_data_list_size (AST.gvar_init v) in
      let sblk := mkSegBlock sid ofs (Ptrofs.repr sz) in
      do v' <- transl_gvar v;
        OK (Some ((id, Some (Gvar v'), sblk), nil))
    end
  | Some (AST.Gfun f) =>
    match f with
    | External f => 
      match gid_map id with
      | None => Error (MSG "Translation of an external function fails: no address for the function" :: nil)
      | Some (sid, ofs) => 
        let sblk := mkSegBlock sid ofs Ptrofs.one in
        OK (Some ((id, Some (Gfun (External f)), sblk), nil))
      end
    | Internal fd =>
      do fd' <- transl_fun id fd;
        OK (Some ((id, Some (Gfun (Internal fd')), (fn_range fd')), (fn_code fd')))
    end
  end.

Fixpoint transl_globdefs (defs : list (ident * option (AST.globdef Asm.fundef unit))) 
  : res (list (ident * option gdef * segblock) * code) :=
  match defs with
  | nil => OK (nil, nil)
  | (id, def)::defs' =>
    do tdef_code <- transl_globdef id def;
    do (tdefs', c') <- transl_globdefs defs';
    match tdef_code with
     | None => OK (tdefs', c')
     | Some (tdef, c) => OK (tdef :: tdefs', c++c')
     end
  end.
  
(** Translation of a program *)
Definition transl_prog_with_map (p:Asm.program) (data_sz code_sz extfuns_sz:Z): res program := 
  do (defs, code) <- transl_globdefs (AST.prog_defs p);
  OK (Build_program
        defs
        (AST.prog_public p)
        (AST.prog_main p)
        (* (mkSegment stack_segid (Ptrofs.repr Mem.stack_limit)) *)
        (mkSegment data_segid (Ptrofs.repr data_sz))
        (mkSegment code_segid (Ptrofs.repr code_sz), code)
        (mkSegment extfuns_segid (Ptrofs.repr extfuns_sz))
        (Globalenvs.Genv.to_senv (Globalenvs.Genv.globalenv p)))
      .

(* Definition transl_prog_with_map (p:Asm.program) (data_sz code_sz extfuns_sz:Z): res program :=  *)
(*   do data_defs <- transl_globvars (AST.prog_defs p); *)
(*   do (fun_defs, code) <- transl_funs (AST.prog_defs p); *)
(*   do ext_fun_defs <- transl_ext_funs (AST.prog_defs p); *)
(*   OK (Build_program *)
(*         (data_defs ++ fun_defs ++ ext_fun_defs) *)
(*         (AST.prog_public p) *)
(*         (AST.prog_main p) *)
(*         (* (mkSegment stack_segid (Ptrofs.repr Mem.stack_limit)) *) *)
(*         (mkSegment data_segid (Ptrofs.repr data_sz)) *)
(*         (mkSegment code_segid (Ptrofs.repr code_sz), code) *)
(*         (mkSegment extfuns_segid (Ptrofs.repr extfuns_sz))) *)
(*       . *)

End WITH_LABEL_MAP.

End WITH_GID_MAP.


(** * Compute mappings from global identifiers to section labels *)

(* (** Information accumulated during the translation of global data *) *)
(* Record dinfo : Type := *)
(* mkDinfo{ *)
(*   di_size : Z;           (**r The size of the data section traversed so far *) *)
(*   di_map : GID_MAP_TYPE *)
(*                           (**r The mapping from global identifiers to section labels *) *)
(* }. *)


(* (** Update the gid mapping for a single variable *) *)
(* Definition update_gvar_map {V:Type} (di: dinfo) *)
(*            (id:ident) (gvar: AST.globvar V) : dinfo := *)
(*   let sz:= AST.init_data_list_size (AST.gvar_init gvar) in *)
(*   let ofs := align (di_size di) alignw in *)
(*   mkDinfo (ofs + sz) (update_gid_map id (data_label ofs) (di_map di)). *)


(* (** Update the gid mapping for all global variables *) *)
(* Fixpoint update_gvars_map (di:dinfo) (gdefs : list (ident * option (AST.globdef Asm.fundef unit))) *)
(*                          : dinfo := *)
(*   match gdefs with *)
(*   | nil => di *)
(*   | ((id, None) :: gdefs') => *)
(*     update_gvars_map di gdefs' *)
(*   | ((_, Some (AST.Gfun _)) :: gdefs') => *)
(*     update_gvars_map di gdefs' *)
(*   | ((id, Some (AST.Gvar v)) :: gdefs') => *)
(*     let di' := update_gvar_map di id v in *)
(*     update_gvars_map di' gdefs' *)
(*   end. *)


(* (** Update the gid mapping for a single instruction *) *)
(* Record cinfo : Type := *)
(* mkCinfo{ *)
(*   ci_size : Z;           (**r The size of the code section traversed so far *) *)
(*   ci_map : GID_MAP_TYPE;  (**r The mapping from global identifiers to section labels *) *)
(*   ci_lmap : LABEL_MAP_TYPE; (**r The mapping for labels in functions *) *)
(* }. *)


(* (** Update the gid mapping for a single instruction *) *)
(* Definition update_instr_map (fid:ident) (ci:cinfo) (instr:Asm.instr_with_info) : cinfo := *)
(*   let new_lmap := *)
(*       match (fst instr) with *)
(*       | Asm.Plabel l =>  *)
(*         let ofs := ci_size ci in *)
(*         update_label_map fid l (code_label (ofs + instr_size instr)) (ci_lmap ci) *)
(*       | _ => ci_lmap ci *)
(*       end *)
(*   in *)
(*   let sz := si_size (snd instr) in *)
(*   mkCinfo (ci_size ci + sz) (ci_map ci) new_lmap. *)

(* (** Update the gid mapping for a list of instructions *) *)
(* Fixpoint update_instrs_map (fid:ident) (ci:cinfo) (instrs: list Asm.instr_with_info) : cinfo := *)
(*   match instrs with *)
(*   | nil => ci *)
(*   | i::instrs' => *)
(*     let ci' := update_instr_map fid ci i in *)
(*     update_instrs_map fid ci' instrs' *)
(*   end. *)

(* (** Update the gid mapping for all internal functions *) *)
(* Fixpoint update_funs_map (ci:cinfo) (gdefs : list (ident * option (AST.globdef Asm.fundef unit))) *)
(*                          : cinfo := *)
(*   match gdefs with *)
(*   | nil => ci *)
(*   | ((id, None) :: gdefs') => *)
(*     update_funs_map ci gdefs' *)
(*   | ((id, Some (AST.Gfun f)) :: gdefs') => *)
(*     match f with *)
(*     | External _ => update_funs_map ci gdefs' *)
(*     | Internal f => *)
(*       let ofs := align (ci_size ci) alignw in *)
(*       let ci' := mkCinfo ofs *)
(*                          (update_gid_map id (code_label ofs) (ci_map ci)) *)
(*                          (ci_lmap ci) *)
(*       in *)
(*       let ci'' := update_instrs_map id ci' (Asm.fn_code f) in *)
(*       update_funs_map ci'' gdefs' *)
(*     end *)
(*   | ((id, Some (AST.Gvar v)) :: gdefs') => *)
(*     update_funs_map ci gdefs' *)
(*   end. *)


(* (** Update the gid mapping for all external functions *) *)
(* Fixpoint update_extfuns_map (ei: dinfo) (gdefs : list (ident * option (AST.globdef Asm.fundef unit))) *)
(*   : dinfo := *)
(*   match gdefs with *)
(*   | nil => ei *)
(*   | ((id, None) :: gdefs') => *)
(*     update_extfuns_map ei gdefs' *)
(*   | ((id, Some (AST.Gfun f)) :: gdefs') => *)
(*     match f with *)
(*     | External _ =>  *)
(*       let ofs := align (di_size ei) alignw in *)
(*       let ei' := mkDinfo (ofs + alignw) *)
(*                          (update_gid_map id (extfun_label ofs) (di_map ei)) *)
(*       in *)
(*       update_extfuns_map ei' gdefs' *)
(*     | Internal f => *)
(*       update_extfuns_map ei gdefs' *)
(*     end *)
(*   | ((id, Some (AST.Gvar v)) :: gdefs') => *)
(*     update_extfuns_map ei gdefs' *)
(*   end. *)

Definition is_label (i: Asm.instruction) : option Asm.label :=
  match i with
  | Asm.Plabel l => Some l
  | _ => None
  end.

Definition update_instr (lmap: ident -> Asm.label -> option seglabel) (csize: Z) (fid: ident) (i: Asm.instruction) :=
  let csize' := csize + instr_size i in
  let lmap' :=
      match is_label i with
      | Some l => update_label_map fid l (code_label csize') lmap
      | _ => lmap
      end in
  (lmap', csize').

Definition update_instrs lmap csize fid c : LABEL_MAP_TYPE * Z :=
  fold_left (fun (ls : LABEL_MAP_TYPE * Z) i =>
               let '(lmap, csize) := ls in
               update_instr lmap csize fid i) c (lmap, csize).

Definition update_maps_def
           (gmap: ident -> option seglabel)
           (lmap: ident -> Asm.label -> option seglabel)
           (dsize csize efsize: Z) (i: ident) (def: option (AST.globdef Asm.fundef unit)):
  (GID_MAP_TYPE * LABEL_MAP_TYPE * Z * Z * Z) :=
  match def with
  | None => (gmap, lmap, dsize, csize, efsize)
  | Some (AST.Gvar gvar) =>
    let sz:= AST.init_data_list_size (AST.gvar_init gvar) in
    (update_gid_map i (data_label dsize) gmap, lmap, dsize + align sz alignw, csize, efsize)
  | Some (AST.Gfun (External ef)) =>
    (update_gid_map i (extfun_label efsize) gmap, lmap, dsize, csize, efsize + alignw)
  | Some (AST.Gfun (Internal f)) =>
    let (lmap', csize') := update_instrs lmap csize i (Asm.fn_code f) in
    (update_gid_map i (code_label csize) gmap, lmap', dsize, align csize' alignw, efsize)
  end.

Definition update_maps gmap lmap dsize csize efsize defs : (GID_MAP_TYPE * LABEL_MAP_TYPE * Z * Z * Z) :=
  fold_left (fun (acc : GID_MAP_TYPE * LABEL_MAP_TYPE * Z * Z * Z)
               (id: ident * option (AST.globdef Asm.fundef unit)) =>
               let '(gmap, lmap, dsize, csize, efsize) := acc in
               let '(i,def) := id in
               update_maps_def gmap lmap dsize csize efsize i def)
            defs (gmap, lmap, dsize, csize, efsize).

Definition make_maps (p:Asm.program) : (GID_MAP_TYPE * LABEL_MAP_TYPE * Z * Z * Z) :=
  update_maps default_gid_map default_label_map 0 0 0 (AST.prog_defs p).

(* (** Update the gid and label mappings by traversing an Asm program *) *)
(* Definition update_map (p:Asm.program) : res (GID_MAP_TYPE * LABEL_MAP_TYPE * Z * Z * Z) := *)
(*   let init_di := (mkDinfo 0 default_gid_map) in *)
(*   let di := update_gvars_map init_di (AST.prog_defs p) in *)
(*   let data_seg_size := align (di_size di) alignw in *)
(*   let ei := mkDinfo 0 (di_map di) in *)
(*   let ei' := update_extfuns_map ei (AST.prog_defs p) in *)
(*   let extfuns_seg_size := align (di_size ei') alignw in *)
(*   let init_ci := mkCinfo 0 (di_map ei') default_label_map in *)
(*   let final_ci := update_funs_map init_ci (AST.prog_defs p) in *)
(*   let code_seg_size := align (ci_size final_ci) alignw in *)
(*   OK (ci_map final_ci, ci_lmap final_ci, data_seg_size, code_seg_size, extfuns_seg_size). *)


(** Check if the source program is well-formed **)
Definition no_duplicated_defs {F V: Type} (defs: list (ident * option (AST.globdef F V))) :=
  list_norepet (map fst defs).

Fixpoint labels (c: Asm.code) : list Asm.label :=
  match c with
  | [] => []
  | i :: r =>
    match is_label i with
      Some l => l :: labels r
    | None => labels r
    end
  end.

Definition no_duplicated_labels (c: Asm.code)  :=
  list_norepet (labels c).

Definition globdef_no_duplicated_labels (def: option (AST.globdef Asm.fundef unit)) :=
  match def with
  | Some (AST.Gfun (Internal f)) => no_duplicated_labels (Asm.fn_code f)
  | _ => True
  end.

Definition globdef_no_duplicated_labels_dec def : { globdef_no_duplicated_labels def } + { ~ globdef_no_duplicated_labels def }.
Proof.
  unfold globdef_no_duplicated_labels.
  repeat destr.
  apply list_norepet_dec. apply ident_eq.
Defined.

Definition defs_no_duplicated_labels (defs: list (ident * _)) :=
  Forall globdef_no_duplicated_labels (map snd defs).

Definition def_size (def: AST.globdef Asm.fundef unit) : Z :=
  match def with
  | AST.Gfun (External e) => 1
  | AST.Gfun (Internal f) => Asm.code_size (Asm.fn_code f)
  | AST.Gvar v => AST.init_data_list_size (AST.gvar_init v)
  end.

Definition odef_size (def: option (AST.globdef Asm.fundef unit)) : Z :=
  match def with
  | Some def => def_size def
  | _ => 0
  end.

Lemma def_size_pos:
  forall d,
    0 <= def_size d.
Proof.
  unfold def_size. intros.
  destr.
  destr. generalize (code_size_non_neg (Asm.fn_code f0)); omega.
  omega.
  generalize (AST.init_data_list_size_pos (AST.gvar_init v)); omega.
Qed.

Lemma odef_size_pos:
  forall d,
    0 <= odef_size d.
Proof.
  unfold odef_size. intros.
  destr. apply def_size_pos. omega.
Qed.

Definition def_not_empty def : Prop :=
  match def with
  | None => True
  | Some def' => 0 < def_size def'
  end.


Definition defs_not_empty defs :=
  Forall def_not_empty defs.

Definition defs_not_empty_dec defs : { defs_not_empty defs } + { ~ defs_not_empty defs }.
Proof.
  apply Forall_dec. intros. destruct x. 
  - simpl. apply zlt.
  - simpl. left. auto.
Defined.

Definition main_exists main (defs: list (ident * option (AST.globdef Asm.fundef unit))) :=
  Exists (fun '(id, def) => 
            main = id 
            /\ match def with
              | None => False
              | Some _ => True
              end) defs.

Definition main_exists_dec main defs : {main_exists main defs } + {~ main_exists main defs}.
Proof.
  apply Exists_dec. intros. destruct x.
  generalize (ident_eq main i). intros.
  destruct o; inv H.
  - left. auto.
  - right. inversion 1. auto.
  - right. inversion 1. auto.
  - right. inversion 1. auto.
Qed.

Record wf_prog (p:Asm.program) : Prop :=
  {
    wf_prog_not_empty: defs_not_empty (map snd (AST.prog_defs p));
    wf_prog_norepet_defs: list_norepet (map fst (AST.prog_defs p));
    wf_prog_norepet_labels: defs_no_duplicated_labels (AST.prog_defs p);
    wf_prog_main_exists: main_exists (AST.prog_main p) (AST.prog_defs p);
  }.

Definition check_wellformedness p : { wf_prog p } + { ~ wf_prog p }.
Proof.
  destruct (defs_not_empty_dec (map snd (AST.prog_defs p))).
  destruct (list_norepet_dec ident_eq (map fst (AST.prog_defs p))).
  destruct (Forall_dec _ globdef_no_duplicated_labels_dec (map snd (AST.prog_defs p))).
  destruct (main_exists_dec (AST.prog_main p) (AST.prog_defs p)).
  left; constructor; auto.
  right. inversion 1. apply n. apply wf_prog_main_exists0.
  right; inversion 1. apply n. apply wf_prog_norepet_labels0.
  right; inversion 1. apply n. apply wf_prog_norepet_defs0.
  right; inversion 1. apply n. apply wf_prog_not_empty0.
Qed.

(** The full translation *)
Definition transf_program (p:Asm.program) : res program :=
  if check_wellformedness p then
    (let r := make_maps p in
     let '(gmap,lmap,dsize,csize,efsize) := r in
     if zle (dsize + csize + efsize) Ptrofs.max_unsigned then
       transl_prog_with_map gmap lmap p dsize csize efsize
     else
       Error (MSG "Size of segments too big" :: nil))
  else
    Error (MSG "Program not well-formed. There exists duplicated labels or definitions" :: nil). 

