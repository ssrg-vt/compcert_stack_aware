(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Jan 9, 2018 *)
(* ******************* *)

Require Import Coqlib Integers AST.
Require Import Asm FlatAsm Sect.
Require Import Errors.


Local Open Scope error_monad_scope.

(** Translation from CompCert Assembly (RawAsm) to FlatAsm *)

Definition stack_sect_id: ident := 1%positive.
Definition data_sect_id:  ident := 2%positive.
Definition code_sect_id:  ident := 3%positive.


(** * Translation of global variables *)

(** Information accumulated during the translation of global data *)
Record data_transl_info : Type :=
mkDataTranslInfo{
  dti_size : ptrofs;           (**r The size of the data section so far *)
  dti_defs : list (ident * globvar unit * sect_block)
                          (**r The global variable translated so far *)
}.

(** Translation of global variables. 
    The main job is to calculate the section block a global variable occupies *)
Fixpoint transl_globvars (gdefs : list (ident * option (globdef Asm.fundef unit)))
                         (dinfo  : data_transl_info)
                         : data_transl_info :=
  match gdefs with
  | nil => dinfo
  | ((id, None) :: gdefs') =>
    transl_globvars gdefs' dinfo
  | ((_, Some (Gfun _)) :: gdefs') =>
    transl_globvars gdefs' dinfo
  | ((id, Some (Gvar v)) :: gdefs') =>
    let sz := Ptrofs.repr (init_data_list_size (gvar_init v)) in
    let ofs := (dti_size dinfo) in
    let sblk := mkSectBlock data_sect_id ofs sz in
    transl_globvars gdefs' 
       (mkDataTranslInfo (Ptrofs.add ofs sz)
                         ((id, v, sblk)::(dti_defs dinfo)))
  end.
         

(* (* Given a FlatAsm instruciton, encode returns the size of its machine encoding *) *)
(* Variable encode : FlatAsm.instruction -> ptrofs. *)


(** * Translation of instructions *)

Section WITH_GID_MAP.

(** A mapping from global identifiers their locations in sections 
    (i.e. pairs of section ids and offsets) *)
Variable gid_map : ident -> option sect_label.


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


Section WITH_LABEL_MAP.
(** A mapping from labels in functions to their offsets in the code section *)
Variable label_map : ident -> Asm.label -> option ptrofs.

Definition code_label (ofs:ptrofs) : sect_label := (code_sect_id, ofs).

Fixpoint transl_tbl (fid:ident) (tbl: list Asm.label) : res (list sect_label) :=
  match tbl with
  | nil => OK nil
  | l::tbl' =>
    match (label_map fid l) with
    | None => Error (MSG "Unknown label in the jump table" :: nil)
    | Some ofs => 
      do rtbl <- transl_tbl fid tbl';
      OK (code_label ofs :: rtbl)
    end
  end.

(** Translation of an instruction *)
Definition transl_instr (fid : ident) (i:Asm.instruction) : res FlatAsm.instruction :=
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
  | Asm.Pcvtss2sd_ff rd r1 => OK (Pcvtss2sd_ff rd r1 )
  | Asm.Pcvttsd2si_rf rd r1=> OK (Pcvttsd2si_rf rd r1)
  | Asm.Pcvtsi2sd_fr rd r1 => OK (Pcvtsi2sd_fr rd r1 )
  | Asm.Pcvttss2si_rf rd r1=> OK (Pcvttss2si_rf rd r1)
  | Asm.Pcvtsi2ss_fr rd r1 => OK (Pcvtsi2ss_fr rd r1 )
  | Asm.Pcvttsd2sl_rf rd r1=> OK (Pcvttsd2sl_rf rd r1)
  | Asm.Pcvtsl2sd_fr rd r1 => OK (Pcvtsl2sd_fr rd r1 )
  | Asm.Pcvttss2sl_rf rd r1=> OK (Pcvttss2sl_rf rd r1)
  | Asm.Pcvtsl2ss_fr rd r1 => OK (Pcvtsl2ss_fr rd r1 )
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
  | Asm.Pcltd            => OK Pcltd          
  | Asm.Pcqto            => OK Pcqto          
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
  | Asm.Pxorq_r rd           => OK (Pxorq_r rd      )
  | Asm.Pxorl_rr rd r1       => OK (Pxorl_rr rd r1  )
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
    | Some ofs => OK (Pjmp_l (code_label ofs))
    end
  | Asm.Pjmp_s symb sg =>
    match (gid_map symb) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown symbol" :: nil)
    | Some l => OK (Pjmp_s l sg)
    end
  | Asm.Pjmp_r r sg => OK (Pjmp_r r sg)
  | Asm.Pjcc c l =>
    match (label_map fid l) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown label" :: nil)
    | Some ofs => OK (Pjcc c (code_label ofs))
    end
  | Asm.Pjcc2 c1 c2 l =>
    match (label_map fid l) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown label" :: nil)
    | Some ofs => OK (Pjcc2 c1 c2 (code_label ofs))
    end
  | Asm.Pjmptbl r tbl =>
    do tbl' <- transl_tbl fid tbl; OK (Pjmptbl r tbl')
  | Asm.Pcall_s symb sg => 
    match (gid_map symb) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown symbol" :: nil)
    | Some l => OK (Pcall_s l sg)
    end
  | Asm.Pcall_r r sg => OK (Pcall_r r sg)
  | Asm.Pret => OK Pret
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
    Error (MSG "transl_instr does not deal with Plabel" :: nil)
  (* | Pallocframeframe(ofs_ra ofs_link: ptrofs) *)
  (* | Pfreeframe sz (ofs_ra ofs_link: ptrofs) *)
  (* | Pbuiltinef(args: list (builtin_arg preg))res *)
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

End WITH_LABEL_MAP.

End WITH_GID_MAP.
