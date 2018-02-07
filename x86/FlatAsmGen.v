(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Jan 9, 2018 *)
(* ******************* *)

Require Import Coqlib Integers AST Maps.
Require Import Asm FlatAsm Sect.
Require Import Errors.
Require Import FlatAsmBuiltin FlatAsmGlobdef.
Require Import Memtype.
Import ListNotations.


Local Open Scope error_monad_scope.

(** Translation from CompCert Assembly (RawAsm) to FlatAsm *)


Definition stack_sect_id: ident := 1%positive.
Definition data_sect_id:  ident := 2%positive.
Definition code_sect_id:  ident := 3%positive.
Definition extfuns_sect_id: ident := 4%positive.

Definition data_label (ofs:Z) : sect_label := (data_sect_id, Ptrofs.repr ofs).
Definition code_label (ofs:Z) : sect_label := (code_sect_id, Ptrofs.repr ofs).

Definition ENCODE_TYPE := FlatAsm.instruction -> res Z.
Definition GID_MAP_TYPE := ident -> option sect_label.
Definition LABEL_MAP_TYPE := ident -> Asm.label -> option Z.

Definition default_gid_map : GID_MAP_TYPE := fun id => None.
Definition default_label_map : LABEL_MAP_TYPE :=
  fun id l => None.

Definition update_gid_map (id:ident) (l:sect_label) (map:GID_MAP_TYPE) : GID_MAP_TYPE :=
  fun id' => if peq id id' then Some l else (map id').

Definition update_label_map (id:ident) (l:Asm.label) (ofs:Z) (map:LABEL_MAP_TYPE) : LABEL_MAP_TYPE :=
  fun id' l' => if peq id id' then (if peq l l' then Some ofs else (map id' l')) else (map id' l').


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
Fixpoint transl_globvars (ofs:Z) (gdefs : list (ident * option (AST.globdef Asm.fundef unit)))
                         : res (Z * list (ident * option FlatAsm.gdef * sect_block)) :=
  match gdefs with
  | nil => OK (ofs, nil)
  | ((id, None) :: gdefs') =>
    transl_globvars ofs gdefs'
  | ((_, Some (AST.Gfun _)) :: gdefs') =>
    transl_globvars ofs gdefs'
  | ((id, Some (AST.Gvar v)) :: gdefs') =>
    let sz := AST.init_data_list_size (AST.gvar_init v) in
    let sblk := mkSectBlock data_sect_id (Ptrofs.repr ofs) (Ptrofs.repr sz) in
    let nofs := ofs+sz in
    do (fofs, tgdefs') <- transl_globvars nofs gdefs';
    do v' <- transl_gvar v;
    OK (fofs, ((id, Some (Gvar v'), sblk) :: tgdefs'))
  end.




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
Definition transl_instr (fid : ident) (i:Asm.instruction) : res (list FlatAsm.instruction) :=
  match i with
  (** Moves *)
  | Asm.Pmov_rr rd r1 => OK (Pmov_rr rd r1 :: nil)
  | Asm.Pmovl_ri rd n => OK (Pmovl_ri rd n :: nil)
  | Asm.Pmovq_ri rd n => OK (Pmovq_ri rd n :: nil)
  | Asm.Pmov_rs rd id => 
    match (gid_map id) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " source id undefined" :: nil)
    | Some l => OK (Pmov_rs rd l :: nil)
    end
  | Asm.Pmovl_rm rd a =>
    do a' <- transl_addr_mode a; OK (Pmovl_rm rd a' :: nil)
  | Asm.Pmovq_rm rd a =>
    do a' <- transl_addr_mode a; OK (Pmovq_rm rd a' :: nil)
  | Asm.Pmovl_mr a rs =>
    do a' <- transl_addr_mode a; OK (Pmovl_mr a' rs :: nil)
  | Asm.Pmovq_mr a rs =>
    do a' <- transl_addr_mode a; OK (Pmovq_mr a' rs :: nil)
  | Asm.Pmovsd_ff rd r1 =>  OK (Pmovsd_ff rd r1 :: nil)
  | Asm.Pmovsd_fi rd n => OK (Pmovsd_fi rd n :: nil)
  | Asm.Pmovsd_fm rd a => 
    do a' <- transl_addr_mode a; OK (Pmovsd_fm rd a' :: nil)
  | Asm.Pmovsd_mf a r1 =>
    do a' <- transl_addr_mode a; OK (Pmovsd_mf a' r1 :: nil)
  | Asm.Pmovss_fi rd n => OK (Pmovss_fi rd n :: nil)
  | Asm.Pmovss_fm rd a => 
    do a' <- transl_addr_mode a; OK (Pmovss_fm rd a' :: nil)
  | Asm.Pmovss_mf a r1 =>
    do a' <- transl_addr_mode a; OK (Pmovss_mf a' r1 :: nil)
  | Asm.Pfldl_m a =>
    do a' <- transl_addr_mode a; OK (Pfldl_m a' :: nil)
  | Asm.Pfstpl_m a =>              
    do a' <- transl_addr_mode a; OK (Pfstpl_m a' :: nil)
  | Asm.Pflds_m a =>               
    do a' <- transl_addr_mode a; OK (Pflds_m a' :: nil)
  | Asm.Pfstps_m a =>              
    do a' <- transl_addr_mode a; OK (Pfstps_m a' :: nil)
  | Asm.Pxchg_rr r1 r2 =>  OK (Pxchg_rr r1 r2 :: nil)
  (** Moves with conversion *)
  | Asm.Pmovb_mr a rs =>
    do a' <- transl_addr_mode a; OK (Pmovb_mr a' rs :: nil)
  | Asm.Pmovw_mr a rs =>
    do a' <- transl_addr_mode a; OK (Pmovw_mr a' rs :: nil)
  | Asm.Pmovzb_rr rd rs    => OK (Pmovzb_rr rd rs :: nil)
  | Asm.Pmovzb_rm rd a     =>
    do a' <- transl_addr_mode a; OK (Pmovzb_rm rd a' :: nil)
  | Asm.Pmovsb_rr rd rs    => OK (Pmovsb_rr rd rs :: nil)
  | Asm.Pmovsb_rm rd a     =>
    do a' <- transl_addr_mode a; OK (Pmovsb_rm rd a' :: nil)
  | Asm.Pmovzw_rr rd rs    => OK (Pmovzw_rr rd rs :: nil)
  | Asm.Pmovzw_rm rd a     =>
    do a' <- transl_addr_mode a; OK (Pmovzw_rm rd a' :: nil)
  | Asm.Pmovsw_rr rd rs    => OK (Pmovsw_rr rd rs :: nil)
  | Asm.Pmovsw_rm rd a     =>
    do a' <- transl_addr_mode a; OK (Pmovsw_rm rd a' :: nil)
  | Asm.Pmovzl_rr rd rs    => OK (Pmovzl_rr rd rs :: nil)
  | Asm.Pmovsl_rr rd rs    => OK (Pmovsl_rr rd rs :: nil)
  | Asm.Pmovls_rr rd       => OK (Pmovls_rr rd :: nil)
  | Asm.Pcvtsd2ss_ff rd r1 => OK (Pcvtsd2ss_ff rd r1 :: nil)
  | Asm.Pcvtss2sd_ff rd r1 => OK (Pcvtss2sd_ff rd r1 :: nil)
  | Asm.Pcvttsd2si_rf rd r1=> OK (Pcvttsd2si_rf rd r1 :: nil)
  | Asm.Pcvtsi2sd_fr rd r1 => OK (Pcvtsi2sd_fr rd r1 :: nil)
  | Asm.Pcvttss2si_rf rd r1=> OK (Pcvttss2si_rf rd r1 :: nil)
  | Asm.Pcvtsi2ss_fr rd r1 => OK (Pcvtsi2ss_fr rd r1 :: nil)
  | Asm.Pcvttsd2sl_rf rd r1=> OK (Pcvttsd2sl_rf rd r1 :: nil)
  | Asm.Pcvtsl2sd_fr rd r1 => OK (Pcvtsl2sd_fr rd r1 :: nil)
  | Asm.Pcvttss2sl_rf rd r1=> OK (Pcvttss2sl_rf rd r1 :: nil)
  | Asm.Pcvtsl2ss_fr rd r1 => OK (Pcvtsl2ss_fr rd r1 :: nil)
  (** Integer arithmetic *)
  | Asm.Pleal rd a       => 
    do a' <- transl_addr_mode a; OK (Pleal rd a' :: nil)     
  | Asm.Pleaq rd a       => 
    do a' <- transl_addr_mode a; OK (Pleaq rd a' :: nil)    
  | Asm.Pnegl rd         => OK (Pnegl rd :: nil)       
  | Asm.Pnegq rd         => OK (Pnegq rd :: nil)       
  | Asm.Paddl_ri rd n    => OK (Paddl_ri rd n :: nil)
  | Asm.Paddq_ri rd n    => OK (Paddq_ri rd n :: nil)  
  | Asm.Psubl_rr rd r1   => OK (Psubl_rr rd r1 :: nil) 
  | Asm.Psubq_rr rd r1   => OK (Psubq_rr rd r1 :: nil) 
  | Asm.Pimull_rr rd r1  => OK (Pimull_rr rd r1 :: nil)
  | Asm.Pimulq_rr rd r1  => OK (Pimulq_rr rd r1 :: nil)
  | Asm.Pimull_ri rd n   => OK (Pimull_ri rd n :: nil) 
  | Asm.Pimulq_ri rd n   => OK (Pimulq_ri rd n :: nil) 
  | Asm.Pimull_r r1      => OK (Pimull_r r1 :: nil)    
  | Asm.Pimulq_r r1      => OK (Pimulq_r r1 :: nil)    
  | Asm.Pmull_r r1       => OK (Pmull_r r1 :: nil)     
  | Asm.Pmulq_r r1       => OK (Pmulq_r r1 :: nil)     
  | Asm.Pcltd            => OK (Pcltd :: nil)
  | Asm.Pcqto            => OK (Pcqto :: nil)          
  | Asm.Pdivl r1         => OK (Pdivl r1 :: nil)
  | Asm.Pdivq r1         => OK (Pdivq r1 :: nil)       
  | Asm.Pidivl r1        => OK (Pidivl r1 :: nil)      
  | Asm.Pidivq r1        => OK (Pidivq r1 :: nil)      
  | Asm.Pandl_rr rd r1   => OK (Pandl_rr rd r1 :: nil) 
  | Asm.Pandq_rr rd r1   => OK (Pandq_rr rd r1 :: nil) 
  | Asm.Pandl_ri rd n    => OK (Pandl_ri rd n :: nil)  
  | Asm.Pandq_ri rd n    => OK (Pandq_ri rd n :: nil)  
  | Asm.Porl_rr rd r1    => OK (Porl_rr rd r1 :: nil)  
  | Asm.Porq_rr rd r1    => OK (Porq_rr rd r1 :: nil)  
  | Asm.Porl_ri rd n     => OK (Porl_ri rd n :: nil)   
  | Asm.Porq_ri rd n     => OK (Porq_ri rd n :: nil)   
  | Asm.Pxorl_r rd       => OK (Pxorl_r rd :: nil)               
  | Asm.Pxorq_r rd           => OK (Pxorq_r rd :: nil)
  | Asm.Pxorl_rr rd r1       => OK (Pxorl_rr rd r1 :: nil)
  | Asm.Pxorq_rr rd r1       => OK (Pxorq_rr rd r1 :: nil  )
  | Asm.Pxorl_ri rd n        => OK (Pxorl_ri rd n  :: nil  )
  | Asm.Pxorq_ri rd n        => OK (Pxorq_ri rd n  :: nil  )
  | Asm.Pnotl rd             => OK (Pnotl rd       :: nil  )
  | Asm.Pnotq rd             => OK (Pnotq rd       :: nil  )
  | Asm.Psall_rcl rd         => OK (Psall_rcl rd   :: nil  )
  | Asm.Psalq_rcl rd         => OK (Psalq_rcl rd   :: nil  )
  | Asm.Psall_ri rd n        => OK (Psall_ri rd n  :: nil  )
  | Asm.Psalq_ri rd n        => OK (Psalq_ri rd n  :: nil  )
  | Asm.Pshrl_rcl rd         => OK (Pshrl_rcl rd   :: nil  )
  | Asm.Pshrq_rcl rd         => OK (Pshrq_rcl rd   :: nil  )
  | Asm.Pshrl_ri rd n        => OK (Pshrl_ri rd n  :: nil  )
  | Asm.Pshrq_ri rd n        => OK (Pshrq_ri rd n  :: nil  )
  | Asm.Psarl_rcl rd         => OK (Psarl_rcl rd   :: nil  )
  | Asm.Psarq_rcl rd         => OK (Psarq_rcl rd   :: nil  )
  | Asm.Psarl_ri rd n        => OK (Psarl_ri rd n  :: nil  )
  | Asm.Psarq_ri rd n        => OK (Psarq_ri rd n  :: nil  )
  | Asm.Pshld_ri rd r1 n     => OK (Pshld_ri rd r1 n :: nil)
  | Asm.Prorl_ri rd n        => OK (Prorl_ri rd n    :: nil)
  | Asm.Prorq_ri rd n        => OK (Prorq_ri rd n    :: nil)  
  | Asm.Pcmpl_rr r1 r2       => OK (Pcmpl_rr r1 r2   :: nil)
  | Asm.Pcmpq_rr r1 r2       => OK (Pcmpq_rr r1 r2   :: nil)
  | Asm.Pcmpl_ri r1 n        => OK (Pcmpl_ri r1 n    :: nil)
  | Asm.Pcmpq_ri r1 n        => OK (Pcmpq_ri r1 n    :: nil)
  | Asm.Ptestl_rr r1 r2      => OK (Ptestl_rr r1 r2  :: nil)
  | Asm.Ptestq_rr r1 r2      => OK (Ptestq_rr r1 r2  :: nil)
  | Asm.Ptestl_ri r1 n       => OK (Ptestl_ri r1 n   :: nil)
  | Asm.Ptestq_ri r1 n       => OK (Ptestq_ri r1 n   :: nil)
  | Asm.Pcmov c rd r1        => OK (Pcmov c rd r1    :: nil)
  | Asm.Psetcc c rd          => OK (Psetcc c rd      :: nil) 
  (** Floating-point arithmetic *)
  | Asm.Paddd_ff rd r1       => OK (Paddd_ff rd r1    :: nil)
  | Asm.Psubd_ff rd r1       => OK (Psubd_ff rd r1    :: nil)
  | Asm.Pmuld_ff rd r1       => OK (Pmuld_ff rd r1    :: nil)
  | Asm.Pdivd_ff rd r1       => OK (Pdivd_ff rd r1    :: nil)
  | Asm.Pnegd rd             => OK (Pnegd rd          :: nil)
  | Asm.Pabsd rd             => OK (Pabsd rd          :: nil)
  | Asm.Pcomisd_ff r1 r2     => OK (Pcomisd_ff r1 r2  :: nil)
  | Asm.Pxorpd_f rd	     => OK (Pxorpd_f rd   :: nil  )    
  | Asm.Padds_ff rd r1       => OK (Padds_ff rd r1    :: nil)
  | Asm.Psubs_ff rd r1       => OK (Psubs_ff rd r1    :: nil)
  | Asm.Pmuls_ff rd r1       => OK (Pmuls_ff rd r1    :: nil)
  | Asm.Pdivs_ff rd r1       => OK (Pdivs_ff rd r1    :: nil)
  | Asm.Pnegs rd             => OK (Pnegs rd          :: nil)
  | Asm.Pabss rd             => OK (Pabss rd          :: nil)
  | Asm.Pcomiss_ff r1 r2     => OK (Pcomiss_ff r1 r2  :: nil)
  | Asm.Pxorps_f rd	     => OK (Pxorps_f rd       :: nil) 	           
  (** Branches and calls *)
  | Asm.Pjmp_l l        => 
    match (label_map fid l) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown label" :: nil)
    | Some ofs => OK (Pjmp_l (code_label ofs) :: nil)
    end
  | Asm.Pjmp_s symb sg =>
    match (gid_map symb) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown symbol" :: nil)
    | Some l => OK (Pjmp_s l sg :: nil)
    end
  | Asm.Pjmp_r r sg => OK (Pjmp_r r sg :: nil)
  | Asm.Pjcc c l =>
    match (label_map fid l) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown label" :: nil)
    | Some ofs => OK (Pjcc c (code_label ofs) :: nil)
    end
  | Asm.Pjcc2 c1 c2 l =>
    match (label_map fid l) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown label" :: nil)
    | Some ofs => OK (Pjcc2 c1 c2 (code_label ofs) :: nil)
    end
  | Asm.Pjmptbl r tbl =>
    do tbl' <- transl_tbl fid tbl; OK (Pjmptbl r tbl' :: nil)
  | Asm.Pcall_s symb sg => 
    match (gid_map symb) with
    | None => Error (MSG (Asm.instr_to_string i) :: MSG " unknown symbol" :: nil)
    | Some l => OK (Pcall_s l sg :: nil)
    end
  | Asm.Pcall_r r sg => OK (Pcall_r r sg :: nil)
  | Asm.Pret => OK (Pret :: nil)
  (** Saving and restoring registers *)
  | Asm.Pmov_rm_a rd a   =>
    do a' <- transl_addr_mode a; OK (Pmov_rm_a rd a' :: nil)
  | Asm.Pmov_mr_a a rs   =>
    do a' <- transl_addr_mode a; OK (Pmov_mr_a a' rs :: nil)
  | Asm.Pmovsd_fm_a rd a =>
    do a' <- transl_addr_mode a; OK (Pmovsd_fm_a rd a' :: nil)
  | Asm.Pmovsd_mf_a a r1 =>
    do a' <- transl_addr_mode a; OK (Pmovsd_mf_a a' r1 :: nil)
  (** Pseudo-instructions *)
  | Asm.Plabel l => OK nil
  | Asm.Pallocframe fi ofs_ra ofs_link =>
    OK (Pallocframe fi ofs_ra ofs_link :: nil)
  | Asm.Pfreeframe sz ofs_ra ofs_link =>
    OK (Pfreeframe sz ofs_ra ofs_link :: nil)
  | Asm.Pbuiltin ef args res =>
    do args' <- transl_builtin_args args;
    OK (Pbuiltin ef args' res :: nil)
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

Section WITH_ENCODE_FUN.

(** Given a FlatAsm instruciton, encode returns the size of its machine encoding *)
Variable encode : FlatAsm.instruction -> res Z.

Fixpoint encode_instrs (c:list FlatAsm.instruction) (ofs:Z) : res (Z * list instr_with_info) :=
  match c with
  | nil => OK (ofs, nil)
  | i::c' =>
    do sz <- encode i;
    do (fofs, code) <- encode_instrs c' (ofs+sz);
    let sblk := mkSectBlock code_sect_id (Ptrofs.repr ofs) (Ptrofs.repr sz) in
    OK (fofs, ((i, sblk)::code))
  end.


(** Translation of a sequence of instructions in a function *)
Fixpoint transl_instrs (fid:ident) (ofs:Z) (instrs: list Asm.instruction) : res (Z * list instr_with_info) :=
  match instrs with
  | nil => OK (ofs, nil)
  | i::instrs' =>
    do instrs <- transl_instr fid i;
    do (nofs, code) <- encode_instrs instrs ofs;
    do (fofs, tinstrs') <- transl_instrs fid nofs instrs';
    OK (fofs, code ++ tinstrs')
  end.

(** Tranlsation of a function *)
Definition transl_fun (fid: ident) (ofs:Z) (f:Asm.function) : res (Z* function) :=
  do (fofs, code') <- transl_instrs fid ofs (Asm.fn_code f);
  let sz := fofs - ofs in
  let sblk := mkSectBlock code_sect_id (Ptrofs.repr ofs) (Ptrofs.repr sz) in
  OK (fofs, (mkfunction (Asm.fn_sig f) code' (Asm.fn_frame f) sblk)).

(** Translation of internal functions *)
Fixpoint transl_funs (ofs:Z) (gdefs : list (ident * option (AST.globdef Asm.fundef unit)))
                         : res (Z * list (ident * option FlatAsm.gdef * sect_block) * code) :=
  match gdefs with
  | nil => OK (ofs, nil, nil)
  | ((id, None) :: gdefs') =>
    transl_funs ofs gdefs'
  | ((id, Some (AST.Gfun f)) :: gdefs') =>
    match f with
    | External f => 
      transl_funs ofs gdefs'
    | Internal fd =>
      do (nofs, fd') <- transl_fun id ofs fd;
      do (h, code') <- transl_funs nofs gdefs';
      let (fofs, tgdefs') := h in
      OK (fofs, (id, Some (Gfun (Internal fd')), (fn_range fd'))::tgdefs', (fn_code fd')++code')
    end
  | ((id, Some (AST.Gvar v)) :: gdefs') =>
    transl_funs ofs gdefs'
  end.

(** Translation of external functions *)
Fixpoint transl_ext_funs (ofs:Z) (gdefs : list (ident * option (AST.globdef Asm.fundef unit)))
                         : res (Z * list (ident * option FlatAsm.gdef * sect_block)) :=
  match gdefs with
  | nil => OK (ofs, nil)
  | ((id, None) :: gdefs') =>
    transl_ext_funs ofs gdefs'
  | ((id, Some (AST.Gfun f)) :: gdefs') =>
    match f with
    | External f => 
      (* We assume an external function only occupies one byte *)
      let nofs := ofs+1 in
      let sblk := mkSectBlock extfuns_sect_id (Ptrofs.repr nofs) (Ptrofs.repr 1) in
      do (fofs, tgdefs') <- transl_ext_funs nofs gdefs';
      OK (fofs, (id, Some (Gfun (External f)), sblk)::tgdefs')
    | Internal fd =>
      transl_ext_funs ofs gdefs'
    end
  | ((id, Some (AST.Gvar v)) :: gdefs') =>
    transl_ext_funs ofs gdefs'
  end.


Section WITHMEMORYMODELOPS.
Context `{memory_model_ops: Mem.MemoryModelOps}.

Definition gen_smap (ds_size cs_size : Z) : res section_map :=
  if zle (ds_size + cs_size + Mem.stack_limit) Ptrofs.modulus then
    let t1 := PTree.set stack_sect_id (Ptrofs.repr (Ptrofs.modulus - Mem.stack_limit)) (PTree.empty _) in
    let t2 := PTree.set code_sect_id (Ptrofs.repr ds_size) t1 in
    let t3 := PTree.set data_sect_id Ptrofs.zero t2 in
    OK t3
  else
    Error (MSG "Sections are too large to fit into the memory" :: nil).

(** Translation of a program *)
Definition transl_prog_with_map (p:Asm.program) : res program := 
  do (data_sz, data_defs) <- transl_globvars 0 (AST.prog_defs p);
  do (h, code) <- transl_funs 0 (AST.prog_defs p);
  let (code_sz, fun_defs) := h in
  do (extfuns_sz, ext_fun_defs) <- transl_ext_funs 0 (AST.prog_defs p);
  do smap <- gen_smap data_sz code_sz;
  OK (Build_program
        (data_defs ++ fun_defs ++ ext_fun_defs)
        (AST.prog_public p)
        (AST.prog_main p)
        smap
        (Build_section stack_sect_id (Ptrofs.repr Mem.stack_limit))
        (Build_section data_sect_id (Ptrofs.repr data_sz))
        (Build_section code_sect_id (Ptrofs.repr code_sz), code)
        (Build_section extfuns_sect_id (Ptrofs.repr extfuns_sz)))
      .

End WITHMEMORYMODELOPS.


End WITH_ENCODE_FUN.

End WITH_LABEL_MAP.

End WITH_GID_MAP.


(** * Compute mappings from global identifiers to section labels *)

(** Information accumulated during the translation of global data *)
Record dinfo : Type :=
mkDinfo{
  di_size : Z;           (**r The size of the data section traversed so far *)
  di_map : GID_MAP_TYPE
                          (**r The mapping from global identifiers to section labels *)
}.


(** Update the gid mapping for a single variable *)
Definition update_gvar_map {V:Type} (di: dinfo)
           (id:ident) (gvar: AST.globvar V) : dinfo :=
  let sz:= AST.init_data_list_size (AST.gvar_init gvar) in
  mkDinfo (di_size di + sz) (update_gid_map id (data_label (di_size di)) (di_map di)).


(** Update the gid mapping for all global variables *)
Fixpoint update_gvars_map (di:dinfo) (gdefs : list (ident * option (AST.globdef Asm.fundef unit)))
                         : dinfo :=
  match gdefs with
  | nil => di
  | ((id, None) :: gdefs') =>
    update_gvars_map di gdefs'
  | ((_, Some (AST.Gfun _)) :: gdefs') =>
    update_gvars_map di gdefs'
  | ((id, Some (AST.Gvar v)) :: gdefs') =>
    let di' := update_gvar_map di id v in
    update_gvars_map di' gdefs'
  end.


(** Update the gid mapping for a single instruction *)
Record cinfo : Type :=
mkCinfo{
  ci_size : Z;           (**r The size of the code section traversed so far *)
  ci_map : GID_MAP_TYPE;  (**r The mapping from global identifiers to section labels *)
  ci_lmap : LABEL_MAP_TYPE; (**r The mapping for labels in functions *)
}.


Section WITH_ENCODE_FUN.

(** Given a FlatAsm instruciton, encode returns the size of its machine encoding *)
Variable encode : FlatAsm.instruction -> res Z.

Definition transl_instr_dummy := transl_instr default_gid_map default_label_map 1%positive.

Definition compute_instr_size (instr:Asm.instruction) : res Z :=
  do instrs <- transl_instr_dummy instr;
  do (sz, code) <- encode_instrs encode instrs 0;
  OK sz.

(** Update the gid mapping for a single instruction *)
Definition update_instr_map (fid:ident) (ci:cinfo) (instr:Asm.instruction) : res cinfo :=
  match instr with
  | Plabel l =>
    let ofs := ci_size ci in
    OK (mkCinfo ofs (ci_map ci) 
                (update_label_map fid l ofs (ci_lmap ci)))
  | i =>
    do sz <- compute_instr_size i;
    OK (mkCinfo (ci_size ci + sz) (ci_map ci) (ci_lmap ci))
  end.

    
(** Update the gid mapping for a list of instructions *)
Fixpoint update_instrs_map (fid:ident) (ci:cinfo) (instrs: list Asm.instruction) : res cinfo :=
  match instrs with
  | nil => OK ci
  | i::instrs' =>
    do ci' <- update_instr_map fid ci i;
    update_instrs_map fid ci' instrs'
  end.

(** Update the gid mapping for all functions *)
Fixpoint update_funs_map (ci:cinfo) (gdefs : list (ident * option (AST.globdef Asm.fundef unit)))
                         : res cinfo :=
  match gdefs with
  | nil => OK ci
  | ((id, None) :: gdefs') =>
    update_funs_map ci gdefs'
  | ((id, Some (AST.Gfun f)) :: gdefs') =>
    match f with
    | External _ => update_funs_map ci gdefs'
    | Internal f =>
      let ci' := mkCinfo (ci_size ci)
                         (update_gid_map id (code_label (ci_size ci)) (ci_map ci))
                         (ci_lmap ci)
      in
      do ci'' <- update_instrs_map id ci' (Asm.fn_code f);
      update_funs_map ci'' gdefs'
    end
  | ((id, Some (AST.Gvar v)) :: gdefs') =>
    update_funs_map ci gdefs'
  end.

(** Update the gid and label mappings by traversing an Asm program *)
Definition update_map (p:Asm.program) : res (GID_MAP_TYPE * LABEL_MAP_TYPE) :=
  let init_di := (mkDinfo 0 default_gid_map) in
  let map := di_map (update_gvars_map init_di (AST.prog_defs p)) in
  let init_ci := mkCinfo 0 map default_label_map in
  do final_ci <- update_funs_map init_ci (AST.prog_defs p);
  OK (ci_map final_ci, ci_lmap final_ci).


Section WITHMEMORYMODELOPS.
Context `{memory_model_ops: Mem.MemoryModelOps}.

(** The full translation *)
Definition transf_program (p:Asm.program) : res program :=
  do (gmap,lmap) <- update_map p;
  transl_prog_with_map gmap lmap encode p.

End WITHMEMORYMODELOPS.

End WITH_ENCODE_FUN.