(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Jan 9, 2018 *)
(* ******************* *)

(** Abstract syntax and semantics for IA32 assembly language with a flat memory space **)

Require Import String Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Smallstep.
Require Import Locations Stacklayout Conventions EraseArgs.
Require Import Sect FlatAsmGlobenv FlatAsmBuiltin FlatAsmGlobdef.
Require Asm RawAsmgen.
Require Globalenvs.


(** * Abstract syntax *)

Definition ireg := Asm.ireg.
Definition freg := Asm.freg.
Definition preg := Asm.preg.
Definition testcond := Asm.testcond.

Definition RAX := Asm.RAX.
Definition RBX := Asm.RBX.
Definition RCX := Asm.RCX.
Definition RDX := Asm.RDX.
Definition RSI := Asm.RSI.
Definition RDI := Asm.RDI.
Definition RBP := Asm.RBP.
Definition RSP := Asm.RSP.


Definition PC := Asm.PC.
Definition ST0 := Asm.ST0.
Definition RA := Asm.RA.
Definition IR := Asm.IR.
Definition FR := Asm.FR.
Definition CR := Asm.CR.
Definition ZF := Asm.ZF.
Definition CF := Asm.CF.
Definition PF := Asm.PF.
Definition SF := Asm.SF.
Definition OF := Asm.OF.

Coercion IR: Asm.ireg >-> Asm.preg.
Coercion FR: Asm.freg >-> Asm.preg.
Coercion CR: Asm.crbit >-> Asm.preg.

Definition undef_regs := Asm.undef_regs.


(** A global location points to an offset in a section *)
Definition gloc:Type := sect_label.
(** A label points to an offset in a section. 
    Labels are different from global locations in that they are local to a function *)
Definition label:Type := sect_label.

(** General form of an addressing mode. *)

Inductive addrmode: Type :=
  | Addrmode (base: option ireg)
             (ofs: option (ireg * Z))
             (const: Z + gloc * ptrofs).


(** Instructions.  IA32 instructions accept many combinations of
  registers, memory references and immediate constants as arguments.
  Here, we list only the combinations that we actually use.

  Naming conventions for types:
- [b]: 8 bits
- [w]: 16 bits ("word")
- [l]: 32 bits ("longword")
- [q]: 64 bits ("quadword")
- [d] or [sd]: FP double precision (64 bits)
- [s] or [ss]: FP single precision (32 bits)

  Naming conventions for operands:
- [r]: integer register operand
- [f]: XMM register operand
- [m]: memory operand
- [i]: immediate integer operand
- [s]: immediate symbol operand
- [l]: immediate label operand
- [cl]: the [CL] register

  For two-operand instructions, the first suffix describes the result
  (and first argument), the second suffix describes the second argument.
*)

Inductive instruction: Type :=
  (** Moves *)
  | Pmov_rr (rd: ireg) (r1: ireg)       (**r [mov] (integer) *)
  | Pmovl_ri (rd: ireg) (n: int)
  | Pmovq_ri (rd: ireg) (n: int64)
  | Pmov_rs (rd: ireg) (loc: gloc)
  | Pmovl_rm (rd: ireg) (a: addrmode)
  | Pmovq_rm (rd: ireg) (a: addrmode)
  | Pmovl_mr (a: addrmode) (rs: ireg)
  | Pmovq_mr (a: addrmode) (rs: ireg)
  | Pmovsd_ff (rd: freg) (r1: freg)     (**r [movsd] (single 64-bit float) *)
  | Pmovsd_fi (rd: freg) (n: float)     (**r (pseudo-instruction) *)
  | Pmovsd_fm (rd: freg) (a: addrmode)
  | Pmovsd_mf (a: addrmode) (r1: freg)
  | Pmovss_fi (rd: freg) (n: float32)   (**r [movss] (single 32-bit float) *)
  | Pmovss_fm (rd: freg) (a: addrmode)
  | Pmovss_mf (a: addrmode) (r1: freg)
  | Pfldl_m (a: addrmode)               (**r [fld] double precision *)
  | Pfstpl_m (a: addrmode)              (**r [fstp] double precision *)
  | Pflds_m (a: addrmode)               (**r [fld] simple precision *)
  | Pfstps_m (a: addrmode)              (**r [fstp] simple precision *)
  | Pxchg_rr (r1: ireg) (r2: ireg)      (**r register-register exchange *)
  (** Moves with conversion *)
  | Pmovb_mr (a: addrmode) (rs: ireg)   (**r [mov] (8-bit int) *)
  | Pmovw_mr (a: addrmode) (rs: ireg)   (**r [mov] (16-bit int) *)
  | Pmovzb_rr (rd: ireg) (rs: ireg)     (**r [movzb] (8-bit zero-extension) *)
  | Pmovzb_rm (rd: ireg) (a: addrmode)
  | Pmovsb_rr (rd: ireg) (rs: ireg)     (**r [movsb] (8-bit sign-extension) *)
  | Pmovsb_rm (rd: ireg) (a: addrmode)
  | Pmovzw_rr (rd: ireg) (rs: ireg)     (**r [movzw] (16-bit zero-extension) *)
  | Pmovzw_rm (rd: ireg) (a: addrmode)
  | Pmovsw_rr (rd: ireg) (rs: ireg)     (**r [movsw] (16-bit sign-extension) *)
  | Pmovsw_rm (rd: ireg) (a: addrmode)
  | Pmovzl_rr (rd: ireg) (rs: ireg)     (**r [movzl] (32-bit zero-extension) *)
  | Pmovsl_rr (rd: ireg) (rs: ireg)     (**r [movsl] (32-bit sign-extension) *)
  | Pmovls_rr (rd: ireg)                (** 64 to 32 bit conversion (pseudo) *)
  | Pcvtsd2ss_ff (rd: freg) (r1: freg)  (**r conversion to single float *)
  | Pcvtss2sd_ff (rd: freg) (r1: freg)  (**r conversion to double float *)
  | Pcvttsd2si_rf (rd: ireg) (r1: freg) (**r double to signed int *)
  | Pcvtsi2sd_fr (rd: freg) (r1: ireg)  (**r signed int to double *)
  | Pcvttss2si_rf (rd: ireg) (r1: freg) (**r single to signed int *)
  | Pcvtsi2ss_fr (rd: freg) (r1: ireg)  (**r signed int to single *)
  | Pcvttsd2sl_rf (rd: ireg) (r1: freg) (**r double to signed long *)
  | Pcvtsl2sd_fr (rd: freg) (r1: ireg)  (**r signed long to double *)
  | Pcvttss2sl_rf (rd: ireg) (r1: freg) (**r single to signed long *)
  | Pcvtsl2ss_fr (rd: freg) (r1: ireg)  (**r signed long to single *)
  (** Integer arithmetic *)
  | Pleal (rd: ireg) (a: addrmode)
  | Pleaq (rd: ireg) (a: addrmode)
  | Pnegl (rd: ireg)
  | Pnegq (rd: ireg)
  | Paddl_ri (rd: ireg) (n: int)
  | Paddq_ri (rd: ireg) (n: int64)
  | Psubl_rr (rd: ireg) (r1: ireg)
  | Psubq_rr (rd: ireg) (r1: ireg)
  | Pimull_rr (rd: ireg) (r1: ireg)
  | Pimulq_rr (rd: ireg) (r1: ireg)
  | Pimull_ri (rd: ireg) (n: int)
  | Pimulq_ri (rd: ireg) (n: int64)
  | Pimull_r (r1: ireg)
  | Pimulq_r (r1: ireg)
  | Pmull_r (r1: ireg)
  | Pmulq_r (r1: ireg)
  | Pcltd
  | Pcqto
  | Pdivl (r1: ireg)
  | Pdivq (r1: ireg)
  | Pidivl (r1: ireg)
  | Pidivq (r1: ireg)
  | Pandl_rr (rd: ireg) (r1: ireg)
  | Pandq_rr (rd: ireg) (r1: ireg)
  | Pandl_ri (rd: ireg) (n: int)
  | Pandq_ri (rd: ireg) (n: int64)
  | Porl_rr (rd: ireg) (r1: ireg)
  | Porq_rr (rd: ireg) (r1: ireg)
  | Porl_ri (rd: ireg) (n: int)
  | Porq_ri (rd: ireg) (n: int64)
  | Pxorl_r (rd: ireg)                  (**r [xor] with self = set to zero *)
  | Pxorq_r (rd: ireg)
  | Pxorl_rr (rd: ireg) (r1: ireg)
  | Pxorq_rr (rd: ireg) (r1: ireg)
  | Pxorl_ri (rd: ireg) (n: int)
  | Pxorq_ri (rd: ireg) (n: int64)
  | Pnotl (rd: ireg)
  | Pnotq (rd: ireg)
  | Psall_rcl (rd: ireg)
  | Psalq_rcl (rd: ireg)
  | Psall_ri (rd: ireg) (n: int)
  | Psalq_ri (rd: ireg) (n: int)
  | Pshrl_rcl (rd: ireg)
  | Pshrq_rcl (rd: ireg)
  | Pshrl_ri (rd: ireg) (n: int)
  | Pshrq_ri (rd: ireg) (n: int)
  | Psarl_rcl (rd: ireg)
  | Psarq_rcl (rd: ireg)
  | Psarl_ri (rd: ireg) (n: int)
  | Psarq_ri (rd: ireg) (n: int)
  | Pshld_ri (rd: ireg) (r1: ireg) (n: int)
  | Prorl_ri (rd: ireg) (n: int)
  | Prorq_ri (rd: ireg) (n: int)
  | Pcmpl_rr (r1 r2: ireg)
  | Pcmpq_rr (r1 r2: ireg)
  | Pcmpl_ri (r1: ireg) (n: int)
  | Pcmpq_ri (r1: ireg) (n: int64)
  | Ptestl_rr (r1 r2: ireg)
  | Ptestq_rr (r1 r2: ireg) 
  | Ptestl_ri (r1: ireg) (n: int)
  | Ptestq_ri (r1: ireg) (n: int64)
  | Pcmov (c: testcond) (rd: ireg) (r1: ireg)
  | Psetcc (c: testcond) (rd: ireg)
  (** Floating-point arithmetic *)
  | Paddd_ff (rd: freg) (r1: freg)
  | Psubd_ff (rd: freg) (r1: freg)
  | Pmuld_ff (rd: freg) (r1: freg)
  | Pdivd_ff (rd: freg) (r1: freg)
  | Pnegd (rd: freg)
  | Pabsd (rd: freg)
  | Pcomisd_ff (r1 r2: freg)
  | Pxorpd_f (rd: freg)	              (**r [xor] with self = set to zero *)
  | Padds_ff (rd: freg) (r1: freg)
  | Psubs_ff (rd: freg) (r1: freg)
  | Pmuls_ff (rd: freg) (r1: freg)
  | Pdivs_ff (rd: freg) (r1: freg)
  | Pnegs (rd: freg)
  | Pabss (rd: freg)
  | Pcomiss_ff (r1 r2: freg)
  | Pxorps_f (rd: freg)	              (**r [xor] with self = set to zero *)
  (** Branches and calls *)
  | Pjmp_l (l: label)
  | Pjmp_s (loc: gloc) (sg: signature)
  | Pjmp_r (r: ireg) (sg: signature)
  | Pjcc (c: testcond)(l: label)
  | Pjcc2 (c1 c2: testcond)(l: label)   (**r pseudo *)
  | Pjmptbl (r: ireg) (tbl: list label) (**r pseudo *)
  | Pcall_s (loc: gloc) (sg: signature)
  | Pcall_r (r: ireg) (sg: signature)
  | Pret
  (** Saving and restoring registers *)
  | Pmov_rm_a (rd: ireg) (a: addrmode)  (**r like [Pmov_rm], using [Many64] chunk *)
  | Pmov_mr_a (a: addrmode) (rs: ireg)  (**r like [Pmov_mr], using [Many64] chunk *)
  | Pmovsd_fm_a (rd: freg) (a: addrmode) (**r like [Pmovsd_fm], using [Many64] chunk *)
  | Pmovsd_mf_a (a: addrmode) (r1: freg) (**r like [Pmovsd_mf], using [Many64] chunk *)
  (** Pseudo-instructions *)
  | Plabel(l: label)
  | Pallocframe(frame: frame_info)(ofs_ra ofs_link: ptrofs)
  | Pfreeframe (sz: Z) (ofs_ra ofs_link: ptrofs)
  | Pbuiltin(ef: external_function)(args: list (builtin_arg preg))(res: builtin_res preg)
  (** Instructions not generated by [Asmgen] -- TO CHECK *)
  | Padcl_ri (rd: ireg) (n: int)
  | Padcl_rr (rd: ireg) (r2: ireg)
  | Paddl_mi (a: addrmode) (n: int)
  | Paddl_rr (rd: ireg) (r2: ireg)
  | Pbsfl (rd: ireg) (r1: ireg)
  | Pbsfq (rd: ireg) (r1: ireg)
  | Pbsrl (rd: ireg) (r1: ireg)
  | Pbsrq (rd: ireg) (r1: ireg)
  | Pbswap64 (rd: ireg)
  | Pbswap32 (rd: ireg)
  | Pbswap16 (rd: ireg)
  | Pcfi_adjust (n: int)
  | Pfmadd132 (rd: freg) (r2: freg) (r3: freg)
  | Pfmadd213 (rd: freg) (r2: freg) (r3: freg)
  | Pfmadd231 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub132 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub213 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub231 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd132 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd213 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd231 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub132 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub213 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub231 (rd: freg) (r2: freg) (r3: freg)
  | Pmaxsd (rd: freg) (r2: freg)
  | Pminsd (rd: freg) (r2: freg)
  | Pmovb_rm (rd: ireg) (a: addrmode)
  | Pmovsq_mr  (a: addrmode) (rs: freg)
  | Pmovsq_rm (rd: freg) (a: addrmode)
  | Pmovsb
  | Pmovsw
  | Pmovw_rm (rd: ireg) (ad: addrmode)
  | Prep_movsl
  | Psbbl_rr (rd: ireg) (r2: ireg)
  | Psqrtsd (rd: freg) (r1: freg)
  | Psubl_ri (rd: ireg) (n: int)
  | Psubq_ri (rd: ireg) (n: int64).

Definition instr_with_info:Type := instruction * sect_block.
Definition code := list instr_with_info.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code; fn_frame: frame_info; fn_range:sect_block}.
Definition fundef := AST.fundef function.
Definition gdef := (FlatAsmGlobdef.globdef fundef unit).


(* The FlatAsm program *)
Record program : Type := {
  prog_defs: list (ident * option gdef * sect_block);
  prog_public: list ident;
  prog_main: ident;
  sects_map : section_map;
  stack_sect: section; (* The stack section *)
  data_sect: section;  (* The data section *)
  code_sect : section * code; (* The code section *)
  extfuns_sect : section; (* The section for external functions *)
}.


(** * Operational semantics *)

Definition regset := Asm.regset.
Definition genv := Genv.t fundef instr_with_info.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Asm.Pregmap.set b c a) (at level 1, b at next level) : asm.


Open Scope asm.

Section WITHEXTERNALCALLS.
Context `{external_calls_prf: ExternalCalls}.

Section RELSEM.


Section WITHGE.

Context {F I: Type}.
Variable ge: Genv.t F I.
  
(** Evaluating an addressing mode *)

Definition eval_addrmode32 (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ofs const) := a in
  Val.add  (match base with
             | None => Vint Int.zero
             | Some r => rs r
            end)
  (Val.add (match ofs with
             | None => Vint Int.zero
             | Some(r, sc) =>
                if zeq sc 1
                then rs r
                else Val.mul (rs r) (Vint (Int.repr sc))
             end)
           (match const with
            | inl ofs => Vint (Int.repr ofs)
            | inr(gloc, ofs) => Genv.get_label_addr ge gloc ofs
            end)).

Definition eval_addrmode64 (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ofs const) := a in
  Val.addl (match base with
             | None => Vlong Int64.zero
             | Some r => rs r
            end)
  (Val.addl (match ofs with
             | None => Vlong Int64.zero
             | Some(r, sc) =>
                if zeq sc 1
                then rs r
                else Val.mull (rs r) (Vlong (Int64.repr sc))
             end)
           (match const with
            | inl ofs => Vlong (Int64.repr ofs)
            | inr(gloc, ofs) => Genv.get_label_addr ge gloc ofs
            end)).

Definition eval_addrmode (a: addrmode) (rs: regset) : val :=
  if Archi.ptr64 then eval_addrmode64 a rs else eval_addrmode32 a rs.

End WITHGE.


(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Definition outcome := Asm.outcome.
Definition Stuck := Asm.Stuck.
Definition Next := Asm.Next.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]).
  [nextinstr_nf] is a variant of [nextinstr] that sets condition flags
  to [Vundef] in addition to incrementing the [PC]. *)

Definition nextinstr (rs: regset) (isz:ptrofs) :=
  rs#PC <- (Val.offset_ptr rs#PC isz).

Definition nextinstr_nf (rs: regset) (isz:ptrofs) : regset :=
  nextinstr (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs) isz.

Definition goto_label {F I} (ge: Genv.t F I) (lbl: label) (rs: regset) (m: mem) :=
  Next (rs#PC <- (Genv.get_label_addr0 ge lbl)) m.

(** [CompCertiKOS:test-compcert-param-mem-accessors] For CertiKOS, we
need to parameterize over [exec_load] and [exec_store], which will be
defined differently depending on whether we are in kernel or user
mode. *)

Class MemAccessors
      `{!Mem.MemoryModelOps mem}
      (exec_load: forall F I: Type, Genv.t F I -> memory_chunk -> mem -> addrmode -> regset -> preg -> ptrofs -> outcome)
      (exec_store: forall F I: Type, Genv.t F I -> memory_chunk -> mem -> addrmode -> regset -> preg -> list preg -> ptrofs -> outcome)
: Prop := {}.

Section MEM_ACCESSORS_DEFAULT.

(** [CompCertiKOS:test-compcert-param-mem-accessors] Compcert does not
care about kernel vs. user mode, and uses its memory model to define
its memory accessors. *)

Definition exec_load {F I} (ge: Genv.t F I) (chunk: memory_chunk) (m: mem)
                     (a: addrmode) (rs: regset) (rd: preg) (sz:ptrofs):=
  match Mem.loadv chunk m (eval_addrmode ge a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v) sz) m
  | None => Stuck
  end.

Definition exec_store {F I} (ge: Genv.t F I) (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg) (sz:ptrofs) :=
  match Mem.storev chunk m (eval_addrmode ge a rs) (rs r1) with
  | Some m' =>
    Next (nextinstr_nf (undef_regs destroyed rs) sz) m'
  | None => Stuck
  end.

Local Instance mem_accessors_default: MemAccessors (@exec_load) (@exec_store).

End MEM_ACCESSORS_DEFAULT.


(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual IA32 instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the IA32 reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the IA32 code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction.

    Concerning condition flags, the comparison instructions set them
    accurately; other instructions (moves, [lea]) preserve them;
    and all other instruction set those flags to [Vundef], to reflect
    the fact that the processor updates some or all of those flags,
    but we do not need to model this precisely.
*)

Definition eval_testcond := Asm.eval_testcond.
Definition compare_ints := Asm.compare_ints.
Definition compare_longs := Asm.compare_longs.
Definition compare_floats := Asm.compare_floats.
Definition compare_floats32 := Asm.compare_floats32.

(* Definition alloc_stack_frame (sp: val) fi := *)
(*   let sz := (align (Z.max 0 (frame_size fi)) 8) in *)
(*   Val.offset_ptr sp (Ptrofs.repr (- sz)). *)

Definition current_offset (ge:genv) (v: val) :=
  match v with
    Vptr stk ofs => Ptrofs.unsigned ofs
  | _ => Mem.stack_limit
  end.

Definition exec_instr {exec_load exec_store} `{!MemAccessors exec_load exec_store} (ge: genv) (ii: instr_with_info) (rs: regset) (m: mem) : outcome :=
  let (i,blk) := ii in
  let sz := sect_block_size blk in
  match i with
  (** Moves *)
  | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) sz) m
  | Pmovl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vint n)) sz) m
  | Pmovq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vlong n)) sz) m
  | Pmov_rs rd gloc =>
      Next (nextinstr_nf (rs#rd <- (Genv.get_label_addr0 ge gloc)) sz) m
  | Pmovl_rm rd a =>
      exec_load _ _ ge Mint32 m a rs rd sz
  | Pmovq_rm rd a =>
      exec_load _ _ ge Mint64 m a rs rd sz
  | Pmovl_mr a r1 =>
      exec_store _ _ ge Mint32 m a rs r1 nil sz
  | Pmovq_mr a r1 =>
      exec_store _ _ ge Mint64 m a rs r1 nil sz
  | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) sz) m
  | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n)) sz) m
  | Pmovsd_fm rd a =>
      exec_load _ _ ge Mfloat64 m a rs rd  sz
  | Pmovsd_mf a r1 =>
      exec_store _ _ ge Mfloat64 m a rs r1 nil sz
  | Pmovss_fi rd n =>
      Next (nextinstr (rs#rd <- (Vsingle n)) sz) m
  | Pmovss_fm rd a =>
      exec_load _ _ ge Mfloat32 m a rs rd sz
  | Pmovss_mf a r1 =>
      exec_store _ _ ge Mfloat32 m a rs r1 nil sz
  | Pfldl_m a =>
      exec_load _ _ ge Mfloat64 m a rs ST0 sz
  | Pfstpl_m a =>
      exec_store _ _ ge Mfloat64 m a rs ST0 (ST0 :: nil) sz
  | Pflds_m a =>
      exec_load _ _ ge Mfloat32 m a rs ST0 sz
  | Pfstps_m a =>
      exec_store _ _ ge Mfloat32 m a rs ST0 (ST0 :: nil) sz
  | Pxchg_rr r1 r2 =>
      Next (nextinstr (rs#r1 <- (rs r2) #r2 <- (rs r1)) sz) m
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store _ _ ge Mint8unsigned m a rs r1 nil sz
  | Pmovw_mr a r1 =>
      exec_store _ _ ge Mint16unsigned m a rs r1 nil sz
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1)) sz) m
  | Pmovzb_rm rd a =>
      exec_load _ _ ge Mint8unsigned m a rs rd sz
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1)) sz) m
  | Pmovsb_rm rd a =>
      exec_load _ _ ge Mint8signed m a rs rd sz
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1)) sz) m
  | Pmovzw_rm rd a =>
      exec_load _ _ ge Mint16unsigned m a rs rd sz
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1)) sz) m
  | Pmovsw_rm rd a =>
      exec_load _ _ ge Mint16signed m a rs rd sz
  | Pmovzl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1)) sz) m
  | Pmovsl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1)) sz) m
  | Pmovls_rr rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd)) sz) m
  | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1)) sz) m
  | Pcvtss2sd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1)) sz) m
  | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1))) sz) m
  | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1))) sz) m
  | Pcvttss2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r1))) sz) m
  | Pcvtsi2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r1))) sz) m
  | Pcvttsd2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longoffloat rs#r1))) sz) m
  | Pcvtsl2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflong rs#r1))) sz) m
  | Pcvttss2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longofsingle rs#r1))) sz) m
  | Pcvtsl2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleoflong rs#r1))) sz) m
  (** Integer arithmetic *)
  | Pleal rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode32 ge a rs)) sz) m
  | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 ge a rs)) sz) m
  | Pnegl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd)) sz) m
  | Pnegq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.negl rs#rd)) sz) m
  | Paddl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.add rs#rd (Vint n))) sz) m
  | Psubl_ri rd n =>
    Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd (Vint n))) sz) m
  | Paddq_ri rd n =>
    Next (nextinstr_nf (rs#rd <- (Val.addl rs#rd (Vlong n))) sz) m
  | Psubq_ri rd n =>
    Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd (Vlong n))) sz) m
  | Psubl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1)) sz) m
  | Psubq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd rs#r1)) sz) m
  | Pimull_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1)) sz) m
  | Pimulq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd rs#r1)) sz) m
  | Pimull_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n))) sz) m
  | Pimulq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd (Vlong n))) sz) m
  | Pimull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhs rs#RAX rs#r1)) sz) m
  | Pimulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhs rs#RAX rs#r1)) sz) m
  | Pmull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhu rs#RAX rs#r1)) sz) m
  | Pmulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhu rs#RAX rs#r1)) sz) m
  | Pcltd =>
      Next (nextinstr_nf (rs#RDX <- (Val.shr rs#RAX (Vint (Int.repr 31)))) sz) m
  | Pcqto =>
      Next (nextinstr_nf (rs#RDX <- (Val.shrl rs#RAX (Vint (Int.repr 63)))) sz) m
  | Pdivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pdivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pandl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1)) sz) m
  | Pandq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd rs#r1)) sz) m
  | Pandl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n))) sz) m
  | Pandq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd (Vlong n))) sz) m
  | Porl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1)) sz) m
  | Porq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd rs#r1)) sz) m
  | Porl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n))) sz) m
  | Porq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd (Vlong n))) sz) m
  | Pxorl_r rd =>
      Next (nextinstr_nf (rs#rd <- Vzero) sz) m
  | Pxorq_r rd =>
      Next (nextinstr_nf (rs#rd <- (Vlong Int64.zero)) sz) m
  | Pxorl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1)) sz) m
  | Pxorq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd rs#r1)) sz) m 
  | Pxorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n))) sz) m
  | Pxorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd (Vlong n))) sz) m
  | Pnotl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notint rs#rd)) sz) m
  | Pnotq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notl rs#rd)) sz) m
  | Psall_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#RCX)) sz) m
  | Psalq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd rs#RCX)) sz) m
  | Psall_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n))) sz) m
  | Psalq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd (Vint n))) sz) m
  | Pshrl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#RCX)) sz) m
  | Pshrq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd rs#RCX)) sz) m
  | Pshrl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n))) sz) m
  | Pshrq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd (Vint n))) sz) m
  | Psarl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#RCX)) sz) m
  | Psarq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd rs#RCX)) sz) m
  | Psarl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n))) sz) m
  | Psarq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd (Vint n))) sz) m
  | Pshld_ri rd r1 n =>
      Next (nextinstr_nf
              (rs#rd <- (Val.or (Val.shl rs#rd (Vint n))
                                (Val.shru rs#r1 (Vint (Int.sub Int.iwordsize n))))) sz) m
  | Prorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n))) sz) m
  | Prorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.rorl rs#rd (Vint n))) sz) m
  | Pcmpl_rr r1 r2 =>
      Next (nextinstr (compare_ints (rs r1) (rs r2) rs m) sz) m
  | Pcmpq_rr r1 r2 =>
      Next (nextinstr (compare_longs (rs r1) (rs r2) rs m) sz) m
  | Pcmpl_ri r1 n =>
      Next (nextinstr (compare_ints (rs r1) (Vint n) rs m) sz) m
  | Pcmpq_ri r1 n =>
      Next (nextinstr (compare_longs (rs r1) (Vlong n) rs m) sz) m
  | Ptestl_rr r1 r2 =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs m) sz) m
  | Ptestq_rr r1 r2 =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (rs r2)) (Vlong Int64.zero) rs m) sz) m
  | Ptestl_ri r1 n =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs m) sz) m
  | Ptestq_ri r1 n =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (Vlong n)) (Vlong Int64.zero) rs m) sz) m
  | Pcmov c rd r1 =>
      match eval_testcond c rs with
      | Some true => Next (nextinstr (rs#rd <- (rs#r1)) sz) m
      | Some false => Next (nextinstr rs sz) m
      | None => Next (nextinstr (rs#rd <- Vundef) sz) m
      end
  | Psetcc c rd =>
      Next (nextinstr (rs#rd <- (Val.of_optbool (eval_testcond c rs))) sz) m
  (** Arithmetic operations over double-precision floats *)
  | Paddd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1)) sz) m
  | Psubd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1)) sz) m
  | Pmuld_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1)) sz) m
  | Pdivd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1)) sz) m
  | Pnegd rd =>
      Next (nextinstr (rs#rd <- (Val.negf rs#rd)) sz) m
  | Pabsd rd =>
      Next (nextinstr (rs#rd <- (Val.absf rs#rd)) sz) m
  | Pcomisd_ff r1 r2 =>
      Next (nextinstr (compare_floats (rs r1) (rs r2) rs) sz) m
  | Pxorpd_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vfloat Float.zero)) sz) m
  (** Arithmetic operations over single-precision floats *)
  | Padds_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#rd rs#r1)) sz) m
  | Psubs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#rd rs#r1)) sz) m
  | Pmuls_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#rd rs#r1)) sz) m
  | Pdivs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#rd rs#r1)) sz) m
  | Pnegs rd =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#rd)) sz) m
  | Pabss rd =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#rd)) sz) m
  | Pcomiss_ff r1 r2 =>
      Next (nextinstr (compare_floats32 (rs r1) (rs r2) rs) sz) m
  | Pxorps_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vsingle Float32.zero)) sz) m
  (** Branches and calls *)
  | Pjmp_l lbl =>
      goto_label ge lbl rs m
  | Pjmp_s gloc sg =>
      Next (rs#PC <- (Genv.get_label_addr0 ge gloc)) m
  | Pjmp_r r sg =>
      Next (rs#PC <- (rs r)) m
  | Pjcc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label ge lbl rs m
      | Some false => Next (nextinstr rs sz) m
      | None => Stuck
      end
  | Pjcc2 cond1 cond2 lbl =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_label ge lbl rs m
      | Some _, Some _ => Next (nextinstr rs sz) m
      | _, _ => Stuck
      end
  | Pjmptbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label ge lbl (rs #RAX <- Vundef #RDX <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcall_s gloc sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC sz) #PC <- (Genv.get_label_addr0 ge gloc)) m
  | Pcall_r r sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC sz) #PC <- (rs r)) m
  | Pret =>
  (** [CompCertX:test-compcert-ra-vundef] We need to erase the value of RA,
      which is actually popped away from the stack in reality. *)
      Next (rs#PC <- (rs#RA) #RA <- Vundef) m
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
      exec_load _ _ ge (if Archi.ptr64 then Many64 else Many32) m a rs rd sz
  | Pmov_mr_a a r1 =>
      exec_store _ _ ge (if Archi.ptr64 then Many64 else Many32) m a rs r1 nil sz
  | Pmovsd_fm_a rd a =>
      exec_load _ _ ge Many64 m a rs rd sz
  | Pmovsd_mf_a a r1 =>
      exec_store _ _ ge Many64 m a rs r1 nil sz
  (** Pseudo-instructions *)
  | Plabel lbl =>
      Next (nextinstr rs sz) m
  | Pallocframe fi ofs_ra ofs_link =>
    let curofs := current_offset ge (rs RSP) in
    let sp := flatptr (Ptrofs.repr (RawAsmgen.offset_after_alloc curofs fi)) in
    (* let sp := alloc_stack_frame (rs RSP) fi in *)
    match Mem.storev Mptr m (Val.offset_ptr sp ofs_link) rs#RSP with
    | None => Stuck
    | Some m2 =>
      match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_ra) rs#RA with
      | None => Stuck
      | Some m3 =>
        Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp) sz) m3
      end
    end
  | Pfreeframe sz' ofs_ra ofs_link =>
    match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
    | None => Stuck
    | Some ra =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_link) with
      | None => Stuck
      | Some sp =>
        Next (nextinstr (rs#RSP <- sp #RA <- ra) sz) m
      end
    end
  | Pcfi_adjust n => Next rs m
  
  | Pbuiltin ef args res =>
      Stuck                             (**r treated specially below *)
  (** The following instructions and directives are not generated
      directly by [Asmgen], so we do not model them. *)
  | Padcl_ri _ _
  | Padcl_rr _ _
  | Paddl_mi _ _
  | Paddl_rr _ _
  | Pbsfl _ _
  | Pbsfq _ _
  | Pbsrl _ _
  | Pbsrq _ _
  | Pbswap64 _
  | Pbswap32 _
  | Pbswap16 _
  | Pfmadd132 _ _ _
  | Pfmadd213 _ _ _
  | Pfmadd231 _ _ _
  | Pfmsub132 _ _ _
  | Pfmsub213 _ _ _
  | Pfmsub231 _ _ _
  | Pfnmadd132 _ _ _
  | Pfnmadd213 _ _ _
  | Pfnmadd231 _ _ _
  | Pfnmsub132 _ _ _
  | Pfnmsub213 _ _ _
  | Pfnmsub231 _ _ _
  | Pmaxsd _ _
  | Pminsd _ _
  | Pmovb_rm _ _
  | Pmovsq_rm _ _
  | Pmovsq_mr _ _
  | Pmovsb
  | Pmovsw
  | Pmovw_rm _ _
  | Prep_movsl
  | Psbbl_rr _ _
  | Psqrtsd _ _
    => Stuck
  end.

(** Symbol environments are not used to describe the semantics of FlatAsm. However, we need to provide a dummy one to match the semantics framework of CompCert *)
Definition dummy_senv := Globalenvs.Genv.to_senv (Globalenvs.Genv.empty_genv unit unit nil).

Definition state := Asm.state.
Definition State := Asm.State.
Definition set_res := Asm.set_res.
Definition preg_of := Asm.preg_of.
Definition set_pair := Asm.set_pair.
Definition loc_external_result := Asm.loc_external_result.
Definition extcall_arguments := Asm.extcall_arguments.

Inductive step {exec_load exec_store} `{!MemAccessors exec_load exec_store} 
  (ge: genv) : state -> trace -> state -> Prop :=
| exec_step_internal:
    forall ofs i rs m rs' m',
      rs PC = Vptr mem_block ofs ->
      Genv.genv_is_instr_internal ge ofs = true ->
      Genv.find_instr ge ofs = Some i ->
      exec_instr ge i rs m = Next rs' m' ->
      step ge (State rs m) E0 (State rs' m')
| exec_step_builtin:
    forall ofs ef args res rs m vargs t vres rs' m' blk,
      rs PC = Vptr mem_block ofs ->
      Genv.genv_is_instr_internal ge ofs = true ->
      Genv.find_instr ge ofs = Some (Pbuiltin ef args res, blk) ->
      eval_builtin_args _ _ preg ge rs (rs RSP) m args vargs ->
        external_call ef dummy_senv vargs m t vres m' ->
      forall BUILTIN_ENABLED: builtin_enabled ef,
        rs' = nextinstr_nf
                (set_res res vres
                         (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) (sect_block_size blk) ->
        step ge (State rs m) t (State rs' m')
| exec_step_external:
    forall ofs ef args res rs m t rs' m',
      rs PC = Vptr mem_block ofs ->
      Genv.genv_is_instr_internal ge ofs = false ->
      Genv.find_funct_offset ge ofs = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      forall (* CompCertX: BEGIN additional conditions for calling convention *)
        (* (STACK: *)
        (*    exists m_, *)
        (*      free_extcall_args (rs RSP) m (regs_of_rpairs (Conventions1.loc_arguments (ef_sig ef))) = Some m_ /\ *)
        (*      exists t_ res'_ m'_, *)
        (*        external_call ef ge args m_ t_ res'_ m'_ *)
        (* ) *)
        (SP_TYPE: Val.has_type (rs RSP) Tptr)
        (RA_TYPE: Val.has_type (rs RA) Tptr)
        (SP_NOT_VUNDEF: rs RSP <> Vundef)
        (RA_NOT_VUNDEF: rs RA <> Vundef)
      ,      (* CompCertX: END additional conditions for calling convention *)
        external_call ef dummy_senv args m t res m' ->
        rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) (undef_regs (map preg_of destroyed_at_call) rs))) #PC <- (rs RA) #RA <- Vundef ->
        step ge (State rs m) t (State rs' m').

End RELSEM.

(** Initialization of the global environment *)
Definition add_global (ge:genv) (idg: ident * option gdef * sect_block) : genv :=
  let '(gid,gdef,sb) := idg in
  match (Genv.get_block_offset0 ge sb) with
  | None => ge
  | Some ofs =>
    match gdef with
    | None => ge
    | Some (Gvar _) => ge
    | Some (Gfun f) =>
      (Genv.mkgenv
         (ZTree.set (Ptrofs.unsigned ofs) f (Genv.genv_defs ge))
         (Genv.genv_smap ge)
         (Genv.genv_instrs_map ge)
         (Genv.genv_is_instr_internal ge)
         (Genv.genv_stack_start ge))
    end
  end.

Fixpoint add_globals (ge:genv) (gl: list (ident * option gdef * sect_block)) : genv :=
  match gl with
  | nil => ge
  | (idg::gl') => 
    let ge' := add_global ge idg in
    add_globals ge' gl'
  end.  

(* Get the offset of an instruction in the flat memory space *)
Definition get_instr_ofs (smap: section_map) (i:instr_with_info): option ptrofs :=
  let (_,bi) := i in get_sect_block_offset0 smap bi.

Definition acc_instr_map (smap:section_map) (i:instr_with_info) map : ZTree.t instr_with_info :=
  match (get_instr_ofs smap i) with
  | None => ZTree.empty _
  | Some ofs => ZTree.set (Ptrofs.unsigned ofs) i map
  end.

Fixpoint acc_instrs_map (smap:section_map) (c:code) map : ZTree.t instr_with_info :=
  match c with 
  | nil => map 
  | i'::c' => 
    let map' := acc_instr_map smap i' map in
    acc_instrs_map smap c' map'
  end.

(* Generate a mapping from offsets to instructions *)
Definition gen_instrs_map (p:program) : ZTree.t instr_with_info :=
  acc_instrs_map (sects_map p) (snd (code_sect p)) (ZTree.empty _).  
  
(* Generate a function for checking if pc points to an internal instruction *)
Definition gen_is_instr_internal (p:program) : ptrofs -> bool:=
  match (get_section_range (sects_map p) (fst (code_sect p))) with
  | None => (fun ofs => false)
  | Some (s,e) => 
    fun ofs => andb (Ptrofs.cmpu Cle s ofs) (Ptrofs.cmpu Clt ofs e)
  end.

Definition empty_genv (smap: section_map)
                      (instrs_map: ZTree.t instr_with_info)
                      (is_instr_internal: ptrofs -> bool)
                      (stack_start: Z): genv :=
  Genv.mkgenv (ZTree.empty _) smap instrs_map is_instr_internal stack_start.


Definition globalenv (p: program) : genv :=
  let stack_start := 
      match (get_section_range (sects_map p) (stack_sect p)) with
      | None => -1
      | Some rng => Ptrofs.unsigned (fst rng)
      end
  in
  let imap := gen_instrs_map p in
  let f := gen_is_instr_internal p in
    add_globals (empty_genv (sects_map p) imap f stack_start) p.(prog_defs).

(** Initialization of the memory *)
Definition mem_block_size : Z :=
  if Archi.ptr64 then two_power_nat 64 else two_power_nat 32.

Section WITHGE.

Variable ge:genv.

Definition store_init_data (m: mem) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m mem_block p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m mem_block p (Vint n)
  | Init_int32 n => Mem.store Mint32 m mem_block p (Vint n)
  | Init_int64 n => Mem.store Mint64 m mem_block p (Vlong n)
  | Init_float32 n => Mem.store Mfloat32 m mem_block p (Vsingle n)
  | Init_float64 n => Mem.store Mfloat64 m mem_block p (Vfloat n)
  | Init_addrof gloc ofs =>
      match Genv.get_label_offset0 ge gloc with
      | None => None
      | Some o => Mem.store Mptr m mem_block p (flatptr (Ptrofs.add o ofs))
      end
  | Init_space n => Some m
  end.

Fixpoint store_init_data_list (m: mem) (b: block) (p: Z) (idl: list init_data)
                              {struct idl}: option mem :=
  match idl with
  | nil => Some m
  | id :: idl' =>
      match store_init_data m p id with
      | None => None
      | Some m' => store_init_data_list m' b (p + init_data_size id) idl'
      end
  end.

Definition alloc_global (smap:section_map) (m: mem) (idg: ident * option gdef * sect_block): option mem :=
  let '(id, gdef, sb) := idg in
  let sz := Ptrofs.unsigned (sect_block_size sb) in
  match (get_sect_block_offset0 smap sb) with
  | None => None
  | Some ofs => 
    let ofs := Ptrofs.unsigned ofs in
    match gdef with
    | None =>
      Some m
    | Some (Gfun f) =>
      Mem.drop_perm m mem_block ofs (ofs+sz) Nonempty
    | Some (Gvar v) =>
      let init := gvar_init unit v in
      let isz := init_data_list_size init in
      if zeq isz sz then  
        match Globalenvs.store_zeros m mem_block ofs sz with
        | None => None
        | Some m1 =>
          match store_init_data_list m1 mem_block ofs init with
          | None => None
          | Some m2 => Mem.drop_perm m2 mem_block ofs (ofs+sz) (perm_globvar v)
          end
        end
      else
        None
    end
  end.

Fixpoint alloc_globals (smap:section_map) (m: mem) (gl: list (ident * option gdef * sect_block))
                       {struct gl} : option mem :=
  match gl with
  | nil => Some m
  | g :: gl' =>
      match alloc_global smap m g with
      | None => None
      | Some m' => alloc_globals smap m' gl'
      end
  end.

End WITHGE.

Definition init_mem (p: program) :=
  let ge := globalenv p in
  let im := fst (Mem.alloc Mem.empty 0 mem_block_size) in
  alloc_globals ge p.(sects_map) im p.(prog_defs).

(** Execution of whole programs. *)
Fixpoint get_main_block (main:ident) (l: list (ident * option gdef * sect_block)) : option sect_block :=
  match l with
  | nil => None
  | (id,_,sb)::l' =>
    if peq main id then Some sb 
    else  get_main_block main l'
  end.

Definition get_main_fun_offset (p:program) : option ptrofs :=
  match get_main_block (prog_main p) (prog_defs p) with
  | None => None
  | Some sb => get_sect_block_offset0 (sects_map p) sb
  end.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0 start_ofs,
      init_mem p = Some m0 ->
      get_main_fun_offset p = Some start_ofs ->
      let rs0 :=
        (Asm.Pregmap.init Vundef)
        # PC <- (Vptr mem_block start_ofs)
        # RA <- Vnullptr
        # RSP <- Vnullptr in
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vnullptr ->
      rs#RAX = Vint r ->
      final_state (State rs m) r.

Local Existing Instance mem_accessors_default.

Definition semantics (p: program) :=
  Semantics_gen step (initial_state p) final_state (globalenv p) dummy_senv.

(* (** Determinacy of the [Asm] semantics. *) *)

(* Remark extcall_arguments_determ: *)
(*   forall rs m sg args1 args2, *)
(*   extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2. *)
(* Proof. *)
(*   intros until m. *)
(*   assert (A: forall l v1 v2, *)
(*              extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2). *)
(*   { intros. inv H; inv H0; congruence. } *)
(*   assert (B: forall p v1 v2, *)
(*              extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2). *)
(*   { intros. inv H; inv H0.  *)
(*     eapply A; eauto. *)
(*     f_equal; eapply A; eauto. } *)
(*   assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 -> *)
(*              forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2). *)
(*   { *)
(*     induction 1; intros vl2 EA; inv EA. *)
(*     auto. *)
(*     f_equal; eauto. } *)
(*   intros. eapply C; eauto. *)
(* Qed. *)

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
+ split. constructor. auto.
+ discriminate.
+ discriminate.
+ assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
+ assert (args0 = args) by (eapply Asm.extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros; inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. assert (start_ofs = start_ofs0) by congruence. subst.
  subst. f_equal. congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

End WITHEXTERNALCALLS.

