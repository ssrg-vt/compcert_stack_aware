Require Import String Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

(* Documentation:
    - https://www.kernel.org/doc/html//v6.4-rc3/bpf/instruction-set.html 
    - https://man7.org/linux/man-pages/man8/bpfc.8.html *)

(* Registers *)
(* eBPF has 10 general purpose registers and R10 reserved for 
   read-only frame pointer register: size 64 bits*)
Inductive breg : Type := 
    | R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10.

Lemma breg_eq: forall (x y: breg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(* Conventional name for read-only frame pointer register *)
Notation FP := R10.

(* Test conditions for Jump instructions *)
Inductive jumpcond : Type :=
    | jeq | jneq | jle | jlt | jge | jgt | jsle | jslt | jsge | jsgt | jset.

Definition label := positive.

(* Instruction encoding *)
(* BPF has two instruction encodings:
   - the basic instruction encoding, which used 64 bits to encode an instruction
   - the wide instruction encoding, which appends a seconf 64 bits after the basic instruction for a total of 128 bits. *)
(* Types:
   - there can be signed or unsigned with width 8, 16, 32, 64 and 128 bits
   - u32: 32 bit unsigned number 
   - Naming conventions for types:
        - [b]: 8 bits
        - [w]: 16 bits (word)
        - [l]: 32 bits (longword)
        - [q]: 64 bits (quadword) *)

Inductive instruction : Type :=
    (* Arithmetic instructions *)
    | Badd_rr (rd : breg) (rs : breg)     (* rd += rs, where both are registers *)
    | Baddl_ri (rd : breg) (imm : int)    (* rd += imm, where source is 32 bit immediate value *)
    | Baddq_ri (rd : breg) (imm : int64)  (* rd += imm, where source is 64 bit immediate value *)
    | Bsub_rr (rd : breg) (rs : breg)     (* rd -= rs, where both are registers *)
    | Bsubl_ri (rd : breg) (imm : int)    (* rd -= imm, where source is 32 bit immediate value *) 
    | Bsubq_ri (rd : breg) (imm : int64)  (* rd -= imm, where source is 64 bit immediate value *) 
    | Bmul_rr (rd : breg) (rs : breg)     (* rd *= rs, where both are registers *)
    | Bmull_ri (rd : breg) (imm : int)    (* rd *= imm, where source is 32 bit immediate value *)
    | Bmulq_ri (rd : breg) (imm : int64)  (* rd *= imm, where source is 64 bit immediate value *)
    | Bdiv_rr (rd : breg) (rs : breg)     (* rd /= rs, where both are registers *)
    | Bdivl_ri (rd : breg) (imm : int)    (* rd /= imm, where source is 32 bit immediate value *)
    | Bdivq_ri (rd : breg) (imm : int64)  (* rd /= imm, where source is 64 bit immediate value *)
    | Bmod_rr (rd : breg) (rs : breg)     (* rd /= rs, where both are registers *)
    | Bmodl_ri (rd : breg) (imm : int)    (* rd /= imm, where source is 32 bit immediate value *)
    | Bmodq_ri (rd : breg) (imm : int64)  (* rd /= imm, where source is 32 bit immediate value *)
    (* Logical instructions *)
    | Bor_rr (rd : breg) (rs : breg)      (* rd |= rs, where both are registers *)
    | Borl_ri (rd : breg) (imm : int)     (* rd |= imm, where source is 32 bit immediate value *)
    | Borq_ri (rd : breg) (imm : int64)   (* rd |= imm, where source is 64 immediate value *)
    | Band_rr (rd : breg) (rs : breg)     (* rd &= rs, where both are registers *)
    | Bandl_ri (rd : breg) (imm : int64)  (* rd &= imm, where source is 32 bit immediate value *)
    | Bandq_ri (rd : breg) (imm : int64)  (* rd &= imm, where source is 64 bit immediate value *)
    | Blsh_rr (rd : breg) (rs : breg)     (* rd <<= rs, where both are registers *)    
    | Blshl_ri (rd : breg) (imm : int)    (* rd <<= imm, where source is 32 bit immediate value *)
    | Blshq_ri (rd : breg) (imm : int64)  (* rd <<= imm, where source is 64 bit immediate value *)
    | Brsh_rr (rd : breg) (rs : breg)     (* rd >>= rs, where both are registers *)    
    | Brshl_ri (rd : breg) (imm : int64)  (* rd >>= imm, where source is 32 bit immediate value *)
    | Brshq_ri (rd : breg) (imm : int64)  (* rd >>= imm, where source is 64 bit immediate value *)
    | Bneg_rr (rd : breg) (rs : breg)     (* rd = ~ rs, where both are registers *)
    | Bnegl_ri (rd : breg) (imm : int)    (* rd = ~imm, where source is 32 bit immediate value *)
    | Bnegq_ri (rd : breg) (imm : int64)  (* rd = ~imm, where source is 64 bit immediate value *)
    | Bxor_rr (rd : breg) (rs : breg)     (* rd ^= rs, where both are registers *)
    | Bxorl_ri (rd : breg) (imm : int64)  (* rd ^= imm, where source is 32 bit immediate value *)
    | Bxorq_ri (rd : breg) (imm : int64)  (* rd ^= imm, where source is 64 bit immediate value *)
    | Barsh_rr (rd : breg) (rs : breg)    (* signed extending shift right, where both are registers *)
    | Barshl_ri (rd : breg) (imm : int64) (* signed extending shift right, where source is 32 bit immediate value *)
    | Barshq_ri (rd : breg) (imm : int64) (* signed extending shift right, where source is 64 bit immediate value *)
    (* Move instruction *)
    | Bmov_rr (rd : breg) (rs : breg)     (* rd = rs, where both are registers *)
    | Bmovl_ri (rd : breg) (imm : int)    (* rd = imm, where source is 32 bit immediate value *)
    | Bmovq_ri (rd : breg) (imm : int64)  (* rd = imm, where source is 64 bits immediate value *)
    (* Jump instructions *)
    | Bj (imm : int)                      (* PC += offset : it should be max 16?? *)
    | Bjc (cond : jumpcond) (imm : int)   (* PC += offset if cond *)
    | Bhcall (imm : int)                  (* call helper functions by address stored as immediate *)
    | Bcall (imm : int)                   (* call PC += offset : program local functions *)
    (* Return instruction *)
    | Bexit                               (* return : needs to store return value in register R0 *).

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code; fn_stacksize: Z}.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Module BregEq.
  Definition t := breg.
  Definition eq := breg_eq.
End BregEq.

Module BregMap := EMap(BregEq).

Definition bregset := BregMap.t val.
Definition genv := Genv.t fundef unit.




