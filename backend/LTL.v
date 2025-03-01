(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** The LTL intermediate language: abstract syntax and semantics.

  LTL (``Location Transfer Language'') is the target language
  for register allocation and the source language for linearization. *)

Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Locations Conventions.

(** * Abstract syntax *)

(** LTL is close to RTL, but uses machine registers and stack slots
  instead of pseudo-registers.  Also, the nodes of the control-flow
  graph are basic blocks instead of single instructions. *)

Definition node := positive.

Inductive instruction: Type :=
  | Lop (op: operation) (args: list mreg) (res: mreg)
  | Lload (chunk: memory_chunk) (addr: addressing) (args: list mreg) (dst: mreg)
  | Lgetstack (sl: slot) (ofs: Z) (ty: typ) (dst: mreg)
  | Lsetstack (src: mreg) (sl: slot) (ofs: Z) (ty: typ)
  | Lstore (chunk: memory_chunk) (addr: addressing) (args: list mreg) (src: mreg)
  | Lcall (sg: signature) (ros: mreg + ident)
  | Ltailcall (sg: signature) (ros: mreg + ident)
  | Lbuiltin (ef: external_function) (args: list (builtin_arg loc)) (res: builtin_res mreg)
  | Lbranch (s: node)
  | Lcond (cond: condition) (args: list mreg) (s1 s2: node)
  | Ljumptable (arg: mreg) (tbl: list node)
  | Lreturn.

Definition bblock := list instruction.

Definition code: Type := PTree.t bblock.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

(** * Operational semantics *)

Definition genv := Genv.t fundef unit.
Definition locset := Locmap.t.

(** Calling conventions are reflected at the level of location sets
  (environments mapping locations to values) by the following two
  functions.

  [call_regs caller] returns the location set at function entry,
  as a function of the location set [caller] of the calling function.
- Machine registers have the same values as in the caller.
- Incoming stack slots (used for parameter passing) have the same
  values as the corresponding outgoing stack slots (used for argument
  passing) in the caller.
- Local and outgoing stack slots are initialized to undefined values.
*)

Definition call_regs (caller: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r => caller (R r)
    | S Local ofs ty => Vundef
    | S Incoming ofs ty => caller (S Outgoing ofs ty)
    | S Outgoing ofs ty => Vundef
    end.

(** [return_regs caller callee] returns the location set after
  a call instruction, as a function of the location set [caller]
  of the caller before the call instruction and of the location
  set [callee] of the callee at the return instruction.
- Callee-save machine registers have the same values as in the caller
  before the call.
- Caller-save machine registers have the same values as in the callee.
- Stack slots have the same values as in the caller.
*)

Definition return_regs (caller callee: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r => if is_callee_save r then caller (R r) else callee (R r)
    | S sl ofs ty => caller (S sl ofs ty)
    end.

(** LTL execution states. *)

Inductive stackframe : Type :=
  | Stackframe:
      forall (f: function)      (**r calling function *)
             (sp: val)          (**r stack pointer in calling function *)
             (ls: locset)       (**r location state in calling function *)
             (bb: bblock),      (**r continuation in calling function *)
      stackframe.

Inductive state `{memory_model_ops: Mem.MemoryModelOps} : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point *)
             (ls: locset)             (**r location state *)
             (m: mem),                (**r memory state *)
      state
  | Block:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (bb: bblock)             (**r current basic block *)
             (ls: locset)             (**r location state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (ls: locset)             (**r location state of caller *)
             (m: mem) (sz: Z),                (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (ls: locset)             (**r location state of callee *)
             (m: mem),                (**r memory state *)
      state.


Section WITHEXTERNALCALLSOPS.
Context `{external_calls_prf: ExternalCalls}.

Variable fn_stack_requirements: ident -> Z.

Section RELSEM.

(** [parent_locset cs] returns the mapping of values for locations
  of the caller function. *)

Variable init_ls: locset.

Definition parent_locset (stack: list stackframe) : locset :=
  match stack with
  | nil => init_ls
  | Stackframe f sp ls bb :: stack' => ls
  end.

Variable ge: genv.

Definition reglist (rs: locset) (rl: list mreg) : list val :=
  List.map (fun r => rs (R r)) rl.

Fixpoint undef_regs (rl: list mreg) (rs: locset) : locset :=
  match rl with
  | nil => rs
  | r1 :: rl => Locmap.set (R r1) Vundef (undef_regs rl rs)
  end.

Definition destroyed_by_getstack (s: slot): list mreg :=
  match s with
  | Incoming => temp_for_parent_frame :: nil
  | _        => nil
  end.

Definition find_function (ros: mreg + ident) (rs: locset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge (rs (R r))
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

Definition ros_is_function (ros: mreg + ident) (rs: locset) (i: ident) : Prop :=
  match ros with
  | inl r => exists b o, rs (R r) = Vptr b o /\ Genv.find_symbol ge i = Some b
  | inr symb => i = symb
  end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_start_block: forall s f sp pc rs m bb,
      (fn_code f)!pc = Some bb ->
      step (State s f sp pc rs m)
        E0 (Block s f sp bb rs m)
  | exec_Lop: forall s f sp op args res bb rs m v rs',
      eval_operation ge sp op (reglist rs args) m = Some v ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      step (Block s f sp (Lop op args res :: bb) rs m)
        E0 (Block s f sp bb rs' m)
  | exec_Lload: forall s f sp chunk addr args dst bb rs m a v rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      step (Block s f sp (Lload chunk addr args dst :: bb) rs m)
        E0 (Block s f sp bb rs' m)
  | exec_Lgetstack: forall s f sp sl ofs ty dst bb rs m rs',
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
      step (Block s f sp (Lgetstack sl ofs ty dst :: bb) rs m)
        E0 (Block s f sp bb rs' m)
  | exec_Lsetstack: forall s f sp src sl ofs ty bb rs m rs',
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
      step (Block s f sp (Lsetstack src sl ofs ty :: bb) rs m)
        E0 (Block s f sp bb rs' m)
  | exec_Lstore: forall s f sp chunk addr args src bb rs m a rs' m',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (Block s f sp (Lstore chunk addr args src :: bb) rs m)
        E0 (Block s f sp bb rs' m')
  | exec_Lcall: forall s f sp sig ros bb rs m fd id (IFI: ros_is_function ros rs id),
      find_function ros rs = Some fd ->
      funsig fd = sig ->
      step (Block s f sp (Lcall sig ros :: bb) rs m)
        E0 (Callstate (Stackframe f sp rs bb :: s) fd rs (Mem.push_new_stage m) (fn_stack_requirements id))
  | exec_Ltailcall: forall s f sp sig ros bb rs m fd rs' m' m'' id (IFI: ros_is_function ros rs' id),
      rs' = return_regs (parent_locset s) rs ->
      find_function ros rs' = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
      Mem.tailcall_stage m' = Some m'' ->
      step (Block s f (Vptr sp Ptrofs.zero) (Ltailcall sig ros :: bb) rs m)
        E0 (Callstate s fd rs' m'' (fn_stack_requirements id))
  | exec_Lbuiltin: forall s f sp ef args res bb rs m vargs t vres rs' m' m'',
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs (Mem.push_new_stage m) t vres m' ->
      Mem.unrecord_stack_block m' = Some m'' ->
      rs' = Locmap.setres res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      forall BUILTIN_ENABLED : builtin_enabled ef,
        step (Block s f sp (Lbuiltin ef args res :: bb) rs m)
             t (Block s f sp bb rs' m'')
  | exec_Lbranch: forall s f sp pc bb rs m,
      step (Block s f sp (Lbranch pc :: bb) rs m)
        E0 (State s f sp pc rs m)
  | exec_Lcond: forall s f sp cond args pc1 pc2 bb rs b pc rs' m,
      eval_condition cond (reglist rs args) m = Some b ->
      pc = (if b then pc1 else pc2) ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (Block s f sp (Lcond cond args pc1 pc2 :: bb) rs m)
        E0 (State s f sp pc rs' m)
  | exec_Ljumptable: forall s f sp arg tbl bb rs m n pc rs',
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      step (Block s f sp (Ljumptable arg tbl :: bb) rs m)
        E0 (State s f sp pc rs' m)
  | exec_Lreturn: forall s f sp bb rs m m',
      Mem.free m sp 0 f.(fn_stacksize) = Some m' ->
      step (Block s f (Vptr sp Ptrofs.zero) (Lreturn :: bb) rs m)
        E0 (Returnstate s (return_regs (parent_locset s) rs) m')
  | exec_function_internal: forall s f rs m m' m'' sp rs' sz,
      Mem.alloc m 0 f.(fn_stacksize) = (m', sp) ->
      Mem.record_stack_blocks m' (make_singleton_frame_adt sp (fn_stacksize f) sz) = Some m'' ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      step (Callstate s (Internal f) rs m sz)
        E0 (State s f (Vptr sp Ptrofs.zero) f.(fn_entrypoint) rs' m'')
  | exec_function_external: forall s ef t args res rs m rs' m' sz,
      args = map (fun p => Locmap.getpair p rs) (loc_arguments (ef_sig ef)) ->
      external_call ef ge args m t res m' ->
      rs' = Locmap.setpair (loc_result (ef_sig ef)) res (undef_regs destroyed_at_call rs) ->
      step (Callstate s (External ef) rs m sz)
         t (Returnstate s rs' m')
  | exec_return: forall f sp rs1 bb s rs m m',
      Mem.unrecord_stack_block m = Some m' ->
      step (Returnstate (Stackframe f sp rs1 bb :: s) rs m)
        E0 (Block s f sp bb rs m').

End RELSEM.

(** Execution of a whole program boils down to invoking its main
  function.  The result of the program is the return value of the
  main function, to be found in the machine register dictated
  by the calling conventions. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0 m2,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      Mem.record_init_sp m0 = Some m2 ->
      initial_state p (Callstate nil f (Locmap.init Vundef) (Mem.push_new_stage m2) (fn_stack_requirements (prog_main p))).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m retcode,
      Locmap.getpair (map_rpair R (loc_result signature_main)) rs = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.

Definition semantics (p: program) :=
  Semantics (step (Locmap.init Vundef)) (initial_state p) final_state (Genv.globalenv p).

End WITHEXTERNALCALLSOPS.

(** * Operations over LTL *)

(** Computation of the possible successors of a block.
  This is used in particular for dataflow analyses. *)

Fixpoint successors_block (b: bblock) : list node :=
  match b with
  | nil => nil                          (**r should never happen *)
  | Ltailcall _ _ :: _ => nil
  | Lbranch s :: _ => s :: nil
  | Lcond _ _ s1 s2 :: _ => s1 :: s2 :: nil
  | Ljumptable _ tbl :: _ => tbl
  | Lreturn :: _ => nil
  | instr :: b' => successors_block b'
  end.

(** Invariant of RTL programs  *)

Definition block_of_stackframe s: option (block * Z) :=
  match s with
    Stackframe f (Vptr sp _) _ _ => Some (sp, fn_stacksize f)
  | _ => None
  end.

Section STACKINV.
  Context `{extcallops: ExternalCalls}.

  Inductive stack_inv : state -> Prop :=
  | stack_inv_regular: forall s f sp pc rs m o
                         (MSA1: match_stack (Some (sp, fn_stacksize f)::map block_of_stackframe s) (Mem.stack m)),
      stack_inv (State s f (Vptr sp o) pc rs m)
  | stack_inv_block: forall s f sp pc rs m o
                       (MSA1: match_stack (Some (sp, fn_stacksize f)::map block_of_stackframe s) (Mem.stack m)),
      stack_inv (Block s f (Vptr sp o) pc rs m)
  | stack_inv_call: forall s fd args m sz
                      (TOPNOPERM: top_tframe_tc (Mem.stack m))
                      (MSA1: match_stack (map block_of_stackframe s) (tl (Mem.stack m))),
      stack_inv (Callstate s fd args m sz)
  | stack_inv_return: forall s res m 
                        (MSA1: match_stack (map block_of_stackframe s) (tl (Mem.stack m))),
      stack_inv (Returnstate s res m).

  Variable fn_stack_requirements: ident -> Z.
  Variable p: program.
  Let ge := Genv.globalenv p.
  Variable init_ls: locset.

  Lemma stack_inv_inv:
    forall S1 t S2,
      step fn_stack_requirements init_ls ge S1 t S2 ->
      stack_inv S1 -> stack_inv S2.
  Proof.
    destruct 1; simpl; intros SI;
      inv SI; try econstructor; repeat rewrite_stack_blocks; eauto;
        try solve [inv MSA1; eauto].
    - constructor. reflexivity.
    - intros; constructor; reflexivity.
    - simpl.
      inv MSA1. inversion 1; subst. auto.
    - intro EQ1; rewrite EQ1 in MSA1; simpl in MSA1. econstructor; eauto; reflexivity.
    - inv MSA1. repeat destr_in H1. econstructor.
      rewrite_stack_blocks. rewrite <- H3. econstructor; eauto.
  Qed.

  Lemma stack_inv_initial:
    forall S
      (INIT: initial_state fn_stack_requirements p S),
      stack_inv S.
  Proof.
    intros; inv INIT; econstructor; rewrite_stack_blocks.
    constructor; reflexivity.
    constructor.
  Qed.

End STACKINV.
