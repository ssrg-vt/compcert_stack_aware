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

(** The Mach intermediate language: abstract syntax.

  Mach is the last intermediate language before generation of assembly
  code.
*)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import Stacklayout.
Require Import Mach.

Section WITHEXTERNALCALLSOPS.
Context `{external_calls: ExternalCalls}.

Section RELSEM.
Variables init_ra: val.

Variable return_address_offset: function -> code -> ptrofs -> Prop.

Variable ge: genv.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Mlabel:
      forall s f sp lbl c rs m,
      step (State s f sp (Mlabel lbl :: c) rs m)
        E0 (State s f sp c rs m)
  | exec_Mgetstack:
      forall s f sp ofs ty dst c rs m v,
      load_stack m sp ty ofs = Some v ->
      step (State s f sp (Mgetstack ofs ty dst :: c) rs m)
        E0 (State s f sp c (rs#dst <- v) m)
  | exec_Msetstack:
      forall s f sp src ofs ty c rs m m' rs',
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      step (State s f sp (Msetstack src ofs ty :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mgetparam:
      forall s fb f sp ofs ty dst c rs m v rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      (* load_stack m sp Tptr f.(fn_link_ofs) = Some (parent_sp s) -> *)
      load_stack m (parent_sp (Mem.stack m)) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      step (State s fb sp (Mgetparam ofs ty dst :: c) rs m)
        E0 (State s fb sp c rs' m)
  | exec_Mop:
      forall s f sp op args res c rs m v rs',
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      step (State s f sp (Mop op args res :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mload:
      forall s f sp chunk addr args dst c rs m a v rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      step (State s f sp (Mload chunk addr args dst :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mstore:
      forall s f sp chunk addr args src c rs m m' a rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (State s f sp (Mstore chunk addr args src :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mcall:
      forall s fb sp sig ros c rs m f f' ra,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      step (State s fb (Vptr sp Ptrofs.zero) (Mcall sig ros :: c) rs m)
        E0 (Callstate (Stackframe fb sp (Vptr fb ra) c :: s)
                       f' rs (Mem.push_new_stage m))
  | exec_Mtailcall:
      forall s fb stk soff sig ros c rs m f f' m' m'',
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      (* load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp s) -> *)
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra init_ra s) ->
      Mem.free m stk (Ptrofs.unsigned soff) (Ptrofs.unsigned soff + f.(fn_stacksize)) = Some m' ->
      Mem.clear_stage m' = Some m'' ->
      step (State s fb (Vptr stk soff) (Mtailcall sig ros :: c) rs m)
        E0 (Callstate s f' rs m'')
  | exec_Mbuiltin:
      forall s f sp rs m ef args res b vargs t vres rs' m' m'',
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs (Mem.push_new_stage m) t vres m' ->
      Mem.unrecord_stack_block m' = Some m'' ->                                          
      rs' = set_res res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      forall BUILTIN_ENABLED : builtin_enabled ef,
      step (State s f sp (Mbuiltin ef args res :: b) rs m)
         t (State s f sp b rs' m'')
  | exec_Mgoto:
      forall s fb f sp lbl c rs m c',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s fb sp (Mgoto lbl :: c) rs m)
        E0 (State s fb sp c' rs m)
  | exec_Mcond_true:
      forall s fb f sp cond args lbl c rs m c' rs',
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s fb sp (Mcond cond args lbl :: c) rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mcond_false:
      forall s f sp cond args lbl c rs m rs',
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s f sp (Mcond cond args lbl :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mjumptable:
      forall s fb f sp arg tbl c rs m n lbl c' rs',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      step (State s fb sp (Mjumptable arg tbl :: c) rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mreturn:
      forall s fb stk soff c rs m f m' m'',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra init_ra s) ->
      Mem.free m stk (Ptrofs.unsigned soff) (Ptrofs.unsigned soff + f.(fn_stacksize)) = Some m' ->
      Mem.clear_stage m' = Some m'' ->
      step (State s fb (Vptr stk soff) (Mreturn :: c) rs m)
        E0 (Returnstate s rs m'')
  | exec_function_internal:
      forall s fb rs m f m1 m1_ m3 stk rs',
        Genv.find_funct_ptr ge fb = Some (Internal f) ->
        check_alloc_frame (fn_frame f) f  ->
       Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      let sp := Vptr stk Ptrofs.zero in
      store_stack m1 sp Tptr f.(fn_retaddr_ofs) (parent_ra init_ra s) = Some m3 ->
      Mem.record_stack_blocks m3 (make_singleton_frame_adt' stk (fn_frame f) (fn_stacksize f)) = Some m1_ ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      step (Callstate s fb rs m)
        E0 (State s fb sp f.(fn_code) rs' m1_)
  | exec_function_external:
      forall s fb rs m t rs' ef args res m',
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      extcall_arguments rs m (parent_sp (Mem.stack m)) (ef_sig ef) args ->
      external_call ef ge args m t res m' ->
      rs' = set_pair (loc_result (ef_sig ef)) res (undef_regs destroyed_at_call rs) ->
      step (Callstate s fb rs m)
         t (Returnstate s rs' m')
  | exec_return:
      forall s f sp ra c rs m m',
        Mem.unrecord_stack_block m = Some m' ->
      step (Returnstate (Stackframe f sp ra c :: s) rs m)
        E0 (State s f (Vptr sp Ptrofs.zero) c rs m').

Inductive callstack_function_defined : list stackframe -> Prop :=
| cfd_empty:
    callstack_function_defined nil
| cfd_cons:
    forall fb sp' ra c' cs' trf
      (FINDF: Genv.find_funct_ptr ge fb = Some (Internal trf))
      (CFD: callstack_function_defined cs'),
      callstack_function_defined (Stackframe fb sp' ra c' :: cs').

Variable init_sg: signature.
Variable init_stk: stack.

Inductive list_prefix : list (option (block * frame_info)) -> stack -> Prop :=
| list_prefix_nil s
                  (INITSTACK: s = init_stk)
                  (STACKINFO: init_sp_stackinfo init_sg s):
    list_prefix nil s
| list_prefix_cons lsp s f sp bi
                   (REC: list_prefix lsp s)
                   (FSIZE: frame_adt_size f = frame_size bi)
                   (BLOCKS: frame_adt_blocks f = (sp,bi)::nil):
    list_prefix (Some (sp,bi) :: lsp) ( (f :: nil) :: s).

Inductive call_stack_consistency: state -> Prop :=
| call_stack_consistency_intro:
    forall c cs' fb sp' rs m' tf
      (FIND: Genv.find_funct_ptr ge fb = Some (Internal tf))
      (CallStackConsistency: list_prefix ((Some (sp', fn_frame tf))::stack_blocks_of_callstack ge cs') (Mem.stack m'))
      (CFD: callstack_function_defined cs'),
      call_stack_consistency (State cs' fb (Vptr sp' Ptrofs.zero) c rs m')
| call_stack_consistency_call:
    forall cs' fb rs m'
      (CallStackConsistency: list_prefix (stack_blocks_of_callstack ge cs') (tl (Mem.stack m')))
      (TIN: Mem.top_is_new m')
      (CFD: callstack_function_defined cs'),
      call_stack_consistency (Callstate cs' fb rs m')
| call_stack_consistency_return:
    forall cs' rs m'
      (CallStackConsistency: list_prefix (stack_blocks_of_callstack ge cs') (tl (Mem.stack m')))
      (TIN: Mem.top_is_new m')
      (CFD: callstack_function_defined cs'),
      call_stack_consistency (Returnstate cs' rs m').

Lemma store_stack_no_abstract:
  forall sp ty o v,
    Mem.abstract_unchanged (fun m m' => store_stack m sp ty o v = Some m').
Proof.
  unfold store_stack, Mem.storev.
  red; simpl; intros.
  destruct (Val.offset_ptr sp o); try discriminate.
  eapply Mem.store_no_abstract; eauto.
Qed.

Lemma csc_step:
  forall s1 t s2,
    step s1 t s2 ->
    (forall fb f, Genv.find_funct_ptr ge fb = Some (Internal f) ->
             frame_size (fn_frame f) = fn_stacksize f) ->
    call_stack_consistency s1 ->
    call_stack_consistency s2.
Proof.
  destruct 1; simpl; intros SIZECORRECT CSC; inv CSC; try now (econstructor; eauto).
  - econstructor; eauto. erewrite store_stack_no_abstract; eauto.
  - econstructor; eauto. destruct a; simpl in *; try discriminate. erewrite Mem.store_no_abstract; eauto.
  - econstructor. rewrite_stack_blocks. simpl. 
    rewrite FIND. repeat rewrite_stack_blocks. simpl. auto.
    red. rewrite_stack_blocks. constructor. auto.
    econstructor; eauto.
  - econstructor; repeat rewrite_stack_blocks. simpl; auto.
    inv CallStackConsistency; simpl; auto.
    red. rewrite_stack_blocks. constructor. auto. auto.
  - econstructor; eauto; repeat rewrite_stack_blocks; simpl; eauto.
  - econstructor; eauto; repeat rewrite_stack_blocks; simpl; eauto.
    inv CallStackConsistency. simpl. auto.
    red. rewrite_stack_blocks. constructor; auto.
  - unfold store_stack in H2.
    econstructor; eauto; repeat rewrite_stack_blocks; simpl; eauto.
    revert EQ1; repeat rewrite_stack_blocks. intro. rewrite EQ1 in CallStackConsistency. simpl in *.
    inv TIN. rewrite EQ1 in H4; inv H4.
    econstructor; eauto.
    simpl.
    erewrite <- SIZECORRECT. apply Z.max_r. apply frame_size_pos. eauto.
  - econstructor; eauto; repeat rewrite_stack_blocks; simpl; eauto.
    red; inv TIN. rewrite_stack_blocks. rewrite <- H2. constructor; auto.
  - inv CFD. econstructor; eauto; repeat rewrite_stack_blocks; simpl; eauto.
    simpl in *; eauto. rewrite FINDF in CallStackConsistency. eauto.
Qed.

Lemma store_stack_nextblock:
  forall m v ty p v1 m',
    store_stack m v ty p v1 = Some m' ->
    Mem.nextblock m' = Mem.nextblock m.
Proof.
  unfold store_stack; intros.
  destruct (Val.offset_ptr v p); simpl in *; inv H;  eauto with mem.
Qed.

End RELSEM.

Definition semantics (rao: function -> code -> ptrofs -> Prop) (p: program) :=
  Semantics (step Vnullptr rao) (initial_state p) final_state (Genv.globalenv p).

End WITHEXTERNALCALLSOPS.
