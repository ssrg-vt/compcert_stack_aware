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

(** Elimination of unneeded computations over RTL: correctness proof. *)

Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL.
Require Import ValueDomain ValueAnalysis NeedDomain NeedOp Deadcode.

Section WITHROMEMFOR.
Context `{romem_for_instance: ROMemFor}.

Definition match_prog (prog tprog: RTL.program) :=
  match_program (fun cu f tf => transf_fundef (romem_for cu) f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

End WITHROMEMFOR.

(** * Relating the memory states *)

Local Notation locset := Mem.locset.
Local Notation magree := Mem.magree.

Local Notation magree_storebytes_parallel := Mem.magree_storebytes_parallel.
Local Notation magree_monotone := Mem.magree_monotone.
Local Notation magree_load := Mem.magree_load.
Local Notation magree_valid_access := Mem.magree_valid_access.
Local Notation ma_perm := Mem.ma_perm.
Local Notation magree_store_left := Mem.magree_store_left.
Local Notation magree_extends := Mem.magree_extends.
Local Notation magree_free := Mem.magree_free.
Local Notation magree_loadbytes := Mem.magree_loadbytes.
Local Notation magree_storebytes_left := Mem.magree_storebytes_left.
Local Notation mextends_agree := Mem.mextends_agree.
Local Notation magree_push := Mem.magree_push.
Local Notation magree_unrecord := Mem.magree_unrecord.


Lemma magree_store_parallel:
  forall `{memory_model_prf: Mem.MemoryModel} {injperm: InjectPerm},
  forall m1 m2 (P Q: locset) chunk b ofs v1 m1' v2,
  magree m1 m2 P ->
  Mem.store chunk m1 b ofs v1 = Some m1' ->
  vagree v1 v2 (store_argument chunk) ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + size_chunk chunk <= i ->
                P b' i) ->
  exists m2', Mem.store chunk m2 b ofs v2 = Some m2' /\ magree m1' m2' Q.
Proof.
  intros.
  exploit Mem.store_valid_access_3; eauto. intros [A [B C]].
  exploit Mem.store_storebytes; eauto. intros SB1.
  exploit magree_storebytes_parallel. eauto. eauto.
  instantiate (1 := Q). intros. rewrite encode_val_length in H4.
  rewrite <- size_chunk_conv in H4. apply H2; auto.
  eapply store_argument_sound; eauto.
  intros [m2' [SB2 AG]].
  exists m2'; split; auto.
  apply Mem.storebytes_store; auto.
Qed.

(** * Properties of the need environment *)

Lemma add_need_all_eagree:
  forall e e' r ne,
  eagree e e' (add_need_all r ne) -> eagree e e' ne.
Proof.
  intros; red; intros. generalize (H r0). unfold add_need_all.
  rewrite NE.gsspec. destruct (peq r0 r); auto with na.
Qed.

Lemma add_need_all_lessdef:
  forall e e' r ne,
  eagree e e' (add_need_all r ne) -> Val.lessdef e#r e'#r.
Proof.
  intros. generalize (H r); unfold add_need_all.
  rewrite NE.gsspec, peq_true. auto with na.
Qed.

Lemma add_need_eagree:
  forall e e' r nv ne,
  eagree e e' (add_need r nv ne) -> eagree e e' ne.
Proof.
  intros; red; intros. generalize (H r0); unfold add_need.
  rewrite NE.gsspec. destruct (peq r0 r); auto.
  subst r0. intros. eapply nge_agree; eauto. apply nge_lub_r.
Qed.

Lemma add_need_vagree:
  forall e e' r nv ne,
  eagree e e' (add_need r nv ne) -> vagree e#r e'#r nv.
Proof.
  intros. generalize (H r); unfold add_need.
  rewrite NE.gsspec, peq_true. intros. eapply nge_agree; eauto. apply nge_lub_l.
Qed.

Lemma add_needs_all_eagree:
  forall rl e e' ne,
  eagree e e' (add_needs_all rl ne) -> eagree e e' ne.
Proof.
  induction rl; simpl; intros.
  auto.
  apply IHrl. eapply add_need_all_eagree; eauto.
Qed.

Lemma add_needs_all_lessdef:
  forall rl e e' ne,
  eagree e e' (add_needs_all rl ne) -> Val.lessdef_list e##rl e'##rl.
Proof.
  induction rl; simpl; intros.
  constructor.
  constructor. eapply add_need_all_lessdef; eauto.
  eapply IHrl. eapply add_need_all_eagree; eauto.
Qed.

Lemma add_needs_eagree:
  forall rl nvl e e' ne,
  eagree e e' (add_needs rl nvl ne) -> eagree e e' ne.
Proof.
  induction rl; simpl; intros.
  auto.
  destruct nvl. apply add_needs_all_eagree with (a :: rl); auto.
  eapply IHrl. eapply add_need_eagree; eauto.
Qed.

Lemma add_needs_vagree:
  forall rl nvl e e' ne,
  eagree e e' (add_needs rl nvl ne) -> vagree_list e##rl e'##rl nvl.
Proof.
  induction rl; simpl; intros.
  constructor.
  destruct nvl.
  apply vagree_lessdef_list. eapply add_needs_all_lessdef with (rl := a :: rl); eauto.
  constructor. eapply add_need_vagree; eauto.
  eapply IHrl. eapply add_need_eagree; eauto.
Qed.

Lemma add_ros_need_eagree:
  forall e e' ros ne, eagree e e' (add_ros_need_all ros ne) -> eagree e e' ne.
Proof.
  intros. destruct ros; simpl in *. eapply add_need_all_eagree; eauto. auto.
Qed.

Hint Resolve add_need_all_eagree add_need_all_lessdef
             add_need_eagree add_need_vagree
             add_needs_all_eagree add_needs_all_lessdef
             add_needs_eagree add_needs_vagree
             add_ros_need_eagree: na.

Lemma eagree_init_regs:
  forall rl vl1 vl2 ne,
  Val.lessdef_list vl1 vl2 ->
  eagree (init_regs vl1 rl) (init_regs vl2 rl) ne.
Proof.
  induction rl; intros until ne; intros LD; simpl.
- red; auto with na.
- inv LD.
  + red; auto with na.
  + apply eagree_update; auto with na.
Qed.

(** * Basic properties of the translation *)

Section PRESERVATION.
Context `{external_calls_prf: ExternalCalls}.
Existing Instance inject_perm_all.

Variable prog: program.
Variable tprog: program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Section WITHROMEMFOR.
Context `{romem_for_instance: ROMemFor}.

Hypothesis TRANSF: match_prog prog tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma genv_next_preserved:
  Genv.genv_next tge = Genv.genv_next ge.
Proof.
  apply senv_preserved.
Qed.

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists cu tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef (romem_for cu) f = OK tf /\ linkorder cu prog.
Proof (Genv.find_funct_match TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef (romem_for cu) f = OK tf /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match TRANSF).

Lemma sig_function_translated:
  forall rm f tf,
  transf_fundef rm f = OK tf ->
  funsig tf = funsig f.
Proof.
  intros; destruct f; monadInv H.
  unfold transf_function in EQ.
  destruct (analyze (ValueAnalysis.analyze rm f) f); inv EQ; auto.
  auto.
Qed.

Lemma stacksize_translated:
  forall rm f tf,
  transf_function rm f = OK tf -> tf.(fn_stacksize) = f.(fn_stacksize).
Proof.
  unfold transf_function; intros. destruct (analyze (ValueAnalysis.analyze rm f) f); inv H; auto.
Qed.

Definition vanalyze (cu: program) (f: function) :=
  ValueAnalysis.analyze (romem_for cu) f.

Lemma transf_function_at:
  forall cu f tf an pc instr,
  transf_function (romem_for cu) f = OK tf ->
  analyze (vanalyze cu f) f = Some an ->
  f.(fn_code)!pc = Some instr ->
  tf.(fn_code)!pc = Some(transf_instr (vanalyze cu f) an pc instr).
Proof.
  intros. unfold transf_function in H. unfold vanalyze in H0. rewrite H0 in H. inv H; simpl.
  rewrite PTree.gmap. rewrite H1; auto.
Qed.

Lemma is_dead_sound_1:
  forall nv, is_dead nv = true -> nv = Nothing.
Proof.
  destruct nv; simpl; congruence.
Qed.

Lemma is_dead_sound_2:
  forall nv, is_dead nv = false -> nv <> Nothing.
Proof.
  intros; red; intros. subst nv; discriminate.
Qed.

Hint Resolve is_dead_sound_1 is_dead_sound_2: na.

Lemma is_int_zero_sound:
  forall nv, is_int_zero nv = true -> nv = I Int.zero.
Proof.
  unfold is_int_zero; destruct nv; try discriminate.
  predSpec Int.eq Int.eq_spec m Int.zero; congruence.
Qed.

Lemma find_function_translated:
  forall ros rs fd trs ne,
  find_function ge ros rs = Some fd ->
  eagree rs trs (add_ros_need_all ros ne) ->
  exists cu tfd,
     find_function tge ros trs = Some tfd
  /\ transf_fundef (romem_for cu) fd = OK tfd
  /\ linkorder cu prog.
Proof.
  intros. destruct ros as [r|id]; simpl in *.
- assert (LD: Val.lessdef rs#r trs#r) by eauto with na. inv LD.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  apply function_ptr_translated; auto.
Qed.

(** * Semantic invariant *)

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall res f sp pc e tf te cu an
        (LINK: linkorder cu prog)
        (FUN: transf_function (romem_for cu) f = OK tf)
        (ANL: analyze (vanalyze cu f) f = Some an)
        (RES: forall v tv,
              Val.lessdef v tv ->
              eagree (e#res <- v) (te#res<- tv)
                     (fst (transfer f (vanalyze cu f) pc an!!pc))),
      match_stackframes (Stackframe res f (Vptr sp Ptrofs.zero) pc e)
                        (Stackframe res tf (Vptr sp Ptrofs.zero) pc te).

Inductive match_states: state -> state -> Prop :=
  | match_regular_states:
      forall s f sp pc e m ts tf te tm cu an
        (STACKS: list_forall2 match_stackframes s ts)
        (LINK: linkorder cu prog)
        (FUN: transf_function (romem_for cu) f = OK tf)
        (ANL: analyze (vanalyze cu f) f = Some an)
        (ENV: eagree e te (fst (transfer f (vanalyze cu f) pc an!!pc)))
        (MEM: magree m tm (nlive ge sp (snd (transfer f (vanalyze cu f) pc an!!pc)))),
      match_states (State s f (Vptr sp Ptrofs.zero) pc e m)
                   (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
  | match_call_states:
      forall s f args m ts tf targs tm cu sz
        (STACKS: list_forall2 match_stackframes s ts)
        (LINK: linkorder cu prog)
        (FUN: transf_fundef (romem_for cu) f = OK tf)
        (ARGS: Val.lessdef_list args targs)
        (MEM: Mem.extends m tm),
      match_states (Callstate s f args m sz)
                   (Callstate ts tf targs tm sz)
  | match_return_states:
      forall s v m ts tv tm
        (STACKS: list_forall2 match_stackframes s ts)
        (RES: Val.lessdef v tv)
        (MEM: Mem.extends m tm),
      match_states (Returnstate s v m)
                   (Returnstate ts tv tm).

(** [match_states] and CFG successors *)

Lemma analyze_successors:
  forall cu f an pc instr pc',
  analyze (vanalyze cu f) f = Some an ->
  f.(fn_code)!pc = Some instr ->
  In pc' (successors_instr instr) ->
  NA.ge an!!pc (transfer f (vanalyze cu f) pc' an!!pc').
Proof.
  intros. eapply DS.fixpoint_solution; eauto.
  intros. unfold transfer; rewrite H2. destruct a. apply DS.L.eq_refl.
Qed.

Lemma match_succ_states:
  forall s f sp pc e m ts tf te tm an pc' cu instr ne nm
    (LINK: linkorder cu prog)
    (STACKS: list_forall2 match_stackframes s ts)
    (FUN: transf_function (romem_for cu) f = OK tf)
    (ANL: analyze (vanalyze cu f) f = Some an)
    (INSTR: f.(fn_code)!pc = Some instr)
    (SUCC: In pc' (successors_instr instr))
    (ANPC: an!!pc = (ne, nm))
    (ENV: eagree e te ne)
    (MEM: magree m tm (nlive ge sp nm)),
  match_states (State s f (Vptr sp Ptrofs.zero) pc' e m)
               (State ts tf (Vptr sp Ptrofs.zero) pc' te tm).
Proof.
  intros. exploit analyze_successors; eauto. rewrite ANPC; simpl. intros [A B].
  econstructor; eauto.
  eapply eagree_ge; eauto.
  eapply magree_monotone; eauto.
Qed.

(** Builtin arguments and results *)

Lemma eagree_set_res:
  forall e1 e2 v1 v2 res ne,
  Val.lessdef v1 v2 ->
  eagree e1 e2 (kill_builtin_res res ne) ->
  eagree (regmap_setres res v1 e1) (regmap_setres res v2 e2) ne.
Proof.
  intros. destruct res; simpl in *; auto.
  apply eagree_update; eauto. apply vagree_lessdef; auto.
Qed.

Lemma transfer_builtin_arg_sound:
  forall bc e e' sp m m' a v,
  eval_builtin_arg ge (fun r => e#r) (Vptr sp Ptrofs.zero) m a v ->
  forall nv ne1 nm1 ne2 nm2,
  transfer_builtin_arg nv (ne1, nm1) a = (ne2, nm2) ->
  eagree e e' ne2 ->
  magree m m' (nlive ge sp nm2) ->
  genv_match bc ge ->
  bc sp = BCstack ->
  exists v',
     eval_builtin_arg ge (fun r => e'#r) (Vptr sp Ptrofs.zero) m' a  v'
  /\ vagree v v' nv
  /\ eagree e e' ne1
  /\ magree m m' (nlive ge sp nm1).
Proof.
  induction 1; simpl; intros until nm2; intros TR EA MA GM SPM; inv TR.
- exists e'#x; intuition auto. constructor. eauto 2 with na. eauto 2 with na.
- exists (Vint n); intuition auto. constructor. apply vagree_same.
- exists (Vlong n); intuition auto. constructor. apply vagree_same.
- exists (Vfloat n); intuition auto. constructor. apply vagree_same.
- exists (Vsingle n); intuition auto. constructor. apply vagree_same.
- simpl in H. exploit magree_load; eauto.
  intros. eapply nlive_add; eauto with va. rewrite Ptrofs.add_zero_l in H0; auto.
  intros (v' & A & B).
  exists v'; intuition auto. constructor; auto. apply vagree_lessdef; auto.
  eapply magree_monotone; eauto. intros; eapply incl_nmem_add; eauto.
- exists (Vptr sp (Ptrofs.add Ptrofs.zero ofs)); intuition auto with na. constructor.
- unfold Senv.symbol_address in H; simpl in H.
  destruct (Genv.find_symbol ge id) as [b|] eqn:FS; simpl in H; try discriminate.
  exploit magree_load; eauto.
  intros. eapply nlive_add; eauto. constructor. apply GM; auto.
  intros (v' & A & B).
  exists v'; intuition auto.
  constructor. simpl. unfold Senv.symbol_address; simpl; rewrite FS; auto.
  apply vagree_lessdef; auto.
  eapply magree_monotone; eauto. intros; eapply incl_nmem_add; eauto.
- exists (Senv.symbol_address ge id ofs); intuition auto with na. constructor.
- destruct (transfer_builtin_arg All (ne1, nm1) hi) as [ne' nm'] eqn:TR.
  exploit IHeval_builtin_arg2; eauto. intros (vlo' & A & B & C & D).
  exploit IHeval_builtin_arg1; eauto. intros (vhi' & P & Q & R & S).
  exists (Val.longofwords vhi' vlo'); intuition auto.
  constructor; auto.
  apply vagree_lessdef.
  apply Val.longofwords_lessdef; apply lessdef_vagree; auto.
Qed.

Lemma transfer_builtin_args_sound:
  forall e sp m e' m' bc al vl,
  eval_builtin_args ge (fun r => e#r) (Vptr sp Ptrofs.zero) m al vl ->
  forall ne1 nm1 ne2 nm2,
  transfer_builtin_args (ne1, nm1) al = (ne2, nm2) ->
  eagree e e' ne2 ->
  magree m m' (nlive ge sp nm2) ->
  genv_match bc ge ->
  bc sp = BCstack ->
  exists vl',
     eval_builtin_args ge (fun r => e'#r) (Vptr sp Ptrofs.zero) m' al vl'
  /\ Val.lessdef_list vl vl'
  /\ eagree e e' ne1
  /\ magree m m' (nlive ge sp nm1).
Proof.
Local Opaque transfer_builtin_arg.
  induction 1; simpl; intros.
- inv H. exists (@nil val); intuition auto. constructor.
- destruct (transfer_builtin_arg All (ne1, nm1) a1) as [ne' nm'] eqn:TR.
  exploit IHlist_forall2; eauto. intros (vs' & A1 & B1 & C1 & D1).
  exploit transfer_builtin_arg_sound; eauto. intros (v1' & A2 & B2 & C2 & D2).
  exists (v1' :: vs'); intuition auto. constructor; auto.
Qed.

Lemma can_eval_builtin_arg:
  forall sp e m e' m' P,
  magree m m' P ->
  forall a v,
  eval_builtin_arg ge (fun r => e#r) (Vptr sp Ptrofs.zero) m a v ->
  exists v', eval_builtin_arg tge (fun r => e'#r) (Vptr sp Ptrofs.zero) m' a v'.
Proof.
  intros until P; intros MA.
  assert (LD: forall chunk addr v,
              Mem.loadv chunk m addr = Some v ->
              exists v', Mem.loadv chunk m' addr = Some v').
  {
    intros. destruct addr; simpl in H; try discriminate.
    eapply Mem.valid_access_load. eapply magree_valid_access; eauto.
    eapply Mem.load_valid_access; eauto.
    eapply inject_perm_condition_writable; constructor.
  }
  induction 1; try (econstructor; now constructor).
- exploit LD; eauto. intros (v' & A). exists v'; constructor; auto.
- exploit LD; eauto. intros (v' & A). exists v'; constructor.
  unfold Senv.symbol_address, Senv.find_symbol. rewrite symbols_preserved. assumption.
- destruct IHeval_builtin_arg1 as (v1' & A1).
  destruct IHeval_builtin_arg2 as (v2' & A2).
  exists (Val.longofwords v1' v2'); constructor; auto.
Qed.

Lemma can_eval_builtin_args:
  forall sp e m e' m' P,
  magree m m' P ->
  forall al vl,
  eval_builtin_args ge (fun r => e#r) (Vptr sp Ptrofs.zero) m al vl ->
  exists vl', eval_builtin_args tge (fun r => e'#r) (Vptr sp Ptrofs.zero) m' al vl'.
Proof.
  induction 2.
- exists (@nil val); constructor.
- exploit can_eval_builtin_arg; eauto. intros (v' & A).
  destruct IHlist_forall2 as (vl' & B).
  exists (v' :: vl'); constructor; eauto.
Qed.

(** Properties of volatile memory accesses *)


Lemma transf_volatile_store:
  forall v1 v2 v1' v2' m tm chunk sp nm t v m',
  volatile_store_sem chunk ge (v1::v2::nil) m t v m' ->
  Val.lessdef v1 v1' ->
  vagree v2 v2' (store_argument chunk) ->
  magree m tm (nlive ge sp nm) ->
  v = Vundef /\
  exists tm', volatile_store_sem chunk ge (v1'::v2'::nil) tm t Vundef tm'
         /\ magree m' tm' (nlive ge sp nm).
Proof.
  intros. inv H. split; auto.
  inv H0. inv H9.
- (* volatile *)
  exists tm; split; auto. econstructor. econstructor; eauto.
  eapply eventval_match_lessdef; eauto. apply store_argument_load_result; auto.
- (* not volatile *)
  exploit magree_store_parallel. eauto. eauto. eauto.
  instantiate (1 := nlive ge sp nm). auto.
  intros (tm' & P & Q).
  exists tm'; split. econstructor. econstructor; eauto.
  auto.
Qed.

Lemma eagree_set_undef:
  forall e1 e2 ne r, eagree e1 e2 ne -> eagree (e1#r <- Vundef) e2 ne.
Proof.
  intros; red; intros. rewrite PMap.gsspec. destruct (peq r0 r); auto with na.
Qed.

(** * The simulation diagram *)

Variable fn_stack_requirements: ident -> Z.


Ltac TransfInstr :=
  match goal with
  | [INSTR: (fn_code _)!_ = Some _,
     FUN: transf_function _ _ = OK _,
     ANL: analyze _ _ = Some _ |- _ ] =>
       generalize (transf_function_at _ _ _ _ _ _ FUN ANL INSTR);
       let TI := fresh "TI" in
       intro TI; unfold transf_instr in TI
  end.

Ltac UseTransfer :=
  match goal with
  | [INSTR: (fn_code _)!?pc = Some _,
     ANL: analyze _ _ = Some ?an |- _ ] =>
       destruct (an!!pc) as [ne nm] eqn:ANPC;
       unfold transfer in *;
       rewrite INSTR in *;
       simpl in *
  end.


Lemma stack_equiv_inv_step:
  forall S1 t S2
    (STEP: step fn_stack_requirements ge S1 t S2)
    S1' (MS: match_states S1 S1')
    S2' (STEP': step fn_stack_requirements tge S1' t S2')
    (SEI: stack_equiv_inv S1 S1'),
    stack_equiv_inv S2 S2'.
Proof.
  intros.
  inv STEP; inv MS; try TransfInstr; inv STEP'; try congruence;
    unfold stack_equiv_inv in *; simpl in *; repeat rewrite_stack_blocks; eauto;
      try match goal with
        H1: (fn_code ?f) ! ?pc = _,
            H2: (fn_code ?f) ! ?pc = _ |- _ =>
        rewrite H1 in H2; repeat destr_in H2
      end.
  - repeat constructor; auto.
  - intros A B; revert SEI; rewrite A, B. simpl.
    inversion 1; subst. repeat constructor; simpl; auto.
    destruct LF2; simpl; auto.
    red in H1; repeat destr_in H1; constructor; auto.
  - intros A B; revert SEI; rewrite A, B. simpl.
    inversion 1; subst. repeat constructor; simpl; auto.
    destruct LF2; simpl; auto.
  - monadInv FUN.
  - monadInv FUN.
  - eauto using stack_equiv_tail.
Qed.

Theorem step_simulation:
  forall S1 t S2, step fn_stack_requirements ge S1 t S2 ->
  forall S1', match_states S1 S1' -> sound_state prog S1 -> stack_inv S1' -> stack_equiv_inv S1 S1' ->
  exists S2', step fn_stack_requirements tge S1' t S2' /\ match_states S2 S2'.
Proof.

  induction 1; intros S1' MS SS SI SEI; inv MS.

- (* nop *)
  TransfInstr; UseTransfer.
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.

- (* op *)
  TransfInstr; UseTransfer.
  destruct (is_dead (nreg ne res)) eqn:DEAD;
  [idtac|destruct (is_int_zero (nreg ne res)) eqn:INTZERO;
  [idtac|destruct (operation_is_redundant op (nreg ne res)) eqn:REDUNDANT]].
+ (* dead instruction, turned into a nop *)
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update_dead; auto with na.
+ (* instruction with needs = [I Int.zero], turned into a load immediate of zero. *)
  econstructor; split.
  eapply exec_Iop with (v0 := Vint Int.zero); eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto.
  rewrite is_int_zero_sound by auto.
  destruct v; simpl; auto. apply iagree_zero.
+ (* redundant operation *)
  destruct args.
  * (* kept as is because no arguments -- should never happen *)
  simpl in *.
  exploit needs_of_operation_sound. intros; eapply ma_perm; eauto. constructor.
  eauto. instantiate (1 := nreg ne res). eauto with na. eauto with na. intros [tv [A B]].
  econstructor; split.
  eapply exec_Iop with (v0 := tv); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto.
  * (* turned into a move *)
  unfold fst in ENV. unfold snd in MEM. simpl in H0.
  assert (VA: vagree v te#r (nreg ne res)).
  { eapply operation_is_redundant_sound with (arg1' := te#r) (args' := te##args).
    eauto. eauto. exploit add_needs_vagree; eauto. }
  econstructor; split.
  eapply exec_Iop; eauto. simpl; reflexivity.
  eapply match_succ_states; eauto. simpl; auto.
  eapply eagree_update; eauto 2 with na.
+ (* preserved operation *)
  simpl in *.
  exploit needs_of_operation_sound. intros; eapply ma_perm; eauto. constructor. eauto. eauto 2 with na. eauto with na.
  intros [tv [A B]].
  econstructor; split.
  eapply exec_Iop with (v0 := tv); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.

- (* load *)
  TransfInstr; UseTransfer.
  destruct (is_dead (nreg ne dst)) eqn:DEAD;
  [idtac|destruct (is_int_zero (nreg ne dst)) eqn:INTZERO];
  simpl in *.
+ (* dead instruction, turned into a nop *)
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update_dead; auto with na.
+ (* instruction with needs = [I Int.zero], turned into a load immediate of zero. *)
  econstructor; split.
  eapply exec_Iop with (v0 := Vint Int.zero); eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto.
  rewrite is_int_zero_sound by auto.
  destruct v; simpl; auto. apply iagree_zero.
+ (* preserved *)
  exploit eval_addressing_lessdef. eapply add_needs_all_lessdef; eauto. eauto.
  intros (ta & U & V). inv V; try discriminate.
  destruct ta; simpl in H1; try discriminate.
  exploit magree_load; eauto.
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. apply nlive_add with bc i; assumption.
  intros (tv & P & Q).
  econstructor; split.
  eapply exec_Iload with (a := Vptr b i). eauto.
  rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved.
  eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na.
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto.

- (* store *)
  TransfInstr; UseTransfer.
  destruct (nmem_contains nm (aaddressing (vanalyze cu f) # pc addr args)
             (size_chunk chunk)) eqn:CONTAINS.
+ (* preserved *)
  simpl in *.
  exploit eval_addressing_lessdef. eapply add_needs_all_lessdef; eauto. eauto.
  intros (ta & U & V). inv V; try discriminate.
  destruct ta; simpl in H1; try discriminate.
  exploit magree_store_parallel. eauto. eauto. instantiate (1 := te#src). eauto with na.
  instantiate (1 := nlive ge sp0 nm).
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. apply nlive_remove with bc b i; assumption.
  intros (tm' & P & Q).
  econstructor; split.
  eapply exec_Istore with (a := Vptr b i). eauto.
  rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved.
  eauto.
  eapply match_succ_states; eauto. simpl; auto.
  eauto 3 with na.
+ (* dead instruction, turned into a nop *)
  destruct a; simpl in H1; try discriminate.
  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  eapply magree_store_left; eauto.
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. eapply nlive_contains; eauto.

- (* call *)
  TransfInstr; UseTransfer.
  exploit find_function_translated; eauto 2 with na. intros (cu' & tfd & A & B & C).
  econstructor; split.
  eapply exec_Icall; eauto.
  {
    destruct ros; simpl in RIF |- *; auto.
    destruct RIF as (b & o & EQ & EQ1).      
    simpl. 
    apply add_needs_all_eagree in ENV.
    eapply add_need_all_lessdef in ENV.
    generalize (ENV). rewrite EQ. inversion 1.
    rewrite symbols_preserved; eauto.
    auto.
  }
  eapply sig_function_translated; eauto.
  eapply match_call_states with (cu := cu'); eauto.
  constructor; auto. eapply match_stackframes_intro with (cu := cu); eauto.
  intros.
  edestruct analyze_successors; eauto. simpl; eauto.
  eapply eagree_ge; eauto. rewrite ANPC. simpl.
  apply eagree_update; eauto with na.
  eauto 2 with na.
  apply Mem.extends_push.
  eapply magree_extends; eauto. apply nlive_all.

- (* tailcall *)
  TransfInstr; UseTransfer.
  exploit find_function_translated; eauto 2 with na. intros (cu' & tfd & A & B & L).
  exploit magree_free. eauto. constructor. eauto. instantiate (1 := nlive ge stk nmem_all).
  intros; eapply nlive_dead_stack; eauto.
  intros (tm' & C & D).
  exploit Mem.magree_tailcall_stage; eauto. inv SI. inv MSA1.
  eapply Mem.free_top_tframe_no_perm; eauto.
  erewrite <- stacksize_translated; eauto.
  intros (tm2' & E & F).
  econstructor; split.
  eapply exec_Itailcall; eauto.
  {
    destruct ros; simpl in RIF |- *; auto.
    destruct RIF as (b & o & EQ & EQ1).      
    simpl. 
    apply add_needs_all_eagree in ENV.
    eapply add_need_all_lessdef in ENV.
    generalize (ENV). rewrite EQ. inversion 1.
    rewrite symbols_preserved; eauto.
    auto.
  }
  eapply sig_function_translated; eauto.
  erewrite stacksize_translated by eauto. eexact C.
  eapply match_call_states with (cu := cu'); eauto 2 with na.
  eapply Mem.magree_extends; eauto. apply nlive_all.

- (* builtin *)
  TransfInstr; UseTransfer. revert ENV MEM TI.
  functional induction (transfer_builtin (vanalyze cu f)#pc ef args res ne nm);
  simpl in *; intros.
+ (* volatile load *)
  inv H0. inv H7. rename b1 into v1.
  destruct (transfer_builtin_arg All
              (kill_builtin_res res ne,
              nmem_add nm (aaddr_arg (vanalyze cu f) # pc a1)
                (size_chunk chunk)) a1) as (ne1, nm1) eqn: TR.
  InvSoundState. exploit transfer_builtin_arg_sound; eauto.
  intros (tv1 & A & B & C & D).
  inv H1. simpl in B. inv B.
  assert (X: exists tvres, volatile_load ge chunk (Mem.push_new_stage tm) b ofs t tvres /\ Val.lessdef vres tvres).
  {
    inv H3.
  * exists (Val.load_result chunk v); split; auto. constructor; auto.
  * exploit magree_load.
    apply Mem.magree_push. eauto. eauto.
    exploit aaddr_arg_sound_1; eauto. rewrite <- AN. intros.
    intros. eapply nlive_add; eassumption.
    intros (tv & P & Q).
    exists tv; split; auto. constructor; auto.
  }
  destruct X as (tvres & P & Q).
  rewrite Mem.unrecord_push in H2; inv H2.
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  apply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  constructor. eauto. constructor.
  eapply external_call_symbols_preserved. apply senv_preserved.
  constructor. simpl. eauto. apply Mem.unrecord_push.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto.
+ (* volatile store *)
  inv H0. inv H7. inv H8. rename b1 into v1. rename b0 into v2.
  destruct (transfer_builtin_arg (store_argument chunk)
              (kill_builtin_res res ne, nm) a2) as (ne2, nm2) eqn: TR2.
  destruct (transfer_builtin_arg All (ne2, nm2) a1) as (ne1, nm1) eqn: TR1.
  InvSoundState.
  exploit transfer_builtin_arg_sound. eexact H5. eauto. eauto. eauto. eauto. eauto.
  intros (tv1 & A1 & B1 & C1 & D1).
  exploit transfer_builtin_arg_sound. eexact H4. eauto. eauto. eauto. eauto. eauto.
  intros (tv2 & A2 & B2 & C2 & D2).
  exploit transf_volatile_store; eauto. apply magree_push. apply D2.
  intros (EQ & tm' & P & Q). subst vres.
  edestruct magree_unrecord as (m2' & USB & MAG). apply Q. eauto.
  econstructor; split.
  eapply exec_Ibuiltin. eauto.
  apply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  constructor. eauto. constructor. eauto. constructor.
  eapply external_call_symbols_preserved. apply senv_preserved.
  simpl; eauto. eauto. auto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
+ (* memcpy *)
  rewrite e1 in TI.
  inv H0. inv H7. inv H8. rename b1 into v1. rename b0 into v2.
  set (adst := aaddr_arg (vanalyze cu f) # pc dst) in *.
  set (asrc := aaddr_arg (vanalyze cu f) # pc src) in *.
  destruct (transfer_builtin_arg All
              (kill_builtin_res res ne,
               nmem_add (nmem_remove nm adst sz) asrc sz) dst)
           as (ne2, nm2) eqn: TR2.
  destruct (transfer_builtin_arg All (ne2, nm2) src) as (ne1, nm1) eqn: TR1.
  InvSoundState.
  exploit transfer_builtin_arg_sound. eexact H4. eauto. eauto. eauto. eauto. eauto.
  intros (tv1 & A1 & B1 & C1 & D1).
  exploit transfer_builtin_arg_sound. eexact H5. eauto. eauto. eauto. eauto. eauto.
  intros (tv2 & A2 & B2 & C2 & D2).
  inv H1.
  exploit magree_loadbytes. 2: eauto. apply magree_push; eauto.
  intros. eapply nlive_add; eauto.
  unfold asrc, vanalyze; rewrite AN; eapply aaddr_arg_sound_1; eauto.
  intros (tbytes & P & Q).
  exploit magree_storebytes_parallel. 2: eauto. apply magree_push.
  eapply magree_monotone. eexact D2.
  instantiate (1 := nlive ge sp0 (nmem_remove nm adst sz)).
  intros. apply incl_nmem_add; auto.
  instantiate (1 := nlive ge sp0 nm).
  intros. eapply nlive_remove; eauto.
  unfold adst, vanalyze; rewrite AN; eapply aaddr_arg_sound_1; eauto.
  erewrite Mem.loadbytes_length in H1 by eauto.
  rewrite nat_of_Z_eq in H1 by omega. auto.
  eauto.
  intros (tm' & A & B).
  edestruct magree_unrecord as (m2' & USB & MAG). apply B. eauto.
    
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  apply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  constructor. eauto. constructor. eauto. constructor.
  eapply external_call_symbols_preserved. apply senv_preserved.
  simpl in B1; inv B1. simpl in B2; inv B2. econstructor; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.

+ (* memcpy eliminated *)
  rewrite e1 in TI.
  inv H0. inv H7. inv H8. rename b1 into v1. rename b0 into v2.
  set (adst := aaddr_arg (vanalyze cu f) # pc dst) in *.
  set (asrc := aaddr_arg (vanalyze cu f) # pc src) in *.
  inv H1.

  edestruct Mem.storebytes_push as (m2 & SB); eauto.
  exploit Mem.push_storebytes_unrecord; eauto. rewrite H2. intro A; inv A.

  econstructor; split.
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  destruct res; auto. apply eagree_set_undef; auto.
  eapply magree_storebytes_left. 2: eauto. eauto. 
  clear H4.
  exploit aaddr_arg_sound; eauto.
  intros (bc & A & B & C).
  intros. eapply nlive_contains; eauto.
  erewrite Mem.loadbytes_length in H0 by eauto.
  rewrite nat_of_Z_eq in H0 by omega. auto.

+ (* annot *)
  destruct (transfer_builtin_args (kill_builtin_res res ne, nm) _x1) as (ne1, nm1) eqn:TR.
  InvSoundState.
  exploit transfer_builtin_args_sound; eauto. intros (tvl & A & B & C & D).
  inv H1.
  rewrite Mem.unrecord_push in H2. inv H2.
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  apply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved. apply senv_preserved.
  constructor. eapply eventval_list_match_lessdef; eauto 2 with na. apply Mem.unrecord_push.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
+ (* annot val *)
  destruct (transfer_builtin_args (kill_builtin_res res ne, nm) _x1) as (ne1, nm1) eqn:TR.
  InvSoundState.
  exploit transfer_builtin_args_sound; eauto. intros (tvl & A & B & C & D).
  inv H1. inv B. inv H7.
  rewrite Mem.unrecord_push in H2; inv H2.
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  apply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved. apply senv_preserved.
  constructor.
  eapply eventval_match_lessdef; eauto 2 with na.
  apply Mem.unrecord_push.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
+ (* debug *)
  inv H1.
  exploit can_eval_builtin_args; eauto. intros (vargs' & A).
  rewrite Mem.unrecord_push in H2; inv H2.
  econstructor; split.
  eapply exec_Ibuiltin; eauto. constructor.
  apply Mem.unrecord_push.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
+ (* all other builtins *)
  assert ((fn_code tf)!pc = Some(Ibuiltin _x _x0 res pc')).
  {
    destruct _x; auto. destruct _x0; auto. destruct _x0; auto. destruct _x0; auto. contradiction.
  }
  clear y TI.
  destruct (transfer_builtin_args (kill_builtin_res res ne, nmem_all) _x0) as (ne1, nm1) eqn:TR.
  InvSoundState.
  exploit transfer_builtin_args_sound; eauto. intros (tvl & A & B & C & D).
  exploit external_call_mem_extends; eauto 2 with na.
  apply Mem.extends_push. eapply magree_extends; eauto. intros. apply nlive_all.
  intros (v' & tm' & P & Q & R & ST).
  exploit Mem.unrecord_stack_block_extends; eauto.
  intros (m2' & USB & EXT).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  apply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved. apply senv_preserved. eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_set_res; auto.
  eapply mextends_agree; eauto.

- (* conditional *)
  TransfInstr; UseTransfer.
  econstructor; split.
  eapply exec_Icond; eauto.
  eapply needs_of_condition_sound. intros; eapply ma_perm; eauto. constructor. eauto. eauto with na.
  eapply match_succ_states; eauto 2 with na.
  simpl; destruct b; auto.

- (* jumptable *)
  TransfInstr; UseTransfer.
  assert (LD: Val.lessdef rs#arg te#arg) by eauto 2 with na.
  rewrite H0 in LD. inv LD.
  econstructor; split.
  eapply exec_Ijumptable; eauto.
  eapply match_succ_states; eauto 2 with na.
  simpl. eapply list_nth_z_in; eauto.

- (* return *)
  TransfInstr; UseTransfer.
  exploit magree_free. eauto. constructor. eauto. instantiate (1 := nlive ge stk nmem_all).
  intros; eapply nlive_dead_stack; eauto.
  intros (tm' & A & B).
  econstructor; split.
  eapply exec_Ireturn; eauto.
  erewrite stacksize_translated by eauto. eexact A.
  constructor; auto.
  destruct or; simpl; eauto 2 with na.
  eapply magree_extends; eauto. apply nlive_all.

- (* internal function *)
  monadInv FUN. generalize EQ. unfold transf_function. fold (vanalyze cu f). intros EQ'.
  destruct (analyze (vanalyze cu f) f) as [an|] eqn:AN; inv EQ'.
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.
  intros (tm' & A & B).
  exploit Mem.record_push_extends_flat_alloc. apply H. apply A. all: eauto.
  + inv SI. auto.
  + repeat rewrite_stack_blocks. apply Z.eq_le_incl. eauto using stack_equiv_fsize, stack_equiv_tail.
  + intros (m2' & USB & EXT).
    econstructor; split.
    econstructor; simpl; eauto.
    simpl. econstructor; eauto.
    apply eagree_init_regs; auto.
    apply mextends_agree; auto.

- (* external function *)
  exploit external_call_mem_extends; eauto.
  intros (res' & tm' & A & B & C & DE).
  simpl in FUN. inv FUN.
  econstructor; split.
  econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.

- (* return *)
  inv STACKS. inv H2.
  exploit Mem.unrecord_stack_block_extends; eauto.
  intros (m2' & USB & EXT).
  econstructor; split.
  constructor. eauto.
  econstructor; eauto. apply mextends_agree; auto.
Qed.

End WITHROMEMFOR.

Local Existing Instance romem_for_wp_instance.

Hypothesis TRANSF: match_prog prog tprog.

Variable fn_stack_requirements: ident -> Z.

Lemma transf_initial_states:
  forall st1, initial_state fn_stack_requirements prog st1 ->
  exists st2, initial_state fn_stack_requirements tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros (cu & tf & A & B & C).
  exists (Callstate nil tf nil (Mem.push_new_stage m2) (fn_stack_requirements (prog_main tprog))); split.
  econstructor; eauto.
  eapply (Genv.init_mem_match TRANSF); eauto.
  replace (prog_main tprog) with (prog_main prog). 
  rewrite symbols_preserved. eauto.
  assumption.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. eapply sig_function_translated; eauto.
  erewrite <- match_program_main; eauto. econstructor; eauto. constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv RES. constructor.
Qed.

(** * Semantic preservation *)

Theorem transf_program_correct:
  forward_simulation (RTL.semantics fn_stack_requirements prog) (RTL.semantics fn_stack_requirements tprog).
Proof.
  intros.
  apply forward_simulation_step with
     (match_states := fun s1 s2 => sound_state prog s1 /\ match_states s1 s2 /\ stack_inv s2 /\ stack_equiv_inv s1 s2).
- apply senv_preserved.
  assumption.
- simpl; intros. exploit transf_initial_states; eauto. intros [st2 [A B]].
  exists st2; intuition. eapply sound_initial; eauto.
  eapply stack_inv_initial; eauto.
  inv H; inv A. red. simpl.
  repeat rewrite_stack_blocks.
  repeat erewrite Genv.init_mem_stack by eauto.
  repeat constructor.
- simpl; intros. destruct H as (? & MS & ?). eapply transf_final_states; eauto.
- simpl; intros. destruct H0 as (SS & MS & SI & SEI).
  assert (sound_state prog s1') by (eapply sound_step; eauto).
  fold ge; fold tge. exploit step_simulation; eauto. intros [st2' [A B]].
  exploit stack_inv_inv. apply A. eauto. intro SI2.
  exploit stack_equiv_inv_step; eauto. intros.
  exists st2'; auto.
Qed.

End PRESERVATION.
