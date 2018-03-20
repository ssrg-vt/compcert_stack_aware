(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Feb 7, 2018 *)
(* ******************* *)

(** Correctness proof for the FlatAsm generation **)

Require Import Coqlib Integers Values Maps AST.
Require Import Memtype Memory.
Require Import Asm RawAsmgen.
Require Import FlatAsm FlatAsmgen.
Require Import Sect.
Require Import Events.
Require Import StackADT.
Require Import Linking Errors.
Require Import Globalenvs FlatAsmGlobenv.
Require Import RawAsmgen.
Require Import AsmFacts.

Ltac monadInvX1 H :=
  let monadInvX H :=  
      monadInvX1 H ||
                 match type of H with
                 | (?F _ _ _ _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 | (?F _ = OK _) =>
                   ((progress simpl in H) || unfold F in H); monadInvX1 H
                 end
  in

  match type of H with
  | (OK _ = OK _) =>
      inversion H; clear H; try subst
  | (Error _ = OK _) =>
      discriminate
  | (bind ?F ?G = OK ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInvX EQ1);
      try (monadInvX1 EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (monadInvX EQ1);
      try (monadInvX1 EQ2)))))
  | (match ?X with left _ => _ | right _ => assertion_failed end = OK _) =>
      destruct X eqn:?; [try (monadInvX1 H) | discriminate]
  | (match (negb ?X) with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [discriminate | try (monadInvX1 H)]
  | (match ?X with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [try (monadInvX1 H) | discriminate]
  | (mmap ?F ?L = OK ?M) =>
      generalize (mmap_inversion F L H); intro
  | (match ?X with Some _ => _ | None => _ end = _) =>
      let EQ := fresh "EQ" in (
      destruct X eqn:EQ; try (monadInvX1 H))
  | (match ?X with pair _ _ => _ end = OK _) =>
      let EQ := fresh "EQ" in (
      destruct X eqn:EQ; try (monadInvX1 H))
  end.

Ltac monadInvX H :=
  monadInvX1 H ||
  match type of H with
  | (?F _ _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  | (?F _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInvX1 H
  end.


Section WITHMEMORYMODEL.
  
Context `{memory_model: Mem.MemoryModel }.
Existing Instance inject_perm_upto_writable.

Definition match_prog (p: Asm.program) (tp: FlatAsm.program) :=
  transf_program p = OK tp.


Section PRESERVATION.

Variable prog: Asm.program.
Variable tprog: FlatAsm.program.
Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := globalenv tprog.

Definition regset_inject (j:meminj) (rs rs' : regset) : Prop :=
  forall r, Val.inject j (rs r) (rs' r).

(** Agreement between a memory injection from Asm to the flat memory and 
    the mappings for sections, global id and labels *)    
Record match_sminj (gm: GID_MAP_TYPE) (lm: LABEL_MAP_TYPE) (mj: meminj) : Type :=
  mk_match_sminj {

      agree_sminj_instr :  forall b b' f ofs ofs' i,
        Genv.find_funct_ptr ge b = Some (Internal f) -> 
        Asm.find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
        mj b = Some (b', ofs') -> 
        exists id i' ofs1, 
          Genv.find_instr tge (Ptrofs.add ofs (Ptrofs.repr ofs')) = Some i' /\
          Genv.find_symbol ge id = Some b /\
          transl_instr gm lm ofs1 id i = OK i';

      agree_sminj_glob : forall id gloc,
          gm id = Some gloc ->
          exists ofs' b, 
            Genv.find_symbol ge id = Some b /\
            get_sect_label_offset0 (Genv.genv_smap tge) gloc = Some ofs' /\
            mj b = Some (mem_block, Ptrofs.unsigned ofs');

      agree_sminj_lbl : forall id b f l z z',
          Genv.find_symbol ge id = Some b ->
          Genv.find_funct_ptr ge b = Some (Internal f) ->
          label_pos l 0 (Asm.fn_code f) = Some z ->
          lm id l = Some z' ->
          Val.inject mj (Vptr b (Ptrofs.repr z)) (get_sect_label_addr0 (Genv.genv_smap tge) (code_label z'));
      
    }.

Definition gid_map_for_undef_syms (gm: GID_MAP_TYPE) :=
  forall id, Genv.find_symbol ge id = None -> gm id = None.

Definition globs_inj_into_flatmem (mj:meminj) := 
  forall b g b' ofs',
    Genv.find_def ge b = Some g -> 
    mj b = Some (b', ofs') -> b' = mem_block.

Definition funs_inj_into_flatmem (mj:meminj) := 
  forall b f b' ofs',
    Genv.find_funct_ptr ge b = Some f -> 
    mj b = Some (b', ofs') -> b' = mem_block.

Lemma globs_to_funs_inj_into_flatmem : forall (j:meminj),
    globs_inj_into_flatmem j -> funs_inj_into_flatmem j.
Proof.
  unfold globs_inj_into_flatmem, funs_inj_into_flatmem. 
  unfold Genv.find_funct_ptr. intros.
  destruct (Genv.find_def ge b) eqn: FDEF; try congruence.
  destruct g; try congruence. 
  inv H0. eapply H; eauto.
Qed.


Definition valid_instr_offset_is_internal (mj:meminj) :=
  forall b f ofs i ofs',
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    mj b = Some (mem_block, ofs') ->
    Genv.genv_is_instr_internal tge (Ptrofs.add ofs (Ptrofs.repr ofs')) = true.    

Definition extfun_entry_is_external (mj:meminj) :=
  forall b b' f ofs,
    Genv.find_funct_ptr ge b = Some (External f) ->
    mj b = Some (b', ofs) ->
    Genv.genv_is_instr_internal tge (Ptrofs.repr ofs) = false.


Definition def_frame_inj m := (fun n => if lt_dec n (length (Mem.stack_adt m)) then Some O else None).


Lemma store_pres_def_frame_inj : forall chunk m1 b ofs v m1',
    Mem.store chunk m1 b ofs v = Some m1' -> 
    forall n, def_frame_inj m1 n = def_frame_inj m1' n.
Proof.
  unfold def_frame_inj. intros.
  exploit Mem.store_stack_blocks; eauto. intros. rewrite H0.
  auto.
Qed.

Lemma store_mapped_inject' : 
  forall (f : meminj) (chunk : memory_chunk) 
    (m1 : mem) (b1 : block) (ofs : Z) (v1 : val) 
    (n1 m2 : mem) (b2 : block) (delta : Z) (v2 : val),
    Mem.inject f (def_frame_inj m1) m1 m2 ->
    Mem.store chunk m1 b1 ofs v1 = Some n1 ->
    f b1 = Some (b2, delta) ->
    Val.inject f v1 v2 ->
    exists n2 : mem,
      Mem.store chunk m2 b2 (ofs + delta) v2 = Some n2 /\
      Mem.inject f (def_frame_inj n1) n1 n2.
Proof.
  intros. exploit Mem.store_mapped_inject; eauto. 
  intros (n2 & STORE & MINJ).
  exploit (Mem.mem_inject_ext f (def_frame_inj m1) (def_frame_inj n1)); eauto.
  eapply store_pres_def_frame_inj; eauto.
Qed.


Lemma storev_pres_def_frame_inj : forall chunk m1 a r m1',
    Mem.storev chunk m1 a r = Some m1' -> 
    forall n, def_frame_inj m1 n = def_frame_inj m1' n.
Proof.
  unfold Mem.storev. intros.
  destruct a in H; try congruence.
  eapply store_pres_def_frame_inj; eauto.
Qed.
  

Definition match_find_funct (j:meminj) :=
  forall b f ofs,
  Genv.find_funct_ptr ge b = Some (External f) ->
  j b = Some (mem_block, ofs) ->
  Genv.find_funct_offset tge (Ptrofs.repr ofs) = Some (External f).

Definition glob_block_valid (m:mem) := 
  forall b g, Genv.find_def ge b = Some g -> Mem.valid_block m b.

Definition stack_block_inject (j:meminj) : Prop :=
  j (Genv.genv_next ge) = Some (mem_block, 0).

Inductive match_states: Asm.state -> FlatAsm.state -> Prop :=
| match_states_intro: forall (j:meminj) (rs: regset) (m: mem) (rs': regset) (m':mem)
                        (gm: GID_MAP_TYPE) (lm: LABEL_MAP_TYPE)
                        (MINJ: Mem.inject j (def_frame_inj m) m m')
                        (MATCHSMINJ: match_sminj gm lm j)
                        (GINJFLATMEM: globs_inj_into_flatmem j)
                        (INSTRINTERNAL: valid_instr_offset_is_internal j)
                        (EXTEXTERNAL: extfun_entry_is_external j)
                        (MATCHFINDFUNCT: match_find_funct j)
                        (RSINJ: regset_inject j rs rs')
                        (GBVALID: glob_block_valid m)
                        (GMUNDEF: gid_map_for_undef_syms gm)
                        (SBINJ:stack_block_inject j),
    match_states (State rs m) (State rs' m').


Context `{external_calls_ops : !ExternalCallsOps mem }.
Context `{!EnableBuiltins mem}.
Existing Instance Asm.mem_accessors_default.
Existing Instance FlatAsm.mem_accessors_default.

Lemma eval_builtin_arg_inject : forall gm lm j m m' rs rs' sp sp' arg varg arg',
    match_sminj gm lm j ->
    gid_map_for_undef_syms gm ->
    Mem.inject j (def_frame_inj m) m m' ->
    regset_inject j rs rs' ->
    Val.inject j sp sp' ->
    transl_builtin_arg gm arg = OK arg' ->
    eval_builtin_arg ge rs sp m arg varg ->
    exists varg', FlatAsmBuiltin.eval_builtin_arg _ _ preg tge rs' sp' m' arg' varg' /\
             Val.inject j varg varg'.
Proof.
  unfold regset_inject. 
  induction arg; intros; inv H5;
    try (eexists; split; auto; monadInv H4; constructor).
  - monadInv H4. exploit Mem.loadv_inject; eauto.
    eapply Val.offset_ptr_inject; eauto.
    intros (v2 & MVLOAD & LINJ).
    eexists; split; eauto.
    constructor; auto.
  - monadInv H4. 
    exists (Val.offset_ptr sp' ofs). split; try (eapply Val.offset_ptr_inject; eauto).
    constructor.
  - monadInvX H4. unfold Senv.symbol_address in H10.
    destruct (Senv.find_symbol ge id) eqn:FINDSYM.
    + inv H. exploit agree_sminj_glob0; eauto. 
      intros (ofs' & b0 & FSYM & GLOFS & JB).
      unfold Senv.find_symbol in FINDSYM. simpl in FINDSYM. rewrite FSYM in FINDSYM; inv FINDSYM.
      exploit Mem.loadv_inject; eauto.
      intros (varg' & LOADV & VARGINJ).
      exists varg'. split; auto.
      apply FlatAsmBuiltin.eval_BA_loadglobal with (Ptrofs.add ofs ofs').
      * exploit get_sect_label_offset0_offset; eauto.
      * rewrite Ptrofs.repr_unsigned in *. auto.
    + simpl in H10. congruence.
  - monadInvX H4. unfold Senv.symbol_address.
    destruct (Senv.find_symbol ge id) eqn:FINDSYM.
    + inv H. exploit agree_sminj_glob0; eauto. 
      intros (ofs' & b0 & FSYM & GLOFS & JB).
      unfold Senv.find_symbol in FINDSYM. simpl in FINDSYM. rewrite FSYM in FINDSYM; inv FINDSYM.
      exists (flatptr (Ptrofs.add ofs ofs')). split; auto.
      apply FlatAsmBuiltin.eval_BA_addrglobal.
      * exploit get_sect_label_offset0_offset; eauto.
      * unfold flatptr. eapply Val.inject_ptr; eauto.
        rewrite Ptrofs.repr_unsigned. auto.
    + unfold Senv.find_symbol in FINDSYM. simpl in FINDSYM.
      unfold gid_map_for_undef_syms in *. exploit H0; eauto.
      congruence.
  - monadInv H4.
    exploit IHarg1; eauto. intros (vhi' & EVAL1 & VINJ1).
    exploit IHarg2; eauto. intros (vlo' & EVAL2 & VINJ2).
    exists (Val.longofwords vhi' vlo'); split.
    + constructor; auto.
    + apply Val.longofwords_inject; eauto.
Qed.

Lemma eval_builtin_args_inject : forall gm lm j m m' rs rs' sp sp' args vargs args',
    match_sminj gm lm j ->
    gid_map_for_undef_syms gm ->
    Mem.inject j (def_frame_inj m) m m' ->
    regset_inject j rs rs' ->
    Val.inject j sp sp' ->
    transl_builtin_args gm args = OK args' ->
    eval_builtin_args ge rs sp m args vargs ->
    exists vargs', FlatAsmBuiltin.eval_builtin_args _ _ preg tge rs' sp' m' args' vargs' /\
             Val.inject_list j vargs vargs'.
Proof.
  induction args; intros; simpl. 
  - inv H4. inv H5. exists nil. split; auto.
    unfold FlatAsmBuiltin.eval_builtin_args. apply list_forall2_nil.
  - monadInv H4. inv H5.
    exploit eval_builtin_arg_inject; eauto. 
    intros (varg' & EVARG & VINJ).
    exploit IHargs; eauto. 
    intros (vargs' & EVARGS & VSINJ).
    exists (varg' :: vargs'). split; auto.
    unfold FlatAsmBuiltin.eval_builtin_args. 
    apply list_forall2_cons; auto.
Qed.

Lemma extcall_arg_inject : forall rs1 rs2 m1 m2 l arg1 j,
    extcall_arg rs1 m1 l arg1 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists arg2,
      Val.inject j arg1 arg2 /\
      extcall_arg rs2 m2 l arg2.
Proof.
  intros. inv H.
  - unfold regset_inject in *.
    specialize (H1 (Asm.preg_of r)). eexists; split; eauto.
    constructor.
  - exploit Mem.loadv_inject; eauto.
    apply Val.offset_ptr_inject. apply H1.
    intros (arg2 & MLOADV & ARGINJ).
    exists arg2. split; auto.
    eapply extcall_arg_stack; eauto.
Qed.

Lemma extcall_arg_pair_inject : forall rs1 rs2 m1 m2 lp arg1 j,
    extcall_arg_pair rs1 m1 lp arg1 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists arg2,
      Val.inject j arg1 arg2 /\
      extcall_arg_pair rs2 m2 lp arg2.
Proof.
  intros. inv H.
  - exploit extcall_arg_inject; eauto. 
    intros (arg2 & VINJ & EXTCALL).
    exists arg2. split; auto. constructor. auto.
  - exploit (extcall_arg_inject rs1 rs2 m1 m2 hi vhi); eauto. 
    intros (arghi & VINJHI & EXTCALLHI).
    exploit (extcall_arg_inject rs1 rs2 m1 m2 lo vlo); eauto. 
    intros (arglo & VINJLO & EXTCALLLO).
    exists (Val.longofwords arghi arglo). split.
    + apply Val.longofwords_inject; auto.
    + constructor; auto.
Qed.

Lemma extcall_arguments_inject_aux : forall rs1 rs2 m1 m2 locs args1 j,
   list_forall2 (extcall_arg_pair rs1 m1) locs args1 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists args2,
      Val.inject_list j args1 args2 /\
      list_forall2 (extcall_arg_pair rs2 m2) locs args2.
Proof.
  induction locs; simpl; intros; inv H.
  - exists nil. split.
    + apply Val.inject_list_nil.
    + unfold Asm.extcall_arguments. apply list_forall2_nil.
  - exploit extcall_arg_pair_inject; eauto.
    intros (arg2 & VINJARG2 & EXTCALLARG2).
    exploit IHlocs; eauto.
    intros (args2 & VINJARGS2 & EXTCALLARGS2).
    exists (arg2 :: args2). split; auto.
    apply list_forall2_cons; auto.
Qed.

Lemma extcall_arguments_inject : forall rs1 rs2 m1 m2 ef args1 j,
    Asm.extcall_arguments rs1 m1 (ef_sig ef) args1 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    regset_inject j rs1 rs2 ->
    exists args2,
      Val.inject_list j args1 args2 /\
      Asm.extcall_arguments rs2 m2 (ef_sig ef) args2.
Proof.
  unfold Asm.extcall_arguments. intros.
  eapply extcall_arguments_inject_aux; eauto.
Qed.

Axiom external_call_inject : forall j vargs1 vargs2 m1 m2 m1' vres1 t ef,
    Val.inject_list j vargs1 vargs2 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    external_call ef ge vargs1 m1 t vres1 m1' ->
    exists j' vres2 m2',
      external_call ef dummy_senv vargs2 m2 t vres2 m2' /\ 
      Val.inject j' vres1 vres2 /\ Mem.inject j' (def_frame_inj m1') m1' m2' /\
      inject_incr j j' /\
      inject_separated j j' m1 m2.

Axiom  external_call_valid_block: forall ef ge vargs m1 t vres m2 b,
    external_call ef ge vargs m1 t vres m2 -> Mem.valid_block m1 b -> Mem.valid_block m2 b.

Lemma extcall_pres_glob_block_valid : forall ef ge vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 -> glob_block_valid m1 -> glob_block_valid m2.
Proof.
  unfold glob_block_valid in *. intros.
  eapply external_call_valid_block; eauto.
Qed.

Lemma regset_inject_incr : forall j j' rs rs',
    regset_inject j rs rs' ->
    inject_incr j j' ->
    regset_inject j' rs rs'.
Proof.
  unfold inject_incr, regset_inject. intros.
  specialize (H r).
  destruct (rs r); inversion H; subst; auto.
  eapply Val.inject_ptr. apply H0. eauto. auto.
Qed.

Lemma undef_regs_pres_inject : forall j rs rs' regs,
  regset_inject j rs rs' ->
  regset_inject j (Asm.undef_regs regs rs) (Asm.undef_regs regs rs').
Proof.
  unfold regset_inject. intros. apply val_inject_undef_regs.
  auto.
Qed.    
  
Lemma Pregmap_gsspec_alt : forall (A : Type) (i j : Pregmap.elt) (x : A) (m : Pregmap.t A),
    (m # j <- x) i  = (if Pregmap.elt_eq i j then x else m i).
Proof.
  intros. apply Pregmap.gsspec.
Qed.

Lemma regset_inject_expand : forall j rs1 rs2 v1 v2 r,
  regset_inject j rs1 rs2 ->
  Val.inject j v1 v2 ->
  regset_inject j (rs1 # r <- v1) (rs2 # r <- v2).
Proof.
  intros. unfold regset_inject. intros.
  repeat rewrite Pregmap_gsspec_alt. 
  destruct (Pregmap.elt_eq r0 r); auto.
Qed.

Lemma regset_inject_expand_vundef_left : forall j rs1 rs2 r,
  regset_inject j rs1 rs2 ->
  regset_inject j (rs1 # r <- Vundef) rs2.
Proof.
  intros. unfold regset_inject. intros.
  rewrite Pregmap_gsspec_alt. destruct (Pregmap.elt_eq r0 r); auto.
Qed.

Lemma set_res_pres_inject : forall res j rs1 rs2,
    regset_inject j rs1 rs2 ->
    forall vres1 vres2,
    Val.inject j vres1 vres2 ->
    regset_inject j (set_res res vres1 rs1) (set_res res vres2 rs2).
Proof.
  induction res; auto; simpl; unfold regset_inject; intros.
  - rewrite Pregmap_gsspec_alt. destruct (Pregmap.elt_eq r x); subst.
    + rewrite Pregmap.gss. auto.
    + rewrite Pregmap.gso; auto.
  - exploit (Val.hiword_inject j vres1 vres2); eauto. intros. 
    exploit (Val.loword_inject j vres1 vres2); eauto. intros.
    apply IHres2; auto.
Qed.


Lemma nextinstr_pres_inject : forall j rs1 rs2 sz,
    regset_inject j rs1 rs2 ->
    regset_inject j (Asm.nextinstr rs1 sz) (FlatAsm.nextinstr rs2 sz).
Proof.
  unfold nextinstr. intros. apply regset_inject_expand; auto.
  apply Val.offset_ptr_inject. auto.
Qed.  

Lemma nextinstr_nf_pres_inject : forall j rs1 rs2 sz,
    regset_inject j rs1 rs2 ->
    regset_inject j (Asm.nextinstr_nf rs1 sz) (FlatAsm.nextinstr_nf rs2 sz).
Proof.
  intros. apply nextinstr_pres_inject.
  apply undef_regs_pres_inject. auto.
Qed. 


Lemma set_pair_pres_inject : forall j rs1 rs2 v1 v2 loc,
    regset_inject j rs1 rs2 ->
    Val.inject j v1 v2 ->
    regset_inject j (set_pair loc v1 rs1) (set_pair loc v2 rs2).
Proof.
  intros. unfold set_pair, Asm.set_pair. destruct loc; simpl.
  - apply regset_inject_expand; auto.
  - apply regset_inject_expand; auto.
    apply regset_inject_expand; auto.
    apply Val.hiword_inject; auto.
    apply Val.loword_inject; auto.
Qed.

Lemma vinject_pres_not_vundef : forall j v1 v2,
  Val.inject j v1 v2 -> v1 <> Vundef -> v2 <> Vundef.
Proof.
  intros. destruct v1; inversion H; subst; auto.
  congruence.
Qed.

Lemma vinject_pres_has_type : forall j v1 v2 t,
    Val.inject j v1 v2 -> v1 <> Vundef ->
    Val.has_type v1 t -> Val.has_type v2 t.
Proof.
  intros. destruct v1; inversion H; subst; simpl in H; auto. 
  congruence.
Qed.

Lemma inject_decr : forall b j j' m1 m2 b' ofs,
  Mem.valid_block m1 b -> inject_incr j j' -> inject_separated j j' m1 m2 ->
  j' b = Some (b', ofs) -> j b = Some (b', ofs).
Proof.
  intros. destruct (j b) eqn:JB.
  - unfold inject_incr in *. destruct p. exploit H0; eauto.
    intros. congruence.
  - unfold inject_separated in *. exploit H1; eauto.
    intros (NVALID1 & NVALID2). congruence.
Qed.

Lemma inject_pres_match_sminj : 
  forall j j' m1 m2 gm lm (ms: match_sminj gm lm j), 
    glob_block_valid m1 -> inject_incr j j' -> inject_separated j j' m1 m2 -> 
    match_sminj gm lm j'.
Proof.
  unfold glob_block_valid.
  intros. inversion ms. constructor; intros.
  - 
    eapply agree_sminj_instr0; eauto.
    instantiate (1:=b').
    unfold Genv.find_funct_ptr in H2. destruct (Genv.find_def ge b) eqn:FDEF; try congruence.
    exploit H; eauto. intros.
    eapply inject_decr; eauto.
  - 
    exploit agree_sminj_glob0; eauto. 
    intros (ofs' & b0 & FSYM & GLBL & JB).
    eexists; eauto.
  - 
    exploit agree_sminj_lbl0; eauto.
Qed.

Lemma inject_pres_globs_inj_into_flatmem : forall j j' m1 m2,
    glob_block_valid m1 -> inject_incr j j' -> inject_separated j j' m1 m2 -> 
    globs_inj_into_flatmem j -> globs_inj_into_flatmem j'.
Proof.
  unfold globs_inj_into_flatmem, glob_block_valid. intros.
  exploit H; eauto. intros.
  assert (j b = Some (b', ofs')) by (eapply inject_decr; eauto).
  eapply H2; eauto.
Qed.

Lemma inject_pres_valid_instr_offset_is_internal : forall j j' m1 m2,
    glob_block_valid m1 -> inject_incr j j' -> inject_separated j j' m1 m2 -> 
    valid_instr_offset_is_internal j -> valid_instr_offset_is_internal j'.
Proof.
  unfold glob_block_valid.
  unfold valid_instr_offset_is_internal. intros.
  eapply H2; eauto.
  unfold Genv.find_funct_ptr in H3. destruct (Genv.find_def ge b) eqn:FDEF; try congruence.
  exploit H; eauto. intros.
  eapply inject_decr; eauto.
Qed.

Lemma inject_pres_extfun_entry_is_external : forall j j' m1 m2,
    glob_block_valid m1 -> inject_incr j j' -> inject_separated j j' m1 m2 -> 
    extfun_entry_is_external j -> extfun_entry_is_external j'.
Proof.
  unfold glob_block_valid.
  unfold extfun_entry_is_external. intros.
  eapply H2; eauto.
  instantiate (1:=b').
  unfold Genv.find_funct_ptr in H3. destruct (Genv.find_def ge b) eqn:FDEF; try congruence.
  exploit H; eauto. intros.
  eapply inject_decr; eauto.
Qed.

Lemma inject_pres_match_find_funct : forall j j' m1 m2,
    glob_block_valid m1 -> inject_incr j j' -> inject_separated j j' m1 m2 -> 
    match_find_funct j -> match_find_funct j'.
Proof.
  unfold glob_block_valid, match_find_funct. intros.
  eapply H2; eauto.
  unfold Genv.find_funct_ptr in H3. destruct (Genv.find_def ge b) eqn:FDEF; try congruence.
  exploit H; eauto. intros.
  eapply inject_decr; eauto.
Qed.  

Remark mul_inject:
  forall f v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mul v1 v2) (Val.mul v1' v2').
Proof.
  intros. unfold Val.mul. destruct v1, v2; simpl; auto.
  inversion H; inversion H0; subst. auto.
Qed.

Remark mull_inject:
  forall f v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mull v1 v2) (Val.mull v1' v2').
Proof.
Proof.
  intros. unfold Val.mull. destruct v1, v2; simpl; auto.
  inversion H; inversion H0; subst. auto.
Qed.

Remark mulhs_inject:
  forall f v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mulhs v1 v2) (Val.mulhs v1' v2').
Proof.
  intros. unfold Val.mulhs. destruct v1, v2; simpl; auto.
  inversion H; inversion H0; subst. auto.
Qed.


Lemma inject_symbol_sectlabel : forall gm lm j id lbl ofs,
    match_sminj gm lm j ->
    gm id = Some lbl ->
    Val.inject j (Genv.symbol_address ge id ofs) (Genv.get_label_addr tge lbl ofs).
Proof.
  unfold Genv.symbol_address, Genv.get_label_addr.
  unfold get_sect_label_addr. intros.
  destruct (Genv.find_symbol ge id) eqn:FINDSYM; auto.
  inv H. exploit agree_sminj_glob0; eauto.
  intros (ofs' & b0 & FSYM & SBOFS & JB).
  rewrite FSYM in FINDSYM; inv FINDSYM.
  unfold get_sect_label_addr0. rewrite SBOFS.
  unfold flatptr; simpl. 
  eapply Val.inject_ptr. eauto.
  rewrite Ptrofs.repr_unsigned. apply Ptrofs.add_commut.
Qed.

Lemma add_undef : forall v,
  Val.add v Vundef = Vundef.
Proof.
  intros; destruct v; simpl; auto.
Qed.

Lemma addl_undef : forall v,
  Val.addl v Vundef = Vundef.
Proof.
  intros; destruct v; simpl; auto.
Qed.

Ltac simpl_goal :=
  repeat match goal with
         | [ |- context [ Int.add Int.zero _ ] ] =>
           rewrite Int.add_zero_l
         | [ |- context [ Int64.add Int64.zero _ ] ] =>
           rewrite Int64.add_zero_l
         | [ |- context [Ptrofs.add _ (Ptrofs.of_int Int.zero)] ] =>
           rewrite Ptrofs.add_zero
         | [ |- context [Ptrofs.add _ (Ptrofs.of_int64 Int64.zero)] ] =>
           rewrite Ptrofs.add_zero
         | [ |- context [Ptrofs.add Ptrofs.zero _] ] =>
           rewrite Ptrofs.add_zero_l
         | [ |- context [Ptrofs.repr (Ptrofs.unsigned _)] ] =>
           rewrite Ptrofs.repr_unsigned
         end.

Ltac solve_symb_inj :=
  match goal with
  | [  H1 : Genv.symbol_address _ _ _ = _,
       H2 : Genv.get_label_addr _ _ _ = _ |- _ ] =>
    exploit inject_symbol_sectlabel; eauto;
    rewrite H1, H2; auto
  end.

Ltac destr_pair_if :=
  repeat match goal with
         | [ |- context [match ?a with pair _ _ => _ end] ] =>
           destruct a eqn:?
         | [ |- context [if ?h then _ else _] ] =>
           destruct h eqn:?
         end.

Ltac inject_match :=
  match goal with
  | [ |- Val.inject ?j (match ?a with _ => _ end) (match ?b with _ => _ end) ] =>
    assert (Val.inject j a b)
  end.

Ltac inv_valinj :=
  match goal with
         | [ H : Val.inject _ (Vint _) _ |- _ ] =>
           inversion H; subst
         | [ H : Val.inject _ (Vlong _) _ |- _ ] =>
           inversion H; subst
         | [ H : Val.inject _ (Vptr _ _) _ |- _ ] =>
           inversion H; subst
         end.

Ltac destr_valinj_right H :=
  match type of H with
  | Val.inject _ _ ?a =>
    destruct a eqn:?
  end.

Ltac destr_valinj_left H :=
  match type of H with
  | Val.inject _ ?a ?b =>
    destruct a eqn:?
  end.

Lemma eval_addrmode32_inject: forall gm lm j a1 a2 rs1 rs2,
    match_sminj gm lm j ->
    regset_inject j rs1 rs2 ->
    transl_addr_mode gm a1 = OK a2 ->
    Val.inject j (Asm.eval_addrmode32 ge a1 rs1) (FlatAsm.eval_addrmode32 tge a2 rs2).
Proof.
  intros. unfold Asm.eval_addrmode32, FlatAsm.eval_addrmode32.
  destruct a1, a2. destruct base, ofs, const; simpl in *; monadInvX H1; simpl; simpl_goal;
  try apply Val.add_inject; auto.
  - apply Val.add_inject; auto. destr_pair_if; repeat apply Val.add_inject; auto.
    apply mul_inject; auto.
  - destr_pair_if; 
      try (repeat apply Val.add_inject; auto);
      try (eapply inject_symbol_sectlabel; eauto).
    apply mul_inject; auto.
  - destruct (Genv.symbol_address ge i0 i1) eqn:SYMADDR; auto.
    simpl_goal.
    exploit inject_symbol_sectlabel; eauto.
    rewrite SYMADDR. intros. inv H1.
    simpl_goal; auto.
  - destr_pair_if.
    + inject_match.
      apply Val.add_inject; auto.
      destruct (Val.add (rs1 i) (Vint (Int.repr z))); auto.
      inv_valinj. simpl_goal. congruence.
    + inject_match. apply Val.add_inject; auto.
      destruct (Val.add (rs1 i) (Vint (Int.repr z))); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. repeat apply Val.add_inject; auto.
      apply mul_inject; auto.
      destruct (Val.add (Val.mul (rs1 i) (Vint (Int.repr z0))) (Vint (Int.repr z))); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. repeat apply Val.add_inject; auto.
      apply mul_inject; auto.
      destruct (Val.add (Val.mul (rs1 i) (Vint (Int.repr z0))) (Vint (Int.repr z))); auto;
      inv_valinj; simpl_goal; congruence.
  - destr_pair_if. 
    + inject_match.
      apply Val.add_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.add (rs1 i1) (Genv.symbol_address ge i i0)); auto.
      inv_valinj. simpl_goal. congruence.
    + inject_match. apply Val.add_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.add (rs1 i1) (Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. repeat apply Val.add_inject; auto.
      apply mul_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.add (Val.mul (rs1 i1) (Vint (Int.repr z))) (Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. repeat apply Val.add_inject; auto.
      apply mul_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.add (Val.mul (rs1 i1) (Vint (Int.repr z))) (Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
  - inject_match. 
    inject_match. eapply inject_symbol_sectlabel; eauto.
    destruct (Genv.symbol_address ge i i0) eqn:EQ; auto.
    inv_valinj. simpl_goal. auto.
    destr_valinj_left H1; auto. inv_valinj. auto.
Qed.

Lemma eval_addrmode64_inject: forall gm lm j a1 a2 rs1 rs2,
    match_sminj gm lm j ->
    regset_inject j rs1 rs2 ->
    transl_addr_mode gm a1 = OK a2 ->
    Val.inject j (Asm.eval_addrmode64 ge a1 rs1) (FlatAsm.eval_addrmode64 tge a2 rs2).
Proof.
  intros. unfold Asm.eval_addrmode64, FlatAsm.eval_addrmode64.
  destruct a1, a2. destruct base, ofs, const; simpl in *; monadInvX H1; simpl; simpl_goal;
  try apply Val.add_inject; auto.
  - destr_pair_if.
    + repeat apply Val.addl_inject; auto.
    + repeat apply Val.addl_inject; auto.
      apply mull_inject; auto.
  - destr_pair_if.
    + repeat apply Val.addl_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
    + repeat apply Val.addl_inject; auto.
      apply mull_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
  - simpl_goal. apply Val.addl_inject; auto.
  - apply Val.addl_inject; auto.
    inject_match.
    eapply inject_symbol_sectlabel; eauto.
    destruct (Genv.symbol_address ge i0 i1); auto.
    inv_valinj. auto.
    destruct Archi.ptr64; auto.
    inv_valinj. simpl_goal. congruence.
  - destr_pair_if. 
    + inject_match.
      apply Val.addl_inject; auto.
      destruct (Val.addl (rs1 i) (Vlong (Int64.repr z))); simpl_goal; auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. apply Val.addl_inject; auto.
      destruct (Val.addl (rs1 i) (Vlong (Int64.repr z))); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. repeat apply Val.addl_inject; auto.
      apply mull_inject; auto.
      destruct (Val.addl (Val.mull (rs1 i) (Vlong (Int64.repr z0))) (Vlong (Int64.repr z))); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. repeat apply Val.addl_inject; auto.
      apply mull_inject; auto.
      destruct (Val.addl (Val.mull (rs1 i) (Vlong (Int64.repr z0))) (Vlong (Int64.repr z))); auto;
      inv_valinj; simpl_goal; congruence.
  - destr_pair_if. 
    + inject_match.
      apply Val.addl_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.addl (rs1 i1) (Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. apply Val.addl_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.addl (rs1 i1) (Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. repeat apply Val.addl_inject; auto.
      apply mull_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.addl (Val.mull (rs1 i1) (Vlong (Int64.repr z))) (Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. repeat apply Val.addl_inject; auto.
      apply mull_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.addl (Val.mull (rs1 i1) (Vlong (Int64.repr z))) (Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
  - inject_match. 
    inject_match. eapply inject_symbol_sectlabel; eauto.
    destruct (Genv.symbol_address ge i i0) eqn:EQ; auto.
    inv_valinj. simpl_goal. auto.
    inv_valinj. destruct Archi.ptr64.
    simpl_goal. congruence. auto.
    destr_valinj_left H1; auto. inv_valinj. auto. 
    destruct Archi.ptr64 eqn:ARCHI; auto; simpl_goal.
    inv_valinj. simpl_goal. congruence.
Qed.

Lemma eval_addrmode_inject: forall gm lm j a1 a2 rs1 rs2,
    match_sminj gm lm j ->
    regset_inject j rs1 rs2 ->
    transl_addr_mode gm a1 = OK a2 ->
    Val.inject j (Asm.eval_addrmode ge a1 rs1) (FlatAsm.eval_addrmode tge a2 rs2).
Proof.
  intros. unfold Asm.eval_addrmode, eval_addrmode. destruct Archi.ptr64.
  + eapply eval_addrmode64_inject; eauto.
  + eapply eval_addrmode32_inject; eauto.
Qed.

Lemma exec_load_step: forall j rs1 rs2 m1 m2 rs1' m1' gm lm sz chunk rd a1 a2
                          (MINJ: Mem.inject j (def_frame_inj m1) m1 m2)
                          (MATCHSMINJ: match_sminj gm lm j)
                          (GINJFLATMEM: globs_inj_into_flatmem j)
                          (INSTRINTERNAL: valid_instr_offset_is_internal j)
                          (EXTEXTERNAL: extfun_entry_is_external j)
                          (MATCHFINDFUNCT: match_find_funct j)
                          (RSINJ: regset_inject j rs1 rs2)
                          (GBVALID: glob_block_valid m1)
                          (GMUNDEF: gid_map_for_undef_syms gm)
                          (SBINJ:stack_block_inject j),
    Asm.exec_load ge chunk m1 a1 rs1 rd sz = Next rs1' m1' ->
    transl_addr_mode gm a1 = OK a2 ->
    exists rs2' m2',
      FlatAsm.exec_load tge chunk m2 a2 rs2 rd sz = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. unfold Asm.exec_load in *.  
  exploit eval_addrmode_inject; eauto. intro EMODINJ. unfold Next in H.
  destruct (Mem.loadv chunk m1 (Asm.eval_addrmode ge a1 rs1)) eqn:MLOAD; try congruence.
  exploit Mem.loadv_inject; eauto. intros (v2 & MLOADV & VINJ).
  eexists. eexists. split.
  - unfold exec_load. rewrite MLOADV. auto.
  - inv H. eapply match_states_intro; eauto.
    apply nextinstr_pres_inject. apply undef_regs_pres_inject.
    apply regset_inject_expand; eauto.
Qed.

Lemma store_pres_glob_block_valid : forall m1 chunk b v ofs m2,
  Mem.store chunk m1 b ofs v = Some m2 -> glob_block_valid m1 -> glob_block_valid m2.
Proof.
  unfold glob_block_valid in *. intros.
  eapply Mem.store_valid_block_1; eauto.
Qed.

Lemma storev_pres_glob_block_valid : forall m1 chunk ptr v m2,
  Mem.storev chunk m1 ptr v = Some m2 -> glob_block_valid m1 -> glob_block_valid m2.
Proof.
  unfold Mem.storev. intros. destruct ptr; try congruence.
  eapply store_pres_glob_block_valid; eauto.
Qed.

Lemma exec_store_step: forall j rs1 rs2 m1 m2 rs1' m1' gm lm sz chunk r a1 a2 dregs
                         (MINJ: Mem.inject j (def_frame_inj m1) m1 m2)
                         (MATCHSMINJ: match_sminj gm lm j)
                         (GINJFLATMEM: globs_inj_into_flatmem j)
                         (INSTRINTERNAL: valid_instr_offset_is_internal j)
                         (EXTEXTERNAL: extfun_entry_is_external j)
                         (MATCHFINDFUNCT: match_find_funct j)
                         (RSINJ: regset_inject j rs1 rs2)
                         (GBVALID: glob_block_valid m1)
                         (GMUNDEF: gid_map_for_undef_syms gm)
                         (SBINJ:stack_block_inject j),
    Asm.exec_store ge chunk m1 a1 rs1 r dregs sz = Next rs1' m1' ->
    transl_addr_mode gm a1 = OK a2 ->
    exists rs2' m2',
      FlatAsm.exec_store tge chunk m2 a2 rs2 r dregs sz = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. unfold Asm.exec_store in *.  
  exploit eval_addrmode_inject; eauto. intro EMODINJ. unfold Next in H.
  destruct (Mem.storev chunk m1 (Asm.eval_addrmode ge a1 rs1) (rs1 r)) eqn:MSTORE; try congruence.
  exploit Mem.storev_mapped_inject; eauto. intros (m2' & MSTOREV & MINJ').
  eexists. eexists. split.
  - unfold exec_store. rewrite MSTOREV. auto.
  - inv H. eapply match_states_intro; eauto.
    eapply Mem.mem_inject_ext; eauto.
    eapply storev_pres_def_frame_inj; eauto.
    apply nextinstr_pres_inject. repeat apply undef_regs_pres_inject. auto.
    eapply storev_pres_glob_block_valid; eauto.
Qed.

Inductive opt_val_inject (j:meminj) : option val -> option val -> Prop :=
| opt_val_inject_none v : opt_val_inject j None v
| opt_val_inject_some v1 v2 : Val.inject j v1 v2 -> 
                                opt_val_inject j (Some v1) (Some v2).

Lemma maketotal_inject : forall v1 v2 j,
    opt_val_inject j v1 v2 -> Val.inject j (Val.maketotal v1) (Val.maketotal v2).
Proof.
  intros. inversion H; simpl; subst; auto.
Qed.

Inductive opt_lessdef {A:Type} : option A -> option A -> Prop :=
| opt_lessdef_none v : opt_lessdef None v
| opt_lessdef_some v : opt_lessdef (Some v) (Some v). 

Lemma vzero_inject : forall j,
  Val.inject j Vzero Vzero.
Proof.
  intros. unfold Vzero. auto.
Qed.

Lemma vtrue_inject : forall j,
  Val.inject j Vtrue Vtrue.
Proof.
  intros. unfold Vtrue. auto.
Qed.

Lemma vfalse_inject : forall j,
  Val.inject j Vfalse Vfalse.
Proof.
  intros. unfold Vfalse. auto.
Qed.

Lemma vofbool_inject : forall j v,
  Val.inject j (Val.of_bool v) (Val.of_bool v).
Proof.
  destruct v; simpl.
  - apply vtrue_inject.
  - apply vfalse_inject.
Qed.
  
Lemma neg_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.neg v1) (Val.neg v2).
Proof.
  intros. unfold Val.neg. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma negl_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.negl v1) (Val.negl v2).
Proof.
  intros. unfold Val.negl. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma mullhs_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.mullhs v1 v1') (Val.mullhs v2 v2').
Proof.
  intros. unfold Val.mullhs. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma mullhu_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.mullhu v1 v1') (Val.mullhu v2 v2').
Proof.
  intros. unfold Val.mullhu. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma mulhu_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.mulhu v1 v1') (Val.mulhu v2 v2').
Proof.
  intros. unfold Val.mulhu. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.


Lemma shr_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.shr v1 v1') (Val.shr v2 v2').
Proof.
  intros. unfold Val.shr. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. 
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma shrl_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.shrl v1 v1') (Val.shrl v2 v2').
Proof.
  intros. unfold Val.shrl. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. 
  destruct (Int.ltu i0 Int64.iwordsize'); auto.
Qed.

Lemma shru_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.shru v1 v1') (Val.shru v2 v2').
Proof.
  intros. unfold Val.shru. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. 
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma shrlu_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.shrlu v1 v1') (Val.shrlu v2 v2').
Proof.
  intros. unfold Val.shrlu. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. 
  destruct (Int.ltu i0 Int64.iwordsize'); auto.
Qed.

Lemma or_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.or v1 v1') (Val.or v2 v2').
Proof.
  intros. unfold Val.or. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma orl_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.orl v1 v1') (Val.orl v2 v2').
Proof.
  intros. unfold Val.orl. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma ror_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.ror v1 v1') (Val.ror v2 v2').
Proof.
  intros. unfold Val.ror. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma rorl_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.rorl v1 v1') (Val.rorl v2 v2').
Proof.
  intros. unfold Val.rorl. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.


Lemma xor_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.xor v1 v1') (Val.xor v2 v2').
Proof.
  intros. unfold Val.xor. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma xorl_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.xorl v1 v1') (Val.xorl v2 v2').
Proof.
  intros. unfold Val.xorl. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma and_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.and v1 v1') (Val.and v2 v2').
Proof.
  intros. unfold Val.and. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma andl_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.andl v1 v1') (Val.andl v2 v2').
Proof.
  intros. unfold Val.andl. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma notl_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.notl v1) (Val.notl v2).
Proof.
  intros. unfold Val.notl. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma notint_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.notint v1) (Val.notint v2).
Proof.
  intros. unfold Val.notint. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma shl_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.shl v1 v1') (Val.shl v2 v2').
Proof.
  intros. unfold Val.shl. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. 
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Lemma shll_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.shll v1 v1') (Val.shll v2 v2').
Proof.
  intros. unfold Val.shll. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. 
  destruct (Int.ltu i0 Int64.iwordsize'); auto.
Qed.

Lemma addf_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.addf v1 v1') (Val.addf v2 v2').
Proof.
  intros. unfold Val.addf. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma subf_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.subf v1 v1') (Val.subf v2 v2').
Proof.
  intros. unfold Val.subf. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma mulf_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.mulf v1 v1') (Val.mulf v2 v2').
Proof.
  intros. unfold Val.mulf. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma divf_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.divf v1 v1') (Val.divf v2 v2').
Proof.
  intros. unfold Val.divf. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma negf_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.negf v1) (Val.negf v2).
Proof.
  intros. unfold Val.negf. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma absf_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.absf v1) (Val.absf v2).
Proof.
  intros. unfold Val.absf. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma addfs_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.addfs v1 v1') (Val.addfs v2 v2').
Proof.
  intros. unfold Val.addfs. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma subfs_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.subfs v1 v1') (Val.subfs v2 v2').
Proof.
  intros. unfold Val.subfs. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma mulfs_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.mulfs v1 v1') (Val.mulfs v2 v2').
Proof.
  intros. unfold Val.mulfs. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma divfs_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> Val.inject j (Val.divfs v1 v1') (Val.divfs v2 v2').
Proof.
  intros. unfold Val.divfs. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma negfs_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.negfs v1) (Val.negfs v2).
Proof.
  intros. unfold Val.negfs. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma absfs_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.absfs v1) (Val.absfs v2).
Proof.
  intros. unfold Val.absfs. 
  destruct v1; auto. inv H. auto.
Qed.

(* Injection for cmpu_bool and cmplu_bool *)
Lemma valid_ptr_inj : forall j m m',
    Mem.inject j (def_frame_inj m) m m' ->
    forall b i b' delta,                                  
      j b = Some (b', delta) ->
      Mem.valid_pointer m b (Ptrofs.unsigned i) = true ->
      Mem.valid_pointer m' b' (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta))) = true.
Proof.
  intros. eapply Mem.valid_pointer_inject'; eauto.
Qed.


Lemma weak_valid_ptr_inj: forall j m m',
  Mem.inject j (def_frame_inj m) m m' ->
  forall b1 ofs b2 delta,
  j b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros. eapply Mem.weak_valid_pointer_inject'; eauto.
Qed.

Lemma weak_valid_ptr_no_overflow: forall j m m',
  Mem.inject j (def_frame_inj m) m m' ->
  forall b1 ofs b2 delta,
  j b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
Qed.

Lemma valid_different_ptrs_inj: forall j m m',
  Mem.inject j (def_frame_inj m) m m' ->
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  j b1 = Some (b1', delta1) ->
  j b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros. eapply Mem.different_pointers_inject; eauto.
Qed.

Definition cmpu_bool_inject := fun j m m' (MINJ: Mem.inject j (def_frame_inj m) m m') =>
                     Val.cmpu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m')
                                          (valid_ptr_inj j m m' MINJ)
                                          (weak_valid_ptr_inj j m m' MINJ)
                                          (weak_valid_ptr_no_overflow j m m' MINJ)
                                          (valid_different_ptrs_inj j m m' MINJ).

Lemma cmpu_bool_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    opt_lessdef (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2)
                (Val.cmpu_bool (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) eqn:EQ.
  - exploit (cmpu_bool_inject j m m' H1 c v1 v2); eauto.
    intros. rewrite H2. constructor.
  - constructor.
Qed.

Definition cmplu_bool_inject := fun j m m' (MINJ: Mem.inject j (def_frame_inj m) m m') =>
                     Val.cmplu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m')
                                           (valid_ptr_inj j m m' MINJ)
                                           (weak_valid_ptr_inj j m m' MINJ)
                                           (weak_valid_ptr_no_overflow j m m' MINJ)
                                           (valid_different_ptrs_inj j m m' MINJ).


Lemma cmplu_bool_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    opt_lessdef (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2)
                (Val.cmplu_bool (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) eqn:EQ.
  - exploit (cmplu_bool_inject j m m' H1 c v1 v2); eauto.
    intros. rewrite H2. constructor.
  - constructor.
Qed.

Lemma val_of_optbool_lessdef : forall j v1 v2,
    opt_lessdef v1 v2 -> Val.inject j (Val.of_optbool v1) (Val.of_optbool v2).
Proof.
  intros. destruct v1; auto.
  simpl. inv H. destruct b; constructor.
Qed.

Lemma cmpu_inject : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    Val.inject j (Val.cmpu (Mem.valid_pointer m) c v1 v2)
               (Val.cmpu (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. unfold Val.cmpu.
  exploit (cmpu_bool_lessdef j v1 v2); eauto. intros. 
  exploit val_of_optbool_lessdef; eauto.
Qed.

Lemma val_negative_inject: forall j v1 v2,
  Val.inject j v1 v2 -> Val.inject j (Val.negative v1) (Val.negative v2).
Proof.
  intros. unfold Val.negative. destruct v1; auto.
  inv H. auto.
Qed.

Lemma val_negativel_inject: forall j v1 v2,
  Val.inject j v1 v2 -> Val.inject j (Val.negativel v1) (Val.negativel v2).
Proof.
  intros. unfold Val.negativel. destruct v1; auto.
  inv H. auto.
Qed.

Lemma sub_overflow_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> 
    Val.inject j (Val.sub_overflow v1 v1') (Val.sub_overflow v2 v2').
Proof.
  intros. unfold Val.sub_overflow. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma subl_overflow_inject : forall v1 v2 v1' v2' j,
    Val.inject j v1 v2 -> Val.inject j v1' v2' -> 
    Val.inject j (Val.subl_overflow v1 v1') (Val.subl_overflow v2 v2').
Proof.
  intros. unfold Val.subl_overflow. 
  destruct v1; auto. inv H. 
  destruct v1'; auto. inv H0. auto.
Qed.

Lemma compare_ints_inject: forall j v1 v2 v1' v2' rs rs' m m',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_ints v1 v2 rs m) (compare_ints v1' v2' rs' m').
Proof.
  intros. unfold compare_ints, Asm.compare_ints.
  repeat apply regset_inject_expand; auto.
  - apply cmpu_inject; auto.
  - apply cmpu_inject; auto.
  - apply val_negative_inject. apply Val.sub_inject; auto.
  - apply sub_overflow_inject; auto.
Qed.

Lemma cmplu_lessdef : forall j v1 v2 v1' v2' m m' c,
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    opt_val_inject j (Val.cmplu (Mem.valid_pointer m) c v1 v2)
                     (Val.cmplu (Mem.valid_pointer m') c v1' v2').
Proof.
  intros. unfold Val.cmplu.
  exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' c); eauto. intros.
  inversion H2; subst; simpl; constructor.
  apply vofbool_inject.
Qed.

Lemma compare_longs_inject: forall j v1 v2 v1' v2' rs rs' m m',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    Mem.inject j (def_frame_inj m) m m' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_longs v1 v2 rs m) (compare_longs v1' v2' rs' m').
Proof.
  intros. unfold compare_longs, Asm.compare_longs.
  repeat apply regset_inject_expand; auto.
  - unfold Val.cmplu.
    exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' Ceq); eauto. intros.
    inversion H3; subst.
    + simpl. auto. 
    + simpl. apply vofbool_inject.
  - unfold Val.cmplu.
    exploit (cmplu_bool_lessdef j v1 v2 v1' v2' m m' Clt); eauto. intros.
    inversion H3; subst.
    + simpl. auto. 
    + simpl. apply vofbool_inject.
  - apply val_negativel_inject. apply Val.subl_inject; auto.
  - apply subl_overflow_inject; auto.
Qed.

Ltac solve_val_inject :=
  match goal with
  (* | [ H : Val.inject _ (Vint _) (Vlong _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vint _) (Vfloat _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vint _) (Vsingle _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vint _) (Vptr _ _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vptr _ _) (Vlong _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vptr _ _) (Vfloat _) |- _] => inversion H *)
  (* | [ H : Val.inject _ (Vptr _ _) (Vsingle _) |- _] => inversion H *)
  | [ H : Val.inject _ (Vfloat _) Vundef |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vint _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vlong _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vsingle _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vptr _ _) |- _] => inversion H
  | [ H : Val.inject _ (Vfloat _) (Vfloat _) |- _] => inv H; solve_val_inject
  | [ H : Val.inject _ (Vsingle _) Vundef |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vint _) |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vlong _) |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vsingle _) |- _] => inv H; solve_val_inject
  | [ H : Val.inject _ (Vsingle _) (Vptr _ _) |- _] => inversion H
  | [ H : Val.inject _ (Vsingle _) (Vfloat _) |- _] => inversion H
  | [ |- Val.inject _ (Val.of_bool ?v) (Val.of_bool ?v) ] => apply vofbool_inject
  | [ |- Val.inject _ Vundef _ ] => auto
  end.

Ltac solve_regset_inject :=
  match goal with
  | [ H: regset_inject ?j ?rs1 ?rs2 |- regset_inject ?j (Asm.undef_regs ?uregs ?rs1) (Asm.undef_regs ?uregs ?rs2)] =>
    apply undef_regs_pres_inject; auto
  | [ |- regset_inject _ (Asm.undef_regs _ _) _ ] =>
    unfold Asm.undef_regs; solve_regset_inject
  | [ |- regset_inject _ _ (Asm.undef_regs _ _) ] =>
    unfold Asm.undef_regs; simpl; solve_regset_inject
  | [ |- regset_inject _ (?rs1 # ?r <- ?v1) (?rs2 # ?r <- ?v2) ] =>
    apply regset_inject_expand; [solve_regset_inject | solve_val_inject]
  | [ H: regset_inject ?j ?rs1 ?rs2 |- regset_inject ?j ?rs1 ?rs2 ] =>
    auto
  end.

Lemma compare_floats_inject: forall j v1 v2 v1' v2' rs rs',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_floats v1 v2 rs) (compare_floats v1' v2' rs').
Proof.
  intros. unfold compare_floats, Asm.compare_floats.
  destruct v1, v2, v1', v2'; try solve_regset_inject. 
Qed.

Lemma compare_floats32_inject: forall j v1 v2 v1' v2' rs rs',
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    regset_inject j rs rs' -> 
    regset_inject j (compare_floats32 v1 v2 rs) (compare_floats32 v1' v2' rs').
Proof.
  intros. unfold compare_floats32, Asm.compare_floats32.
  destruct v1, v2, v1', v2'; try solve_regset_inject. 
Qed.

Lemma zero_ext_inject : forall v1 v2 n j,
    Val.inject j v1 v2 -> Val.inject j (Val.zero_ext n v1) (Val.zero_ext n v2).
Proof.
  intros. unfold Val.zero_ext. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma sign_ext_inject : forall v1 v2 n j,
    Val.inject j v1 v2 -> Val.inject j (Val.sign_ext n v1) (Val.sign_ext n v2).
Proof.
  intros. unfold Val.sign_ext. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma longofintu_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.longofintu v1) (Val.longofintu v2).
Proof.
  intros. unfold Val.longofintu. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma longofint_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.longofint v1) (Val.longofint v2).
Proof.
  intros. unfold Val.longofint. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma singleoffloat_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.singleoffloat v1) (Val.singleoffloat v2).
Proof.
  intros. unfold Val.singleoffloat. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma loword_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.loword v1) (Val.loword v2).
Proof.
  intros. unfold Val.loword. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma floatofsingle_inject : forall v1 v2 j,
    Val.inject j v1 v2 -> Val.inject j (Val.floatofsingle v1) (Val.floatofsingle v2).
Proof.
  intros. unfold Val.floatofsingle. 
  destruct v1; auto. inv H. auto.
Qed.

Lemma intoffloat_inject : forall j v1 v2,
  Val.inject j v1 v2 -> opt_val_inject j (Val.intoffloat v1) (Val.intoffloat v2).
Proof.
  intros. unfold Val.intoffloat. destruct v1; try constructor.
  inv H. destruct (Floats.Float.to_int f); simpl. 
  - constructor. auto.
  - constructor.
Qed.

Lemma floatofint_inject : forall j v1 v2,
  Val.inject j v1 v2 -> opt_val_inject j (Val.floatofint v1) (Val.floatofint v2).
Proof.
  intros. unfold Val.floatofint. destruct v1; try constructor.
  inv H. constructor; auto.
Qed.

Lemma intofsingle_inject : forall j v1 v2,
  Val.inject j v1 v2 -> opt_val_inject j (Val.intofsingle v1) (Val.intofsingle v2).
Proof.
  intros. unfold Val.intofsingle. destruct v1; try constructor.
  inv H. destruct (Floats.Float32.to_int f); simpl; constructor; auto.
Qed.

Lemma longoffloat_inject : forall j v1 v2,
  Val.inject j v1 v2 -> opt_val_inject j (Val.longoffloat v1) (Val.longoffloat v2).
Proof.
  intros. unfold Val.longoffloat. destruct v1; try constructor.
  inv H. destruct (Floats.Float.to_long f) eqn:EQ; simpl; constructor; auto.
Qed.

Lemma floatoflong_inject : forall j v1 v2,
  Val.inject j v1 v2 -> opt_val_inject j (Val.floatoflong v1) (Val.floatoflong v2).
Proof.
  intros. unfold Val.floatoflong. destruct v1; try constructor.
  inv H. constructor; auto. 
Qed.

Lemma longofsingle_inject : forall j v1 v2,
  Val.inject j v1 v2 -> opt_val_inject j (Val.longofsingle v1) (Val.longofsingle v2).
Proof.
  intros. unfold Val.longofsingle. destruct v1; try constructor.
  inv H. destruct (Floats.Float32.to_long f) eqn:EQ; simpl; constructor; auto.
Qed.

Lemma singleoflong_inject : forall j v1 v2,
  Val.inject j v1 v2 -> opt_val_inject j (Val.singleoflong v1) (Val.singleoflong v2).
Proof.
  intros. unfold Val.singleoflong. destruct v1; try constructor.
  inv H. constructor; auto.
Qed.

Lemma singleofint_inject : forall j v1 v2,
  Val.inject j v1 v2 -> opt_val_inject j (Val.singleofint v1) (Val.singleofint v2).
Proof.
  intros. unfold Val.singleofint. destruct v1; try constructor.
  inv H. constructor; auto.
Qed.
  
Ltac solve_store_load :=
  match goal with
  | [ H : Asm.exec_instr _ _ _ _ _ = Next _ _ |- _ ] =>
    unfold Asm.exec_instr in H; simpl in H; solve_store_load
  | [ H : Asm.exec_store _ _ _ _ _ _ _ _ = Next _ _ |- _ ] =>
    exploit exec_store_step; eauto
  | [ H : Asm.exec_load _ _ _ _ _ _ _ = Next _ _ |- _ ] =>
    exploit exec_load_step; eauto
  end.

Ltac solve_opt_lessdef := 
  match goal with
  | [ |- opt_lessdef (match ?rs1 ?r with
                     | _ => _
                     end) _ ] =>
    let EQ := fresh "EQ" in (destruct (rs1 r) eqn:EQ; solve_opt_lessdef)
  | [ |- opt_lessdef None _ ] => constructor
  | [ |- opt_lessdef (Some _) (match ?rs2 ?r with
                              | _ => _
                              end) ] =>
    let EQ := fresh "EQ" in (destruct (rs2 r) eqn:EQ; solve_opt_lessdef)
  | [ H1: regset_inject _ ?rs1 ?rs2, H2: ?rs1 ?r = _, H3: ?rs2 ?r = _ |- _ ] =>
    generalize (H1 r); rewrite H2, H3; clear H2 H3; inversion 1; subst; solve_opt_lessdef
  | [ |- opt_lessdef (Some ?v) (Some ?v) ] => constructor
  end.

Lemma eval_testcond_inject: forall j c rs1 rs2,
    regset_inject j rs1 rs2 ->
    opt_lessdef (Asm.eval_testcond c rs1) (Asm.eval_testcond c rs2).
Proof.
  intros. destruct c; simpl; try solve_opt_lessdef.
Qed.

Hint Resolve nextinstr_nf_pres_inject nextinstr_pres_inject regset_inject_expand 
  regset_inject_expand_vundef_left undef_regs_pres_inject 
  zero_ext_inject sign_ext_inject longofintu_inject longofint_inject
  singleoffloat_inject loword_inject floatofsingle_inject intoffloat_inject maketotal_inject
  intoffloat_inject floatofint_inject intofsingle_inject singleofint_inject
  longoffloat_inject floatoflong_inject longofsingle_inject singleoflong_inject
  eval_addrmode32_inject eval_addrmode64_inject eval_addrmode_inject
  neg_inject negl_inject Val.add_inject Val.addl_inject
  Val.sub_inject Val.subl_inject mul_inject mull_inject mulhs_inject mulhu_inject
  mullhs_inject mullhu_inject shr_inject shrl_inject or_inject orl_inject
  xor_inject xorl_inject and_inject andl_inject notl_inject
  shl_inject shll_inject vzero_inject notint_inject
  shru_inject shrlu_inject ror_inject rorl_inject
  compare_ints_inject compare_longs_inject compare_floats_inject compare_floats32_inject
  addf_inject subf_inject mulf_inject divf_inject negf_inject absf_inject
  addfs_inject subfs_inject mulfs_inject divfs_inject negfs_inject absfs_inject
  val_of_optbool_lessdef eval_testcond_inject: inject_db.

Ltac solve_exec_instr :=
  match goal with
  | [ |- Next _ _ = Next _ _ ] =>
    reflexivity
  | [ |- context [eval_testcond _ _] ]=>
    unfold eval_testcond; solve_exec_instr
  | [ H: Asm.eval_testcond ?c ?r = _ |- context [Asm.eval_testcond ?c ?r] ] =>
    rewrite H; solve_exec_instr
  | [ H: _ = Asm.eval_testcond ?c ?r |- context [Asm.eval_testcond ?c ?r] ] =>
    rewrite <- H; solve_exec_instr
  end.

Ltac solve_match_states :=
  match goal with
  | [ H: Asm.Stuck = Next _ _ |- _ ] => inv H
  | [ |- exists _, _ ] => eexists; solve_match_states
  | [ |- (FlatAsm.exec_instr _ _ _ _ = Next _ _) /\ match_states _ _ ] =>
    split; [simpl; solve_exec_instr | econstructor; eauto; solve_match_states]
  | [ |- regset_inject _ _ _ ] =>
    eauto 10 with inject_db
  end.

Ltac destr_eval_testcond :=
  match goal with
  | [ H : match Asm.eval_testcond ?c ?rs with | _ => _ end = Next _ _ |- _ ] =>
    let ETEQ := fresh "ETEQ" in (
      destruct (Asm.eval_testcond c rs) eqn:ETEQ); destr_eval_testcond
  | [ H : Some ?b = Asm.eval_testcond _ _ |- _ ] =>
    match b with
    | true => fail 1
    | false => fail 1
    | _ => destruct b; destr_eval_testcond
    end
  | [ H : Asm.eval_testcond _ _ = Some ?b |- _] =>
    match b with
    | true => fail 1
    | false => fail 1
    | _ => destruct b; destr_eval_testcond
    end
  | [ H : Asm.Next _ _ = Next _ _ |- _ ] =>
    inv H; destr_eval_testcond
  | [ H: opt_lessdef (Some true) (Asm.eval_testcond _ _) |- _ ] =>
    inv H; destr_eval_testcond
  | [ H: opt_lessdef (Some false) (Asm.eval_testcond _ _) |- _ ] =>
    inv H; destr_eval_testcond
  | _ => idtac
  end.

Ltac destr_match_outcome :=
  match goal with
  | [ H: Asm.Stuck = Next _ _ |- _ ] => inv H
  | [ H: Asm.Next _ _ = Next _ _ |- _ ] => inv H; destr_match_outcome
  | [ H: match ?a with _ => _ end = Next _ _ |- _] =>
    let EQ := fresh "EQ" in (destruct a eqn:EQ; destr_match_outcome)
  | _ => idtac
  end.


Lemma goto_label_pres_mem : forall f l rs1 m1 rs1' m1',
    Asm.goto_label ge f l rs1 m1 = Next rs1' m1' -> m1 = m1'.
Proof.
  unfold Asm.goto_label. intros.
  destruct (label_pos l 0 (Asm.fn_code f)); try inv H. 
  destruct (rs1 Asm.PC); try inv H1.
  destruct (Genv.find_funct_ptr ge b); try inv H0. auto.
Qed.

Lemma goto_label_inject : forall rs1 rs2 gm lm id b f l z j m1 m2 rs1' m1' ofs
                            (MATCHSMINJ: match_sminj gm lm j)
                            (RINJ: regset_inject j rs1 rs2)
                            (MINJ:Mem.inject j (def_frame_inj m1) m1 m2),
    rs1 PC = Vptr b ofs ->
    Genv.find_symbol ge id = Some b ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    Asm.goto_label ge f l rs1 m1 = Next rs1' m1' ->
    lm id l = Some z ->
    exists rs2', goto_label tge (code_label z) rs2 m2 = Next rs2' m2 /\
            regset_inject j rs1' rs2' /\ Mem.inject j (def_frame_inj m1') m1' m2.
Proof.
  intros. unfold Asm.goto_label in H2.
  destruct (label_pos l 0 (Asm.fn_code f)) eqn:EQLBL; try inv H2.
  setoid_rewrite H in H5. rewrite H1 in H5. inv H5.
  exploit agree_sminj_lbl; eauto. intros. inv H2.
  eexists. split.
  unfold goto_label. auto. split; auto.
  repeat apply regset_inject_expand; auto. setoid_rewrite <- H6.
  eapply Val.inject_ptr; eauto.
Qed.

Definition null_or_valid_ptr (v:val) : Prop :=
  v = Vnullptr \/ exists (b : block) (ofs : ptrofs), v = Vptr b ofs.

Definition agree_ge_rsp_ptr (rs:regset): Prop :=
  forall b ofs, (rs RSP) = Vptr b ofs -> b = Genv.genv_next ge.

Lemma goto_tbl_label_inject : forall gm lm id tbl tbl' l b f j rs1 rs2 m1 m2 rs1' m1' i ofs
                                (MATCHSMINJ: match_sminj gm lm j)
                                (RINJ: regset_inject j rs1 rs2)
                                (MINJ:Mem.inject j (def_frame_inj m1) m1 m2),
    rs1 PC = Vptr b ofs ->
    Genv.find_symbol ge id = Some b ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    list_nth_z tbl i = Some l ->
    Asm.goto_label ge f l ((rs1 # RAX <- Vundef) # RDX <- Vundef) m1 = Next rs1' m1' ->
    transl_tbl lm id tbl = OK tbl' ->
    exists rs2' l', 
      list_nth_z tbl' i = Some l' /\
      FlatAsm.goto_label tge l' ((rs2 # RAX <- Vundef) # RDX <- Vundef) m2 = Next rs2' m2 /\
      regset_inject j rs1' rs2' /\ Mem.inject j (def_frame_inj m1') m1' m2.
Proof.
  induction tbl; simpl; intros.
  - congruence.
  - destruct (zeq i 0).
    + inv H2. monadInvX H4.
      exploit (goto_label_inject ((rs1 # RAX <- Vundef) # RDX <- Vundef) ((rs2 # RAX <- Vundef) # RDX <- Vundef)); eauto with inject_db. 
      intros (rs2' & GLBL & RSINJ' & MINJ').
      eexists; eexists. split. simpl. auto. split.
      rewrite GLBL. auto. split; eauto.
    + monadInvX H4.
      exploit (IHtbl x); eauto.
      intros (rs2' & l' & LNTH & GLBL & RSINJ' & MINJ').
      exists rs2', l'. split. simpl. erewrite zeq_false; auto. split; auto.
Qed.


Lemma Vundef_null_ptr_eq_absurd :
  ~ Vundef = Vnullptr.
Proof.
  unfold not, Vnullptr. intros. destruct Archi.ptr64; congruence.
Qed.

Lemma Vundef_null_or_valid_ptr_absurd :
  ~null_or_valid_ptr Vundef.
Proof.
  unfold not. intros. unfold null_or_valid_ptr in *. destruct H.
  - apply Vundef_null_ptr_eq_absurd. auto.
  - destruct H as (b & ofs & EQ). congruence.
Qed.

Lemma Vfloat_null_ptr_eq_absurd : forall f,
    ~ Vfloat f = Vnullptr.
Proof.
  unfold not, Vnullptr. intros. destruct Archi.ptr64; congruence.
Qed.

Lemma Vfloat_null_or_valid_ptr_absurd : forall f,
    ~null_or_valid_ptr (Vfloat f).
Proof.
  unfold not. intros. unfold null_or_valid_ptr in *. destruct H.
  - eapply Vfloat_null_ptr_eq_absurd. eauto.
  - destruct H as (b & ofs & EQ). congruence.
Qed.

Lemma Vsingle_null_ptr_eq_absurd : forall f,
    ~ Vsingle f = Vnullptr.
Proof.
  unfold not, Vnullptr. intros. destruct Archi.ptr64; congruence.
Qed.

Lemma Vsingle_null_or_valid_ptr_absurd : forall f,
    ~null_or_valid_ptr (Vsingle f).
Proof.
  unfold not. intros. unfold null_or_valid_ptr in *. destruct H.
  - eapply Vsingle_null_ptr_eq_absurd. eauto.
  - destruct H as (b & ofs & EQ). congruence.
Qed.


Lemma exec_instr_pres_rsp : forall f i rs1 rs1' m1 m1',
  asm_instr_no_rsp i ->
  RawAsmgen.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
  null_or_valid_ptr (rs1 RSP) -> null_or_valid_ptr (rs1' RSP).
Proof.
  intros. destruct i. 
  destruct i; simpl in *;
    try (exploit H; eauto; intros; unfold RSP in *; congruence).
  - destruct (Mem.store Mptr m1 (Genv.genv_next ge)
                        (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (offset_after_alloc (current_offset (rs1 Asm.RSP)) frame)) ofs_link)) (rs1 Asm.RSP)) 
             eqn:MSTORELINK;
      try inv H0.
    destruct (Mem.store Mptr m (Genv.genv_next ge) (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (offset_after_alloc (current_offset (rs1 Asm.RSP)) frame)) ofs_ra))
                        (rs1 Asm.RA))
             eqn:MSTORERA;
    try inv H3.
    unfold null_or_valid_ptr. right. eexists; eexists.
    erewrite nextinstr_rsp. rewrite Pregmap.gss. auto.
  - destruct (Mem.loadv Mptr m1 (Val.offset_ptr (rs1 Asm.RSP) ofs_ra)) eqn:LOADRA;
      try inv H0.
    destruct (Mem.loadv Mptr m1 (Val.offset_ptr (rs1 Asm.RSP) ofs_link)) eqn:LOADRSP;
      try inv H3.
    unfold null_or_valid_ptr. right.
    eexists; eexists. erewrite nextinstr_rsp. 
    rewrite Pregmap.gso; try congruence. erewrite Pregmap.gss.
    admit.
Admitted.
    

(** The internal step preserves the invariant *)
Lemma exec_instr_step : forall j rs1 rs2 m1 m2 rs1' m1' gm lm i i' id ofs ofs' f b
                        (MINJ: Mem.inject j (def_frame_inj m1) m1 m2)
                        (MATCHSMINJ: match_sminj gm lm j)
                        (GINJFLATMEM: globs_inj_into_flatmem j)
                        (INSTRINTERNAL: valid_instr_offset_is_internal j)
                        (EXTEXTERNAL: extfun_entry_is_external j)
                        (MATCHFINDFUNCT: match_find_funct j)
                        (RSINJ: regset_inject j rs1 rs2)
                        (GBVALID: glob_block_valid m1)
                        (GMUNDEF: gid_map_for_undef_syms gm)
                        (SBINJ:stack_block_inject j),
    rs1 PC = Vptr b ofs ->
    Genv.find_symbol ge id = Some b ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    Asm.find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    RawAsmgen.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
    transl_instr gm lm ofs' id i = OK i' ->
    exists rs2' m2',
      FlatAsm.exec_instr tge i' rs2 m2 = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. destruct i. destruct i; inv H3; simpl in *; monadInvX H4;
                        try first [solve_store_load |
                                   solve_match_states].

  - (* Pmov_rs *)
    apply nextinstr_nf_pres_inject.
    apply regset_inject_expand; auto.
    inv MATCHSMINJ.
    unfold Genv.symbol_address. unfold Genv.get_label_addr0.
    destruct (Genv.find_symbol ge id0) eqn:FINDSYM; auto.
    exploit agree_sminj_glob0; eauto.
    intros (ofs1 & b1 & FSYM & GLBL & JB).
    rewrite FSYM in FINDSYM; inv FINDSYM. 
    unfold get_sect_label_addr0. rewrite GLBL.
    rewrite <- (Ptrofs.add_zero_l ofs1).
    eapply Val.inject_ptr; eauto.
    rewrite Ptrofs.repr_unsigned. auto.

  (* Divisions *)
  - unfold Asm.exec_instr in H6; simpl in H6.
    destr_match_outcome. 
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. setoid_rewrite <- H10. setoid_rewrite <- H8.
    setoid_rewrite <- H6. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - unfold Asm.exec_instr in H6; simpl in H6.
    destr_match_outcome. 
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. setoid_rewrite <- H10. setoid_rewrite <- H8.
    setoid_rewrite <- H6. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - unfold Asm.exec_instr in H6; simpl in H6.
    destr_match_outcome. 
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. setoid_rewrite <- H10. setoid_rewrite <- H8.
    setoid_rewrite <- H6. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.

  - unfold Asm.exec_instr in H6; simpl in H6.
    destr_match_outcome. 
    generalize (RSINJ Asm.RDX). generalize (RSINJ Asm.RAX). generalize (RSINJ r1).
    rewrite EQ, EQ0, EQ1. inversion 1; subst. inversion 1; subst. inversion 1; subst.
    eexists; eexists. split. simpl. setoid_rewrite <- H10. setoid_rewrite <- H8.
    setoid_rewrite <- H6. rewrite EQ2. auto.
    eapply match_states_intro; eauto with inject_db.
     
  - (* Pcmov *)
    unfold Asm.exec_instr in H6; simpl in H6.
    exploit (eval_testcond_inject j c rs1 rs2); eauto.
    intros. 


    destr_eval_testcond; try solve_match_states.
    destruct (Asm.eval_testcond c rs2) eqn:EQ'. destruct b0; solve_match_states.
    solve_match_states.

  - (* Pjmp_l *)
    unfold Asm.exec_instr in H6; simpl in H6.
    unfold Asm.goto_label in H6. destruct (label_pos l 0 (Asm.fn_code f)) eqn:LBLPOS; inv H6.
    destruct (rs1 Asm.PC) eqn:PC1; inv H4.
    destruct (Genv.find_funct_ptr ge b0); inv H5.
    eexists; eexists. split. simpl.
    unfold goto_label. eauto.
    eapply match_states_intro; eauto.
    apply regset_inject_expand; auto. 
    unfold PC in *. rewrite H in *. inv PC1.    
    eapply agree_sminj_lbl; eauto.

  - (* Pjmp_s *)
    apply regset_inject_expand; auto.
    inversion MATCHSMINJ. 
    exploit (agree_sminj_glob0 symb s0); eauto.
    intros (ofs1 & b1 & FSYM & LBLOFS & JB). 
    unfold Genv.symbol_address. rewrite FSYM. 
    unfold Genv.get_label_addr0. unfold get_sect_label_addr0. rewrite LBLOFS.
    unfold flatptr. econstructor; eauto.
    simpl_goal. auto.

  - (* Pjcc *)
    unfold Asm.exec_instr in H6; simpl in H6.
    exploit (eval_testcond_inject j c rs1 rs2); eauto.
    intros.
    destr_eval_testcond; try solve_match_states.
    exploit goto_label_inject; eauto. intros (rs2' & GOTO & RINJ' & MINJ').
    exists rs2', m2. split. simpl. unfold eval_testcond. rewrite <- H7. auto.
    eapply match_states_intro; eauto.
    assert (m1 = m1') by (eapply goto_label_pres_mem; eauto). subst. auto.

  - (* Pjcc2 *)
    unfold Asm.exec_instr in H6; simpl in H6.
    exploit (eval_testcond_inject j c1 rs1 rs2); eauto.
    exploit (eval_testcond_inject j c2 rs1 rs2); eauto.
    intros ELF1 ELF2.
    destr_eval_testcond; try solve_match_states.
    exploit goto_label_inject; eauto. intros (rs2' & GOTO & RINJ' & MINJ').
    exists rs2', m2. split. simpl. setoid_rewrite <- H5. setoid_rewrite <- H7. auto.
    eapply match_states_intro; eauto.
    assert (m1 = m1') by (eapply goto_label_pres_mem; eauto). subst. auto.

  - (* Pjmptbl *)
    unfold Asm.exec_instr in H6; simpl in H6.
    destruct (rs1 r) eqn:REQ; inv H6.
    destruct (list_nth_z tbl (Int.unsigned i)) eqn:LEQ; inv H4.
    assert (rs2 r = Vint i) by
        (generalize (RSINJ r); rewrite REQ; inversion 1; auto).
    exploit (goto_tbl_label_inject gm lm id tbl x0 l); eauto. 
    intros (rs2' & l' & LEQ' & GLBL & RSINJ' & MINJ').
    exists rs2', m2. split. simpl. setoid_rewrite H3. setoid_rewrite LEQ'. auto. 
    eapply match_states_intro; eauto.
    assert (m1 = m1') by (eapply goto_label_pres_mem; eauto). subst. auto.
    
  - (* Pcall_s *)
    generalize (RSINJ PC). intros. rewrite H in *. inv H3.
    repeat apply regset_inject_expand; auto.
    + unfold instr_size. setoid_rewrite H. 
      apply Val.offset_ptr_inject. eauto.
    + exploit (inject_symbol_sectlabel gm lm j symb s0 Ptrofs.zero); eauto. 
      unfold Genv.get_label_addr. unfold Genv.get_label_addr0.
      unfold get_sect_label_addr. 
      generalize (Val.offset_ptr_zero (get_sect_label_addr0 (Genv.genv_smap tge) s0)).
      intros. inv H3. auto. rewrite <- H8 in *. inv H4. auto.
      
  - (* Pcall_r *)
    generalize (RSINJ PC). intros. rewrite H in *. inv H3.
    repeat apply regset_inject_expand; auto.
    unfold instr_size. setoid_rewrite H. 
    apply Val.offset_ptr_inject. eauto.

  - (* Pallocframe *)
    generalize (RSINJ RSP). intros RSPINJ.
    assert (null_or_valid_ptr (rs1 RSP)) as RSPVALID. admit.      
    assert (agree_ge_rsp_ptr rs1) as GERSP. admit.
    unfold stack_block_inject in *.
    (* assert (rs1 RSP = Vnullptr \/ exists b ofs, rs1 RSP = Vptr b ofs /\ j b = Some (mem_block, Genv.genv_stack_limit tge -  Mem.stack_limit)). *)
    (* admit. *)
    (* assert (forall b ofs, rs1 RSP = Vptr b ofs -> b = Genv.genv_next ge). admit. *)
    unfold RSP in *. 
    destruct (Mem.store Mptr m1 (Genv.genv_next ge)
                        (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (offset_after_alloc (current_offset (rs1 Asm.RSP)) frame)) ofs_link))
                        (rs1 Asm.RSP)) eqn:STORELINK; try inv H6.
    generalize (RSINJ Asm.RSP). intros.
    exploit (fun ofs delta => 
               store_mapped_inject' j Mptr m1 (Genv.genv_next ge) ofs (rs1 Asm.RSP) m m2 mem_block delta (rs2 Asm.RSP)); eauto.
    intros (m' & STORELINK' & MINJ1).
    destruct (Mem.store Mptr m (Genv.genv_next ge)
                        (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (offset_after_alloc (current_offset (rs1 Asm.RSP)) frame)) ofs_ra))
                        (rs1 Asm.RA)) eqn:STORERA; try inv H4.
    generalize (RSINJ Asm.RA). intros.
    exploit (fun ofs delta => 
               store_mapped_inject' j Mptr m (Genv.genv_next ge) ofs (rs1 Asm.RA) m1' m' mem_block delta (rs2 Asm.RA)); eauto.
    intros (m2' & STORERA' & MINJ2).
    destruct (rs1 Asm.RSP) eqn:RSP1; simpl in *.
    + generalize Vundef_null_or_valid_ptr_absurd. congruence.
    + inv H3. eexists; eexists; split.
      (* Find the resulting state *)
      setoid_rewrite <- H7. simpl.
      setoid_rewrite <- H7 in STORELINK'.
      rewrite <- Zplus_0_r_reverse in STORELINK', STORERA'.
      rewrite STORELINK'.
      setoid_rewrite <- H7. simpl.
      setoid_rewrite STORERA'. auto.
      (* Solve the match state *)
      eapply match_states_intro; eauto.
      setoid_rewrite <- H7. unfold RSP, RAX. apply nextinstr_pres_inject.
      repeat apply regset_inject_expand; eauto.
      unfold flatptr. simpl. eapply Val.inject_ptr; eauto.
      rewrite Ptrofs.add_zero. auto.
      eapply store_pres_glob_block_valid; eauto.
      eapply store_pres_glob_block_valid; eauto.
    + inv H3. eexists; eexists; split.
      (* Find the resulting state *)
      setoid_rewrite <- H7. simpl.
      setoid_rewrite <- H7 in STORELINK'.
      rewrite <- Zplus_0_r_reverse in STORELINK', STORERA'.
      rewrite STORELINK'.
      setoid_rewrite <- H7. simpl.
      setoid_rewrite STORERA'. auto.
      (* Solve the match state *)
      eapply match_states_intro; eauto.
      setoid_rewrite <- H7. unfold RSP, RAX. apply nextinstr_pres_inject.
      repeat apply regset_inject_expand; eauto.
      unfold flatptr. simpl. eapply Val.inject_ptr; eauto.
      rewrite Ptrofs.add_zero. auto.
      eapply store_pres_glob_block_valid; eauto.
      eapply store_pres_glob_block_valid; eauto.
    + exploit Vfloat_null_or_valid_ptr_absurd; eauto. intros. contradiction.
    + exploit Vsingle_null_or_valid_ptr_absurd; eauto. intros. contradiction.
    + inv H3. unfold agree_ge_rsp_ptr in *. exploit GERSP; eauto. intros. subst.
      rewrite SBINJ in *. inv H8.
      eexists; eexists; split.
      (* Find the resulting state *)
      rewrite <- Zplus_0_r_reverse in STORELINK', STORERA'.
      setoid_rewrite <- H7. simpl. setoid_rewrite <- H7 in STORELINK'.
      rewrite Ptrofs.add_zero. rewrite Ptrofs.add_zero in STORELINK'. rewrite STORELINK'.
      setoid_rewrite <- H7. simpl. rewrite Ptrofs.add_zero. setoid_rewrite STORERA'.
      auto.
      (* Solve match states *)
      eapply match_states_intro; eauto.
      eapply nextinstr_pres_inject; eauto. 
      repeat eapply regset_inject_expand; eauto.
      setoid_rewrite <- H7. simpl. 
      eapply Val.inject_ptr; eauto.
      repeat rewrite Ptrofs.add_zero. auto.
      eapply store_pres_glob_block_valid; eauto.
      eapply store_pres_glob_block_valid; eauto.

  - (* Pfreeframe *)
    generalize (RSINJ Asm.RSP). intros.
    destruct (Mem.loadv Mptr m1 (Val.offset_ptr (rs1 Asm.RSP) ofs_ra)) eqn:EQRA; try inv H6.
    destruct (Mem.loadv Mptr m1 (Val.offset_ptr (rs1 Asm.RSP) ofs_link)) eqn:EQLINK; try inv H5.
    exploit (fun g a2 => Mem.loadv_inject j g m1' m2 Mptr (Val.offset_ptr (rs1 Asm.RSP) ofs_ra) a2 v); eauto.
    apply Val.offset_ptr_inject. auto.
    exploit (fun g a2 => Mem.loadv_inject j g m1' m2 Mptr (Val.offset_ptr (rs1 Asm.RSP) ofs_link) a2 v0); eauto.
    apply Val.offset_ptr_inject. auto.
    intros (v2 & MLOAD2 & VINJ2) (v3 & MLOAD3 & VINJ3).
    eexists; eexists. split. simpl.
    setoid_rewrite MLOAD3. setoid_rewrite MLOAD2. auto.
    eapply match_states_intro; eauto with inject_db.

Admitted.


Theorem step_simulation:
  forall S1 t S2,
    RawAsmgen.step ge S1 t S2 ->
    forall S1' (MS: match_states S1 S1'),
    exists S2',
      FlatAsm.step tge S1' t S2' /\
      match_states S2 S2'.
Proof.
  destruct 1; intros; inv MS.

  - (* Internal step *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst.
    exploit (agree_sminj_instr gm lm j MATCHSMINJ b b2 f ofs delta i); eauto.
    intros (id & i' & ofs1 & FITARG & FSYMB & TRANSL).
    exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst.
    exploit (exec_instr_step j rs rs'0 m m'0 rs' m' gm lm i i' id); eauto.
    intros (rs2' & m2' & FEXEC & MS1).
    exists (State rs2' m2'). split; auto.
    apply FlatAsm.exec_step_internal with (Ptrofs.add ofs (Ptrofs.repr delta)) i'; auto.
    unfold valid_instr_offset_is_internal in INSTRINTERNAL.
    apply INSTRINTERNAL with b f i; auto.
        
  - (* Builtin *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H.
    inversion 1; subst.
    exploit (agree_sminj_instr gm lm j MATCHSMINJ b b2 f ofs delta (Asm.Pbuiltin ef args res, sz)); auto.
    intros (id & i' & ofs1 & FITARG & FSYMB & TRANSL).
    exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst.
    monadInv TRANSL. monadInv EQ.
    set (pbsect := {| sect_block_id := code_sect_id; sect_block_start := Ptrofs.repr ofs1; sect_block_size := Ptrofs.repr (si_size sz) |}).
    fold pbsect in FITARG.
    exploit (eval_builtin_args_inject gm lm j m m'0 rs rs'0 (rs Asm.RSP) (rs'0 Asm.RSP) args vargs x0); auto.
    intros (vargs' & EBARGS & ARGSINJ).
    generalize (external_call_inject j vargs vargs' m m'0 m' vres t ef ARGSINJ MINJ H3).
    intros (j' & vres2 & m2' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
    set (rs' := nextinstr_nf (set_res res vres2 (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs'0)) (sect_block_size pbsect)).
    exploit (FlatAsm.exec_step_builtin tge (Ptrofs.add ofs (Ptrofs.repr delta))
                                       ef x0 res rs'0  m'0 vargs' t vres2 rs' m2' pbsect); auto.
    unfold valid_instr_offset_is_internal in INSTRINTERNAL.
    eapply INSTRINTERNAL; eauto.
    intros FSTEP. eexists; split; eauto.
    eapply match_states_intro with (j:=j'); eauto.
    (* Supposely the following propreties can proved by separation property of injections *)
    + eapply (inject_pres_match_sminj j); eauto.
    + eapply (inject_pres_globs_inj_into_flatmem j); eauto.
    + eapply (inject_pres_valid_instr_offset_is_internal j); eauto.
    + eapply (inject_pres_extfun_entry_is_external j); eauto.
    + eapply (inject_pres_match_find_funct j); eauto.
    + subst rs'. unfold regset_inject. intros. subst pbsect; simpl.
      unfold nextinstr_nf, Asm.nextinstr_nf.
      assert (regset_inject j' rs rs'0) by 
          (eapply regset_inject_incr; eauto).
      set (dregs := (map Asm.preg_of (Machregs.destroyed_by_builtin ef))) in *.
      unfold preg_of. fold dregs.
      generalize (undef_regs_pres_inject j' rs rs'0 dregs H5). intros.
      unfold undef_regs. unfold set_res.
      set (rs1 := (Asm.undef_regs dregs rs)) in *.
      set (rs2 := (Asm.undef_regs dregs rs'0)) in *.
      generalize (set_res_pres_inject res j' 
                  rs1 rs2 H9 vres vres2 RESINJ).
      set (rs3 := (Asm.set_res res vres rs1)) in *.
      set (rs4 := (Asm.set_res res vres2 rs2)) in *.
      intros.
      fold ZF CF PF SF OF.
      set (fregs := (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil)) in *.
      generalize (undef_regs_pres_inject j' rs3 rs4 fregs H10).
      intros.         
      generalize (nextinstr_pres_inject j'  
                    (undef_regs fregs rs3) (undef_regs fregs rs4) 
                    (Ptrofs.repr (si_size sz)) H11).
      intros. unfold regset_inject in H12.
      apply H12.
    + eapply extcall_pres_glob_block_valid; eauto.

  - (* External call *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst. rewrite Ptrofs.add_zero_l in H6.
    exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst.
    generalize (extcall_arguments_inject rs rs'0 m m'0 ef args j H1 MINJ RSINJ).
    intros (args2 & ARGSINJ & EXTCALLARGS).
    exploit (external_call_inject j args args2 m m'0 m' res t ef); eauto.
    intros (j' & res' & m2' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
    exploit (FlatAsm.exec_step_external tge (Ptrofs.repr delta) ef args2 res'); eauto.
    + generalize (RSINJ Asm.RSP). intros. 
      eapply vinject_pres_has_type; eauto.
    + generalize (RSINJ Asm.RA). intros. 
      eapply vinject_pres_has_type; eauto.
    + generalize (RSINJ Asm.RSP). intros. 
      eapply vinject_pres_not_vundef; eauto.
    + generalize (RSINJ Asm.RA). intros. 
      eapply vinject_pres_not_vundef; eauto.
    + intros FSTEP. eexists. split. apply FSTEP.
      eapply match_states_intro with (j := j'); eauto.
      * eapply (inject_pres_match_sminj j); eauto.
      * eapply (inject_pres_globs_inj_into_flatmem j); eauto.
      * eapply (inject_pres_valid_instr_offset_is_internal j); eauto.
      * eapply (inject_pres_extfun_entry_is_external j); eauto.
      * eapply (inject_pres_match_find_funct j); eauto.
      * assert (regset_inject j' rs rs'0) by 
            (eapply regset_inject_incr; eauto).
        unfold preg_of. 
        set (dregs := (map Asm.preg_of Conventions1.destroyed_at_call)) in *.
        generalize (undef_regs_pres_inject j' rs rs'0 dregs H4). intros.
        unfold undef_regs. unfold ZF, CF, PF, SF, OF.
        set (rs1 := (Asm.undef_regs dregs rs)) in *.
        set (rs2 := (Asm.undef_regs dregs rs'0)) in *.
        set (cdregs := (CR Asm.ZF :: CR Asm.CF :: CR Asm.PF :: CR Asm.SF :: CR Asm.OF :: nil)) in *.
        generalize (undef_regs_pres_inject j' rs1 rs2 cdregs H8). intros.
        set (rs3 := (Asm.undef_regs cdregs rs1)) in *.
        set (rs4 := (Asm.undef_regs cdregs rs2)) in *.
        generalize (set_pair_pres_inject j' rs3 rs4 res res' 
                                         (Asm.loc_external_result (ef_sig ef))
                                         H9 RESINJ).
        intros.
        apply regset_inject_expand; auto.
        apply regset_inject_expand; auto.
    * eapply extcall_pres_glob_block_valid; eauto.
Qed.        

End PRESERVATION.

End WITHMEMORYMODEL.