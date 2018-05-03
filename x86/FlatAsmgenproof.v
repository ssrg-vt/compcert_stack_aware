(* ******************* *)
(* Author: Yuting Wang *)
(* Date:   Feb 7, 2018 *)
(* ******************* *)

(** Correctness proof for the FlatAsm generation **)

Require Import Coqlib Integers Values Maps AST.
Require Import Memtype Memory.
Require Import Smallstep.
Require Import Asm RawAsm.
Require Import FlatAsm FlatAsmgen.
Require Import Segment.
Require Import Events.
Require Import StackADT.
Require Import Linking Errors.
Require Import Globalenvs FlatAsmGlobenv.
Require Import AsmFacts.

Open Scope Z_scope.

Lemma map_fst_inversion : forall (A B:Type) (l:list (A*B)) a,
  In a (map fst l) -> exists b, In (a, b) l.
Proof.
  induction l; simpl; intros.
  - contradiction.
  - destruct H. 
    + destruct a. simpl in H. subst. eauto.
    + exploit IHl; eauto. intros H0. destruct H0. eauto.
Qed.

Lemma find_symbol_exists_1:
  forall (F V : Type) (p : AST.program F V) (id : ident),
    In id (prog_defs_names p) -> exists b : block, Genv.find_symbol (Genv.globalenv p) id = Some b.
Proof.
  intros F V p id H.
  unfold prog_defs_names in H. apply map_fst_inversion in H. destruct H.
  eapply Genv.find_symbol_exists; eauto.
Qed.


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


Lemma tprog_id_in_seg_lists : forall gmap lmap p dsize csize efsize tp id,
  transl_prog_with_map gmap lmap p dsize csize efsize = OK tp ->
  id = stack_segid \/ id = code_segid \/ id = data_segid \/ id = extfuns_segid ->
  In id (map segid (list_of_segments tp)).
Proof.
  intros gmap lmap p dsize csize efsize tp id H H0.
  monadInv H. unfold list_of_segments in *. simpl in *.
  destruct H0. auto.
  destruct H. auto. destruct H. auto. destruct H. auto. 
Qed.

Lemma update_instr_pres_gmap : forall i cinfo fid,
    ci_map (update_instr_map fid cinfo i) = ci_map cinfo.
Proof.
  intros i. destruct i.
  destruct i; unfold update_instr_map; simpl; intros; subst; auto.
Qed.

Lemma update_instrs_pres_gmap : forall instrs cinfo fid,
    ci_map (update_instrs_map fid cinfo instrs) = ci_map cinfo.
Proof.
  induction instrs; simpl; intros.
  - subst. auto.
  - apply eq_trans with (ci_map (update_instr_map fid cinfo a)).
    eapply IHinstrs; eauto.
    apply update_instr_pres_gmap; auto.
Qed.

Lemma update_funs_map_id_cases : forall defs cinfo cinfo' id b,
    cinfo' = update_funs_map cinfo defs ->
    ci_map cinfo' id = Some b -> (fst b = code_segid \/ (ci_map cinfo id = Some b)).
Proof.
  induction defs; simpl; intros;
    try (subst; simpl in *; auto).
  destruct a. destruct o. destruct g. destruct f.
  exploit IHdefs; eauto. intros. destruct H. auto. 
  match type of H with
  | (ci_map (update_instrs_map _ ?ci _) _ = Some _) =>
    generalize (update_instrs_pres_gmap (Asm.fn_code f) ci i)
  end.
  intros H1. rewrite H1 in H.
  simpl in *.
  unfold update_gid_map in H. destruct peq. subst. inv H.
  unfold code_label. simpl. auto. auto.
  eapply IHdefs; eauto.
  eapply IHdefs; eauto.
  eapply IHdefs; eauto.
Qed.

Lemma update_gvars_map_id_cases : forall defs dinfo dinfo' id b,
    dinfo' = update_gvars_map dinfo defs ->
    di_map dinfo' id = Some b -> (fst b = code_segid \/ (di_map dinfo id = Some b)).
Proof.
Admitted.

Lemma update_extfuns_map_id_cases : forall defs dinfo dinfo' id b,
    dinfo' = update_extfuns_map dinfo defs ->
    di_map dinfo' id = Some b -> (fst b = code_segid \/ (di_map dinfo id = Some b)).
Proof.
Admitted.


Lemma update_map_gmap_range : forall p gmap lmap dsize csize efsize tp,
  update_map p = OK (gmap, lmap, dsize, csize, efsize) ->
  transl_prog_with_map gmap lmap p dsize csize efsize = OK tp ->
  forall id b, gmap id = Some b -> In (fst b) (map segid (list_of_segments tp)).
Proof.
  intros p gmap lmap dsize csize efsize tp UPDATE TRANS id b GMAP.
  monadInv UPDATE.
  set (gvmap := (update_gvars_map {| di_size := 0; di_map := default_gid_map |} (AST.prog_defs p))) in *.
  set (efmap := (update_extfuns_map {| di_size := 0; di_map := di_map gvmap |} (AST.prog_defs p))) in *.
  set (fmap := (update_funs_map {| ci_size := 0; ci_map := di_map efmap; ci_lmap := default_label_map |} (AST.prog_defs p))) in *.
  exploit update_funs_map_id_cases; eauto. intros. destruct H.
  eapply tprog_id_in_seg_lists; eauto.
  exploit update_extfuns_map_id_cases; eauto. intros. destruct H0.
  eapply tprog_id_in_seg_lists; eauto.
  exploit update_gvars_map_id_cases; eauto. intros. destruct H1.
  eapply tprog_id_in_seg_lists; eauto.
  simpl in H1. cbv in H1. inv H1.
Qed.

Lemma transl_fun_gen_valid_code_labels : forall gmap lmap i f f' tp,
  (forall id b, gmap id = Some b -> In (fst b) (map segid (list_of_segments tp))) ->
  transl_fun gmap lmap i f = OK f' -> 
  code_labels_are_valid init_block (length (list_of_segments tp)) (gen_segblocks tp) (fn_code f').
Proof.
  Admitted.
  
  
Lemma code_labels_are_valid_app : forall initb slen sbmap l1 l2,
    code_labels_are_valid initb slen sbmap l1 ->
    code_labels_are_valid initb slen sbmap l2 ->
    code_labels_are_valid initb slen sbmap (l1 ++ l2).
Proof.
  induction l1. intros. simpl. auto.
  intros. simpl.
Admitted.

Lemma code_labels_are_valid_eq_map : forall initb slen sbmap sbmap' l,
    (forall id, sbmap id = sbmap' id) ->
    code_labels_are_valid initb slen sbmap l ->
    code_labels_are_valid initb slen sbmap' l.
Admitted.

Lemma transl_funs_gen_valid_code_labels : forall defs gmap lmap fundefs code tp,
  (forall id b, gmap id = Some b -> In (fst b) (map segid (list_of_segments tp))) ->
  transl_funs gmap lmap defs = OK (fundefs, code) -> 
  code_labels_are_valid init_block (length (list_of_segments tp)) (gen_segblocks tp) code.
Proof.
  induction defs; intros.
  - monadInv H0. red. intros. inv H0.
  - monadInvX H0. subst. destruct g. destruct f. monadInv H0.
    apply code_labels_are_valid_app.
    eapply transl_fun_gen_valid_code_labels; eauto.
    eapply IHdefs; eauto.
    eapply IHdefs; eauto.
    eapply IHdefs; eauto.
    eapply IHdefs; eauto.
Qed.

Lemma acc_segblocks_cases: forall ids b initb initmap s,
  b = (acc_segblocks initb ids initmap s) -> 
  b = (initmap s) \/ segblock_is_valid initb (length ids) b.
Proof.
  induction ids; simpl; intros.
  - auto.
  - destruct ident_eq; subst.
    + right. red. split. apply Ple_refl.
      rewrite Nat.add_comm.
      (* assert ((Datatypes.S (Datatypes.length ids) + Pos.to_nat initb)%nat = *)
      (*         (Datatypes.S (Datatypes.length ids + Pos.to_nat initb))%nat) by omega. *)
      (* rewrite H. apply Plt_Ple_trans with (Pos.of_nat (Datatypes.length ids + Pos.to_nat initb)). *)
      (* apply Plt_Ple_trans with (Pos.of_nat (Pos.to_nat initb)).  *)
      (* rewrite Pos2Nat.id. *)
      admit. 
      (* simpl. destruct ((Datatypes.length ids + Pos.to_nat initb)%nat) eqn:EQ. *)
      (* assert (Pos.to_nat initb = 0%nat) by omega. *)
      (* generalize (Pos2Nat.is_pos initb). omega. *)
      (* assert (Pos.to_nat initb <= Datatypes.S n)%nat by omega. *)
      (* rewrite Nat2Pos.inj_succ. *)
    + exploit (IHids (acc_segblocks (Pos.succ initb) ids initmap s)); eauto.
      intros [ACC | VALID].
      auto. right. unfold segblock_is_valid in *. destruct VALID.
      split. apply Ple_trans with (Pos.succ initb); auto. apply Ple_succ.
      assert ((Pos.to_nat initb + Datatypes.S (Datatypes.length ids))%nat =
              (Pos.to_nat (Pos.succ initb) + Datatypes.length ids)%nat).
      rewrite Pos2Nat.inj_succ. rewrite Nat.add_comm. simpl. omega.
      rewrite H1. auto.
Admitted.

Lemma Plt_le_absurd : forall a b,
  Plt a b -> Ple b a -> False.
Proof.
  intros a b H H0. apply Pos.lt_nle in H. unfold Ple in *.
  contradiction.
Qed.

Lemma acc_segblocks_absurd : forall ids b initb initmap s,
  (forall s, Plt (initmap s) b) -> Plt b initb ->
  b = (acc_segblocks initb ids initmap s) -> False.
Proof.
  intros. apply acc_segblocks_cases in H1. destruct H1.
  - subst. specialize (H s). specialize (Plt_strict (initmap s)).
    congruence.
  - red in H1. destruct H1. generalize (Plt_le_absurd b initb); eauto.
Qed.

Lemma acc_segblocks_valid : forall ids init_block0 initmap sbmap,
    (forall s, Plt (initmap s) init_block0) ->
    sbmap = acc_segblocks init_block0 ids initmap ->
    injective_on_valid_segs init_block0 (length ids) sbmap.
Proof.
  induction ids; intros.
  - simpl in *. subst. red.
    intros s1 s2 EQ VALID.
    red in VALID. rewrite Nat.add_0_r in VALID. rewrite Pos2Nat.id in VALID.
    destruct VALID as [VALID1 VALID2]. exfalso.
    generalize (Plt_le_absurd (initmap s1) init_block0); eauto.
  - simpl in H0. subst. red. intros. repeat destruct ident_eq.
    + subst. auto.
    + red in H1. destruct H1.
      exfalso. eapply (acc_segblocks_absurd ids init_block0 (Psucc init_block0)); eauto.
      apply Pos.lt_succ_r. apply Ple_refl.
    + red in H1. destruct H1.
      exfalso. eapply (acc_segblocks_absurd ids init_block0 (Psucc init_block0)); eauto.
      apply Pos.lt_succ_r. apply Ple_refl.
    + set (sbmap := acc_segblocks (Pos.succ init_block0) ids initmap) in *.
      generalize (IHids (Pos.succ init_block0) initmap sbmap). intros.
      exploit H2; eauto. intros. apply Plt_trans_succ. auto.
      set (b1 := sbmap s1) in *. 
      assert (b1 = sbmap s2) by auto. subst sbmap.
      apply acc_segblocks_cases in H3. destruct H3; auto.
      red in H1. destruct H1. specialize (H s2). rewrite <- H3 in H.
      exfalso. generalize (Plt_le_absurd b1 init_block0); eauto.
Qed.

Lemma gen_segblocks_valid : forall p,
    injective_on_valid_segs init_block (length (list_of_segments p)) (gen_segblocks p).
Proof.
  intros p. set (sbmap := gen_segblocks p) in *. 
  unfold gen_segblocks in *.
  assert (length (list_of_segments p) = length (map segid (list_of_segments p))).
  symmetry. apply list_length_map. rewrite H.
  eapply acc_segblocks_valid; eauto. 
  instantiate (1:=(fun _ : segid_type => undef_seg_block)). intros. simpl. 
  apply Plt_succ. auto.
Qed.


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
    the mappings for segments, global id and labels *)    
Record match_sminj (gm: GID_MAP_TYPE) (lm: LABEL_MAP_TYPE) (mj: meminj) : Type :=
  mk_match_sminj {

      agree_sminj_instr :  forall b b' f ofs ofs' i,
        Genv.find_funct_ptr ge b = Some (Internal f) -> 
        Asm.find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
        mj b = Some (b', ofs') -> 
        exists id i' sid ofs1, 
          Genv.find_instr tge (Vptr b' (Ptrofs.add ofs (Ptrofs.repr ofs'))) = Some i' /\
          Genv.find_symbol ge id = Some b /\
          transl_instr gm lm ofs1 id sid i = OK i';

      agree_sminj_glob : forall id gloc,
          gm id = Some gloc ->
          exists ofs' b b', 
            Genv.find_symbol ge id = Some b /\
            Genv.symbol_address tge gloc Ptrofs.zero = Vptr b' ofs' /\
            mj b = Some (b', Ptrofs.unsigned ofs');

      agree_sminj_lbl : forall id b f l z z',
          Genv.find_symbol ge id = Some b ->
          Genv.find_funct_ptr ge b = Some (Internal f) ->
          label_pos l 0 (Asm.fn_code f) = Some z ->
          lm id l = Some z' ->
          Val.inject mj (Vptr b (Ptrofs.repr z)) (Genv.symbol_address tge (code_label z') Ptrofs.zero);
      
    }.

Definition gid_map_for_undef_syms (gm: GID_MAP_TYPE) :=
  forall id, Genv.find_symbol ge id = None -> gm id = None.


(* Definition globs_inj_into_flatmem (mj:meminj) := True. *)
  (* forall b g b' ofs', *)
  (*   Genv.find_def ge b = Some g ->  *)
  (*   mj b = Some (b', ofs') -> b' = mem_block. *)

(* Definition funs_inj_into_flatmem (mj:meminj) := True. *)
  (* forall b f b' ofs', *)
  (*   Genv.find_funct_ptr ge b = Some f ->  *)
  (*   mj b = Some (b', ofs') -> b' = mem_block. *)

(* Lemma globs_to_funs_inj_into_flatmem : forall (j:meminj), *)
(*     globs_inj_into_flatmem j -> funs_inj_into_flatmem j. *)
(* Proof. *)
(*   unfold globs_inj_into_flatmem, funs_inj_into_flatmem.  *)
(*   unfold Genv.find_funct_ptr. intros. *)
(*   destruct (Genv.find_def ge b) eqn: FDEF; try congruence. *)
(*   destruct g; try congruence.  *)
(*   inv H0. eapply H; eauto. *)
(* Qed. *)


Definition valid_instr_offset_is_internal (mj:meminj) :=
  forall b b' f ofs i ofs',
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    mj b = Some (b', ofs') ->
    Genv.genv_internal_codeblock tge b' = true.    

Definition extfun_entry_is_external (mj:meminj) :=
  forall b b' f ofs,
    Genv.find_funct_ptr ge b = Some (External f) ->
    mj b = Some (b', ofs) ->
    Genv.genv_internal_codeblock tge b' = false.


Definition def_frame_inj m := (flat_frameinj (length (Mem.stack m))).


Lemma store_pres_def_frame_inj : forall chunk m1 b ofs v m1',
    Mem.store chunk m1 b ofs v = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  unfold def_frame_inj. intros.
  repeat erewrite Mem.push_new_stage_stack. simpl.
  exploit Mem.store_stack_blocks; eauto. intros. rewrite H0.
  auto.
Qed.

Lemma storev_pres_def_frame_inj : forall chunk m1 v1 v2 m1',
    Mem.storev chunk m1 v1 v2 = Some m1' ->
    def_frame_inj m1= def_frame_inj m1'.
Proof.
  intros until m1'. unfold Mem.storev.
  destruct v1; try congruence.
  intros STORE.
  eapply store_pres_def_frame_inj; eauto.
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
  eexists. split. eauto.
  erewrite <- store_pres_def_frame_inj; eauto.
Qed.

Theorem storev_mapped_inject':
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  Mem.inject f (def_frame_inj m1) m1 m2 ->
  Mem.storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    Mem.storev chunk m2 a2 v2 = Some n2 /\ Mem.inject f (def_frame_inj n1) n1 n2.
Proof.
  intros. exploit Mem.storev_mapped_inject; eauto. 
  intros (n2 & STORE & MINJ).
  eexists. split. eauto.
  erewrite <- storev_pres_def_frame_inj; eauto.
Qed.

Definition match_find_funct (j:meminj) :=
  forall b f ofs b',
  Genv.find_funct_ptr ge b = Some (External f) ->
  j b = Some (b', ofs) ->
  Genv.find_funct tge (Vptr b' (Ptrofs.repr ofs)) = Some (External f).

Definition glob_block_valid (m:mem) := 
  forall b g, Genv.find_def ge b = Some g -> Mem.valid_block m b.

Inductive match_states: state -> state -> Prop :=
| match_states_intro: forall (j:meminj) (rs: regset) (m: mem) (rs': regset) (m':mem)
                        (gm: GID_MAP_TYPE) (lm: LABEL_MAP_TYPE)
                        (MINJ: Mem.inject j (def_frame_inj m) m m')
                        (MATCHSMINJ: match_sminj gm lm j)
                        (* (GINJFLATMEM: globs_inj_into_flatmem j) *)
                        (INSTRINTERNAL: valid_instr_offset_is_internal j)
                        (EXTEXTERNAL: extfun_entry_is_external j)
                        (MATCHFINDFUNCT: match_find_funct j)
                        (RSINJ: regset_inject j rs rs')
                        (GBVALID: glob_block_valid m)
                        (GMUNDEF: gid_map_for_undef_syms gm),
    match_states (State rs m) (State rs' m').


(* Definition seglabel_to_ptr (slbl: seglabel) (stob : segid_type -> block) : (block * Z) := *)
(*   let (sid, ofs) := slbl in *)
(*   (stob sid, Ptrofs.unsigned ofs). *)

Definition init_meminj (gmap: GID_MAP_TYPE) : meminj :=
  let ge := Genv.globalenv prog in
  let tge := globalenv tprog in
  fun b => 
    (* (genv_next ge) is the stack block of the source program *)
    if eq_block b (Genv.genv_next ge) 
    then Some (FlatAsm.stack_block, 0)
    else
      match (Genv.invert_symbol ge b) with
      | None => None
      | Some id => 
        match (gmap id) with
        | None => None
        | Some slbl => Some (Genv.symbol_block_offset tge slbl)
        end
      end.


Lemma genv_next_find_funct_ptr_absurd : forall {F V} (p:AST.program F V) m ge gdef,
  Genv.init_mem p = Some m -> ge = (Genv.globalenv p) -> 
  Genv.find_funct_ptr ge (Genv.genv_next ge) = Some gdef -> False.
Proof.
  intros F V p m ge0 gdef INITM GE FINDPTR. subst ge0.
  exploit Genv.find_funct_ptr_not_fresh; eauto. intros BVALID.
  erewrite Genv.init_mem_genv_next in BVALID; eauto.
  unfold Mem.valid_block in BVALID. apply Plt_strict in BVALID. contradiction.
Qed.

Lemma transl_instr_segblock : forall gmap lmap ofs' id i i' sid,
      transl_instr gmap lmap (Ptrofs.unsigned ofs') id sid i = OK i' ->
      segblock_to_label (snd i') = (sid, ofs').
Proof.
  intros. monadInv H. unfold segblock_to_label. simpl.
  rewrite Ptrofs.repr_unsigned. auto.
Qed.

Lemma find_instr_ofs_non_negative : forall code ofs i,
    find_instr ofs code = Some i -> ofs >= 0.
Proof.
  induction code; simpl; intros.
  - inv H.
  - destruct zeq. omega.
    apply IHcode in H. generalize (instr_size_positive a). omega.
Qed.

Lemma transl_instrs_ofs_bound: forall code code' gmap lmap id sid ofs fofs,
  transl_instrs gmap lmap id sid ofs code = OK (fofs, code') -> ofs <= fofs.
Proof.
  induction code; simpl; intros.
  - inv H. omega.
  - monadInv H. apply IHcode in EQ1. 
    generalize (instr_size_positive a). unfold instr_size. omega.
Qed.

Lemma find_instr_transl_instrs : forall code gmap lmap id sid i ofs ofs' fofs code',
    find_instr (Ptrofs.unsigned ofs) code = Some i ->
    transl_instrs gmap lmap id sid (Ptrofs.unsigned ofs') code = OK (fofs, code') ->
    fofs <= Ptrofs.max_unsigned ->
    exists i' ofs1, transl_instr gmap lmap ofs1 id sid i = OK i' 
               /\ segblock_to_label (snd i') = (sid, Ptrofs.add ofs ofs')
               /\ In i' code'.
Proof.
  induction code; simpl; intros.
  - inv H.
  - monadInv H0. destruct zeq.
    + inv H. eexists; eexists; split; eauto.
      rewrite <- (Ptrofs.repr_unsigned ofs). rewrite e. rewrite Ptrofs.add_zero_l. split.
      eapply transl_instr_segblock; eauto. apply in_eq.
    + exploit (IHcode gmap lmap id sid i 
                      (Ptrofs.repr (Ptrofs.unsigned ofs - instr_size a))
                      (Ptrofs.repr (Ptrofs.unsigned ofs' + si_size (snd a)))); eauto.
      rewrite Ptrofs.unsigned_repr. auto. 
      generalize (find_instr_ofs_non_negative code (Ptrofs.unsigned ofs - instr_size a) i H).
      generalize (instr_size_positive a).
      generalize (Ptrofs.unsigned_range_2 ofs). intros. omega.
      rewrite Ptrofs.unsigned_repr. eauto. 
      generalize (transl_instrs_ofs_bound code x1 gmap lmap id sid
                                          (Ptrofs.unsigned ofs' + si_size (snd a)) fofs EQ1).
      generalize (Ptrofs.unsigned_range_2 ofs'). 
      generalize (instr_size_positive a). unfold instr_size. omega.
      intros (i' & ofs1 & TRANSI & SBEQ & IN).
      eexists; eexists; split. eauto. split.
      rewrite SBEQ. f_equal.
      unfold instr_size.
      rewrite Ptrofs.add_unsigned. repeat rewrite Ptrofs.unsigned_repr.
      replace (Ptrofs.unsigned ofs - si_size (snd a) + (Ptrofs.unsigned ofs' + si_size (snd a))) with
              (Ptrofs.unsigned ofs + Ptrofs.unsigned ofs') by omega.
      rewrite <- Ptrofs.add_unsigned. auto.
      generalize (transl_instrs_ofs_bound code x1 gmap lmap id sid
                                          (Ptrofs.unsigned ofs' + si_size (snd a)) fofs EQ1).
      generalize (Ptrofs.unsigned_range_2 ofs'). 
      generalize (instr_size_positive a). unfold instr_size. omega.
      generalize (find_instr_ofs_non_negative code (Ptrofs.unsigned ofs - instr_size a) i H).
      generalize (instr_size_positive a).
      generalize (Ptrofs.unsigned_range_2 ofs). unfold instr_size. intros. omega.
      apply in_cons. auto.
Qed.

Lemma find_instr_transl_fun : forall id f f' ofs i gmap lmap s,
    find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    transl_fun gmap lmap id f = OK f' ->
    gmap id = Some s ->
    exists i' ofs1, transl_instr gmap lmap ofs1 id (fst s) i = OK i' 
               /\ segblock_to_label (snd i') = (fst s, Ptrofs.add ofs (snd s))
               /\ In i' (fn_code f').
Proof.
  intros id f f' ofs i gmap lmap s FINSTR TRANSFUN GMAP.
  unfold transl_fun in TRANSFUN. rewrite GMAP in TRANSFUN.
  monadInvX TRANSFUN. destruct zle; inversion EQ1; clear EQ1.
  exploit find_instr_transl_instrs; eauto.
Qed.

Lemma transl_fun_exists : forall gmap lmap defs gfuns code f id,
    transl_funs gmap lmap defs = OK (gfuns, code) ->
    In (id, Some (Gfun (Internal f))) defs ->
    exists f', transl_fun gmap lmap id f = OK f'
          /\ forall i, In i (fn_code f') -> In i code.
Proof.
  induction defs; simpl; intros.
  - contradiction.
  - destruct a. destruct H0.
    + inv H0. monadInv H. eexists; split; eauto.
      intros. rewrite in_app. auto.
    + destruct o. destruct g. destruct f0.
      monadInv H. 
      exploit IHdefs; eauto. 
      intros (f' & TRANSLF & IN). eexists; split; eauto.
      intros. rewrite in_app. auto.
      exploit IHdefs; eauto. 
      exploit IHdefs; eauto. 
      exploit IHdefs; eauto. 
Qed.

Lemma target_code_labels_are_valid : 
  code_labels_are_valid 
    init_block (length (list_of_segments tprog)) 
    (Genv.genv_segblocks tge)
    (snd (code_seg tprog)).
Proof.
  unfold match_prog in TRANSF. monadInv TRANSF.
  destruct x. destruct p. destruct p. destruct p.
  subst tge. 
  eapply code_labels_are_valid_eq_map. intros.
  symmetry. apply genv_gen_segblocks.
  monadInv EQ0.
  eapply transl_funs_gen_valid_code_labels; eauto.
  eapply update_map_gmap_range; eauto.
  unfold transl_prog_with_map. rewrite EQ1.
  simpl. rewrite EQ0. simpl. rewrite EQ2. simpl. auto.
Qed.

Lemma find_instr_self : forall i, 
    code_labels_are_distinct (snd (code_seg tprog)) ->
    In i (snd (code_seg tprog)) ->
    Genv.find_instr tge 
                    (Vptr (Genv.genv_segblocks tge (segblock_id (snd i))) (segblock_start (snd i))) = Some i.
Proof.
  intros i DLBL IN. subst tge.
  unfold Genv.find_instr. unfold globalenv.
  erewrite <- add_globals_pres_genv_instrs; eauto. simpl.
  erewrite <- add_globals_pres_genv_segblocks; eauto. simpl.
  set (sbmap := (gen_segblocks tprog)).
  unfold gen_instrs_map.
  set (code := (snd (code_seg tprog))) in *.
  eapply acc_instrs_map_self; eauto.
  apply gen_segblocks_valid.
  set (tge := globalenv tprog).
  subst sbmap code.
  apply code_labels_are_valid_eq_map with (Genv.genv_segblocks tge).
  apply genv_gen_segblocks.
  apply target_code_labels_are_valid.
Qed.

Lemma genv_find_symbol_next_abusrd: forall id, 
    Genv.find_symbol ge id = Some (Genv.genv_next ge) -> False.
Proof. 
  intros id FIND. 
  unfold Genv.find_symbol in FIND. 
  apply Genv.genv_symb_range in FIND.
  generalize (Plt_strict (Genv.genv_next ge)). 
  congruence.
Qed.

Lemma update_funs_map_id : forall defs cinfo id slbl,
    ci_map (update_funs_map cinfo defs) id = Some slbl ->
    (ci_map cinfo id = Some slbl \/ In id (map fst defs)).
Proof.
  induction defs; simpl; intros.
  - auto.
  - destruct a. destruct o. destruct g. destruct f.
    + exploit IHdefs; eauto. intros H0. destruct H0.
      match type of H0 with
      | (ci_map (update_instrs_map _ ?ci _) _ = Some _) =>
        generalize (update_instrs_pres_gmap (Asm.fn_code f) ci i)
      end.
      intros H1. rewrite H1 in H0. simpl in H0.
      unfold update_gid_map in H0. destruct peq. subst.
      inv H0. auto. auto. auto.
    + exploit IHdefs; eauto. intros H0. destruct H0; auto.
    + exploit IHdefs; eauto. intros H0. destruct H0; auto.
    + exploit IHdefs; eauto. intros H0. destruct H0; auto.
Qed.


Lemma update_exfuns_map_id : forall defs dinfo id slbl,
    di_map (update_extfuns_map dinfo defs) id = Some slbl ->
    (di_map dinfo id = Some slbl \/ In id (map fst defs)).
Proof.
  induction defs; simpl; intros.
  - auto.
  - destruct a. destruct o. destruct g. destruct f.
    + exploit IHdefs; eauto. intros H0. destruct H0; auto.
    + exploit IHdefs; eauto. intros H0. destruct H0; auto.
      simpl in H0.
      unfold update_gid_map in H0. destruct peq. subst.
      inv H0. auto. auto. 
    + exploit IHdefs; eauto. intros H0. destruct H0; auto.
    + exploit IHdefs; eauto. intros H0. destruct H0; auto.
Qed.
  

Lemma update_gvars_map_id : forall defs dinfo id slbl,
    di_map (update_gvars_map dinfo defs) id = Some slbl ->
    (di_map dinfo id = Some slbl \/ In id (map fst defs)).
Proof.
  induction defs; simpl; intros.
  - auto.
  - destruct a. destruct o. destruct g. destruct f.
    + exploit IHdefs; eauto. intros H0. destruct H0; auto.
    + exploit IHdefs; eauto. intros H0. destruct H0; auto.
    + exploit IHdefs; eauto. intros H0. destruct H0; auto.
      simpl in H0.
      unfold update_gid_map in H0. destruct peq. subst.
      inv H0. auto. auto. 
    + exploit IHdefs; eauto. intros H0. destruct H0; auto.
Qed.

Lemma update_map_gmap_domain : forall gmap lmap dsize csize efsize id slbl, 
    update_map prog = OK (gmap, lmap, dsize, csize, efsize) ->
    gmap id = Some slbl ->
    In id (prog_defs_names prog).
Proof.
  intros gmap lmap dsize csize efsize id slbl H H0.
  monadInv H. 
  exploit update_funs_map_id; eauto. intros H. destruct H; auto.
  exploit update_exfuns_map_id; eauto. intros H1. destruct H1; auto.
  exploit update_gvars_map_id; eauto. intros H2. destruct H2; auto.
  simpl in H2. inv H2.
Qed.


Theorem init_meminj_match_sminj : forall gmap lmap dsize csize efsize m,
    Genv.init_mem prog = Some m ->
    update_map prog = OK (gmap,lmap,dsize,csize,efsize) ->
    transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog ->
    match_sminj gmap lmap (init_meminj gmap).
Proof.   
  intros gmap lmap dsize csize efsize m INITMEM UPDATE TRANS. 
  generalize TRANSF. intros TRANSF'.
  unfold match_prog in TRANSF'. monadInv TRANSF'.
  rewrite UPDATE in EQ. inv EQ. clear EQ0.
  generalize UPDATE. intros UPDATE'.
  unfold update_map in UPDATE. 
  set (dinfo_gvars := update_gvars_map {| di_size := 0; di_map := default_gid_map |} (AST.prog_defs prog)) in *.
  set (dinfo_extfuns := (update_extfuns_map {| di_size := 0; di_map := di_map dinfo_gvars |} (AST.prog_defs prog))) in *.
  set (cinfo_funs := (update_funs_map {| ci_size := 0; ci_map := di_map dinfo_extfuns; ci_lmap := default_label_map |} (AST.prog_defs prog))) in *.
  inv UPDATE. 
  monadInv TRANS.
  rename EQ into TRANSGV. rename EQ1 into TRANSFUN. rename EQ0 into TRANSEF.
  rename x into gvars. rename x0 into gfuns. rename x2 into efuns. rename x1 into code.
  constructor.
  - (* agree_sminj_instr *) 
    intros b b' f ofs ofs' i FPTR FINST INITINJ.
    unfold init_meminj in INITINJ. fold ge in INITINJ.
    destruct (eq_block b (Genv.genv_next ge)); inversion INITINJ. 
    subst ofs' b' b. clear INITINJ.
    + exfalso. eapply genv_next_find_funct_ptr_absurd; eauto. 
    + destruct (Genv.invert_symbol ge b) eqn:INVSYM; inversion H1.
      destruct (ci_map cinfo_funs i0) eqn:CIMAP; inversion H2.
      subst ofs' b'. clear INITINJ H1 H2.
      rewrite Ptrofs.repr_unsigned. rename i0 into id.
      apply Genv.invert_find_symbol in INVSYM.
      exploit (Genv.find_symbol_funct_ptr_inversion prog); eauto.
      intros FINPROG.
      exploit transl_fun_exists; eauto. intros (f' & TRANSLFUN' & INR).
      exploit find_instr_transl_fun; eauto. 
      intros (i' & ofs1 & TRANSINSTR & SEGLBL & IN).
      exists id, i', (fst s), ofs1. split. 
      unfold segblock_to_label in SEGLBL. inversion SEGLBL.
      apply INR in IN.
      apply find_instr_self. admit. subst tprog; simpl. auto.
      split; auto.

  - (* agree_sminj_glob *)
    intros id gloc GMAP.
    assert (In id (prog_defs_names prog)) 
      by (eapply update_map_gmap_domain; eauto).
    exploit find_symbol_exists_1; eauto.
    intros (b & FIND).
    esplit. exists b. esplit. split. auto. split.
    unfold Genv.symbol_address. unfold Genv.label_to_ptr. auto.
    unfold init_meminj.       
    destruct eq_block. exfalso. subst b. eapply genv_find_symbol_next_abusrd; eauto.    
    apply Genv.find_invert_symbol in FIND. subst ge. rewrite FIND. rewrite GMAP.
    unfold Genv.symbol_block_offset. unfold Genv.label_to_block_offset.
    repeat rewrite offset_seglabel_zero. auto.

  - (* agree_sminj_lbl *)
    admit.

    Admitted.

Lemma mem_empty_inject: Mem.inject (fun _ : block => None) (def_frame_inj Mem.empty) Mem.empty Mem.empty.
Proof.
  unfold def_frame_inj. apply Mem.self_inject; auto.
  intros. congruence.
Qed.

Lemma initial_inject: (Mem.inject (fun b => None) (def_frame_inj Mem.empty) Mem.empty (fst (Mem.alloc Mem.empty 0 0))).
Proof.
  apply Mem.alloc_right_inject with 
      (m2 := Mem.empty) (lo:=0) (hi:=0) 
      (b2 := snd (Mem.alloc Mem.empty 0 0)).
  apply mem_empty_inject. 
  destruct (Mem.alloc Mem.empty 0 0). simpl. auto.
Qed.

Lemma alloc_segments_inject: forall sl f g m m',
    Mem.inject f g m m' ->
    Mem.inject f g m (alloc_segments m' sl).
Proof.
  induction sl; simpl; intros.
  - auto.
  - destruct (Mem.alloc m' 0 (Ptrofs.unsigned (segsize a))) eqn:ALLOC.
    exploit Mem.alloc_right_inject; eauto.
Qed.

(* Lemma alloc_globvar_inject : forall gmap gvar1 gvar2 j m1 m2 m1' smap gdef1 gdef2 sb id, *)
(*     transl_gvar gmap gvar1 = OK gvar2 -> *)
(*     Mem.inject j (def_frame_inj m1) m1 m1' -> *)
(*     Genv.alloc_global ge m1 (id, Some gdef1) = Some m2 -> *)
(*     exists j' m2', alloc_global tge smap m1' (id, Some gdef2, sb) = Some m2'  *)
(*               /\ Mem.inject j' (def_frame_inj m2) m2 m2'. *)

Lemma alloc_global_inject : forall j m1 m2 m1' smap gdef1 gdef2 sb id,
    Mem.inject j (def_frame_inj m1) m1 m1' ->
    Genv.alloc_global ge m1 (id, Some gdef1) = Some m2 ->
    exists j' m2', alloc_global tge smap m1' (id, Some gdef2, sb) = Some m2' 
              /\ Mem.inject j' (def_frame_inj m2) m2 m2'.
Proof.
  intros. destruct gdef1. destruct f. simpl in H0.
  Admitted.


Lemma alloc_globals_inject : forall j m1 m2 m1' smap gdefs1 gdefs2,
    Mem.inject j (def_frame_inj m1) m1 m1' ->
    Genv.alloc_globals ge m1 gdefs1 = Some m2 ->
    exists j' m2', alloc_globals tge smap m1' gdefs2 = Some m2' 
           /\ Mem.inject j' (def_frame_inj m2) m2 m2'.
Admitted.

Lemma init_mem_pres : forall m, 
    Genv.init_mem prog = Some m -> 
    exists m' j, init_mem tprog = Some m' /\ Mem.inject j (def_frame_inj m) m m'. 
Proof. 
  unfold Genv.init_mem, init_mem. intros m H.
  generalize initial_inject. intros INITINJ.
  destruct (Mem.alloc Mem.empty 0 0) eqn:IALLOC. simpl in INITINJ.
  exploit (alloc_segments_inject (list_of_segments tprog) (fun _ => None)); eauto.
  intros SINJ.
  set (m1 := alloc_segments m0 (list_of_segments tprog)) in *.
  exploit (alloc_globals_inject (fun _ => None) Mem.empty m m1 (gen_segblocks tprog) (AST.prog_defs prog) (prog_defs tprog)); eauto.
  intros (j' & m2' & ALLOC & GINJ).
  eexists; eexists; eauto.
Qed.

Lemma transf_initial_states : forall st1,
    RawAsm.initial_state prog (Pregmap.init Vundef) st1  ->
    exists st2, FlatAsm.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  (* intros st1 INIT. *)
  (* generalize TRANSF. intros TRANSF'.  *)
  (* unfold match_prog in TRANSF'. monadInv TRANSF'. *)
  (* rename x into gmap. rename x0 into lmap. *)
  (* inv INIT. inv H0. *)
  (* set (rs0' := *)
  (*       (Asm.Pregmap.init Vundef) *)
  (*       # PC <- (get_main_fun_ptr tge tprog) *)
  (*       # RA <- Vnullptr *)
  (*       # RSP <- (init_rsp tge tprog)). *)
  (* exploit init_mem_pres; eauto. intros (m' & INITM'). *)
  (* eexists. split.  *)
  (* - econstructor; eauto.  *)
  (*   + admit. *)
  (*   + admit. *)
  Admitted.


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
      intros (ofs' & b0 & b' & FSYM & GLOFS & JB).
      unfold Senv.find_symbol in FINDSYM. simpl in FINDSYM. rewrite FSYM in FINDSYM; inv FINDSYM.
      exploit Mem.loadv_inject; eauto.
      intros (varg' & LOADV & VARGINJ).
      exists varg'. split; auto.
      eapply FlatAsmBuiltin.eval_BA_loadglobal.       
      exploit Genv.symbol_address_offset; eauto. intros SYMADDR.
      rewrite SYMADDR. rewrite Ptrofs.repr_unsigned in *.
      rewrite Ptrofs.add_commut. auto.
    + simpl in H10. congruence.
  - monadInvX H4. unfold Senv.symbol_address.
    destruct (Senv.find_symbol ge id) eqn:FINDSYM.
    + inv H. exploit agree_sminj_glob0; eauto. 
      intros (ofs' & b0 & b' & FSYM & GLOFS & JB).
      unfold Senv.find_symbol in FINDSYM. simpl in FINDSYM. rewrite FSYM in FINDSYM; inv FINDSYM.
      eexists. split. 
      apply FlatAsmBuiltin.eval_BA_addrglobal.
      exploit Genv.symbol_address_offset; eauto. intros SYMADDR.
      rewrite SYMADDR.
      eapply Val.inject_ptr; eauto.
      rewrite Ptrofs.repr_unsigned. rewrite Ptrofs.add_commut. auto.
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
    regset_inject j (nextinstr rs1 sz) (nextinstr rs2 sz).
Proof.
  unfold nextinstr. intros. apply regset_inject_expand; auto.
  apply Val.offset_ptr_inject. auto.
Qed.  

Lemma nextinstr_nf_pres_inject : forall j rs1 rs2 sz,
    regset_inject j rs1 rs2 ->
    regset_inject j (nextinstr_nf rs1 sz) (nextinstr_nf rs2 sz).
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
    eapply (agree_sminj_instr0 b b'); eauto.
    unfold Genv.find_funct_ptr in H2. destruct (Genv.find_def ge b) eqn:FDEF; try congruence.
    exploit H; eauto. intros.
    eapply inject_decr; eauto.
  - 
    exploit agree_sminj_glob0; eauto. 
    intros (ofs' & b0 & b' & FSYM & GLBL & JB).
    eexists; eexists; eexists; eauto.
  - 
    exploit agree_sminj_lbl0; eauto.
Qed.

(* Lemma inject_pres_globs_inj_into_flatmem : forall j j' m1 m2, *)
(*     glob_block_valid m1 -> inject_incr j j' -> inject_separated j j' m1 m2 ->  *)
(*     globs_inj_into_flatmem j -> globs_inj_into_flatmem j'. *)
(* Proof. *)
(*   unfold globs_inj_into_flatmem, glob_block_valid. intros. *)
(*   exploit H; eauto. intros. *)
(*   assert (j b = Some (b', ofs')) by (eapply inject_decr; eauto). *)
(*   eapply H2; eauto. *)
(* Qed. *)


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
    Val.inject j (Globalenvs.Genv.symbol_address ge id ofs) (Genv.symbol_address tge lbl ofs).
Proof.
  unfold Globalenvs.Genv.symbol_address.
  intros.
  destruct (Genv.find_symbol ge id) eqn:FINDSYM; auto.
  inv H. exploit agree_sminj_glob0; eauto.
  intros (ofs' & b0 & b' & FSYM & SBOFS & JB).  
  rewrite FSYM in FINDSYM; inv FINDSYM.
  exploit Genv.symbol_address_offset; eauto. intro SYMADDR. rewrite SYMADDR.
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
  | [  H1 : Globalenvs.Genv.symbol_address _ _ _ = _,
       H2 : Genv.symbol_address _ _ _ = _ |- _ ] =>
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
  destruct a1. destruct base, ofs, const; simpl in *; monadInvX H1; simpl; simpl_goal; auto.
  - apply Val.add_inject; auto. destr_pair_if; repeat apply Val.add_inject; auto.
    apply mul_inject; auto.
  - destr_pair_if;
      try (repeat apply Val.add_inject; auto);
      try (eapply inject_symbol_sectlabel; eauto).
    apply mul_inject; auto.
  - apply Val.add_inject; auto.
  - apply Val.add_inject; auto.
    destruct (Globalenvs.Genv.symbol_address ge i0 i1) eqn:SYMADDR; auto.
    simpl_goal.
    exploit inject_symbol_sectlabel; eauto.
    rewrite SYMADDR. intros. inv H1.
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
      destruct (Val.add (rs1 i1) (Globalenvs.Genv.symbol_address ge i i0)); auto.
      inv_valinj. simpl_goal. congruence.
    + inject_match. apply Val.add_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.add (rs1 i1) (Globalenvs.Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. repeat apply Val.add_inject; auto.
      apply mul_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.add (Val.mul (rs1 i1) (Vint (Int.repr z))) (Globalenvs.Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. repeat apply Val.add_inject; auto.
      apply mul_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.add (Val.mul (rs1 i1) (Vint (Int.repr z))) (Globalenvs.Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
  - inject_match.
    +  destruct (Globalenvs.Genv.symbol_address ge i i0) eqn:EQ; auto.
       unfold Globalenvs.Genv.symbol_address in EQ. destruct (Genv.find_symbol ge i); inv EQ.
    + destr_valinj_left H1; auto. destruct Archi.ptr64; inv H1.
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
    destruct (Globalenvs.Genv.symbol_address ge i0 i1) eqn:EQ; auto.
    unfold Globalenvs.Genv.symbol_address in EQ. destruct (Genv.find_symbol ge i0); inv EQ.
    destruct Archi.ptr64; auto. simpl_goal.
    exploit inject_symbol_sectlabel; eauto. rewrite EQ. unfold Genv.symbol_address, Genv.label_to_ptr.
    auto.
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
      destruct (Val.addl (rs1 i1) (Globalenvs.Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. apply Val.addl_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.addl (rs1 i1) (Globalenvs.Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. repeat apply Val.addl_inject; auto.
      apply mull_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.addl (Val.mull (rs1 i1) (Vlong (Int64.repr z))) (Globalenvs.Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
    + inject_match. repeat apply Val.addl_inject; auto.
      apply mull_inject; auto.
      eapply inject_symbol_sectlabel; eauto.
      destruct (Val.addl (Val.mull (rs1 i1) (Vlong (Int64.repr z))) (Globalenvs.Genv.symbol_address ge i i0)); auto;
      inv_valinj; simpl_goal; congruence.
  - inject_match.
    + destruct (Globalenvs.Genv.symbol_address ge i i0) eqn:EQ; auto.
      unfold Globalenvs.Genv.symbol_address in EQ. destruct (Genv.find_symbol ge i); inv EQ.
      destruct Archi.ptr64; auto. simpl_goal.
      exploit inject_symbol_sectlabel; eauto. rewrite EQ. unfold Genv.symbol_address, Genv.label_to_ptr.
      auto.
    + destr_valinj_left H1; auto; destruct Archi.ptr64; inv H1.
      simpl_goal. eapply Val.inject_ptr; eauto.
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
                          (* (GINJFLATMEM: globs_inj_into_flatmem j) *)
                          (INSTRINTERNAL: valid_instr_offset_is_internal j)
                          (EXTEXTERNAL: extfun_entry_is_external j)
                          (MATCHFINDFUNCT: match_find_funct j)
                          (RSINJ: regset_inject j rs1 rs2)
                          (GBVALID: glob_block_valid m1)
                          (GMUNDEF: gid_map_for_undef_syms gm),
    Asm.exec_load ge chunk m1 a1 rs1 rd sz = Next rs1' m1' ->
    transl_addr_mode gm a1 = OK a2 ->
    exists rs2' m2',
      FlatAsm.exec_load tge chunk m2 a2 rs2 rd sz = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. unfold Asm.exec_load in *.  
  exploit eval_addrmode_inject; eauto. intro EMODINJ. 
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
                         (* (GINJFLATMEM: globs_inj_into_flatmem j) *)
                         (INSTRINTERNAL: valid_instr_offset_is_internal j)
                         (EXTEXTERNAL: extfun_entry_is_external j)
                         (MATCHFINDFUNCT: match_find_funct j)
                         (RSINJ: regset_inject j rs1 rs2)
                         (GBVALID: glob_block_valid m1)
                         (GMUNDEF: gid_map_for_undef_syms gm),
    Asm.exec_store ge chunk m1 a1 rs1 r dregs sz = Next rs1' m1' ->
    transl_addr_mode gm a1 = OK a2 ->
    exists rs2' m2',
      FlatAsm.exec_store tge chunk m2 a2 rs2 r dregs sz = Next rs2' m2' /\
      match_states (State rs1' m1') (State rs2' m2').
Proof.
  intros. unfold Asm.exec_store in *.  
  exploit eval_addrmode_inject; eauto. intro EMODINJ. 
  destruct (Mem.storev chunk m1 (Asm.eval_addrmode ge a1 rs1) (rs1 r)) eqn:MSTORE; try congruence.
  exploit Mem.storev_mapped_inject; eauto. intros (m2' & MSTOREV & MINJ').
  eexists. eexists. split.
  - unfold exec_store. rewrite MSTOREV. auto.
  - inv H. eapply match_states_intro; eauto.
    erewrite <- storev_pres_def_frame_inj; eauto.
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
  | [ H : Asm.exec_instr _ _ _ _ _ _ = Next _ _ |- _ ] =>
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
  val_of_optbool_lessdef eval_testcond_inject Val.offset_ptr_inject: inject_db.

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
  exploit agree_sminj_lbl; eauto. intros. 
  eexists. split.
  unfold goto_label. auto. split; auto.
  repeat apply regset_inject_expand; auto. 
Qed.

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


(** The internal step preserves the invariant *)
Lemma exec_instr_step : forall j rs1 rs2 m1 m2 rs1' m1' gm lm i i' id sid ofs ofs' f b
                        (MINJ: Mem.inject j (def_frame_inj m1) m1 m2)
                        (MATCHSMINJ: match_sminj gm lm j)
                        (* (GINJFLATMEM: globs_inj_into_flatmem j) *)
                        (INSTRINTERNAL: valid_instr_offset_is_internal j)
                        (EXTEXTERNAL: extfun_entry_is_external j)
                        (MATCHFINDFUNCT: match_find_funct j)
                        (RSINJ: regset_inject j rs1 rs2)
                        (GBVALID: glob_block_valid m1)
                        (GMUNDEF: gid_map_for_undef_syms gm),
    rs1 PC = Vptr b ofs ->
    Genv.find_symbol ge id = Some b ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    Asm.find_instr (Ptrofs.unsigned ofs) (Asm.fn_code f) = Some i ->
    RawAsm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
    transl_instr gm lm ofs' id sid i = OK i' ->
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
    unfold Globalenvs.Genv.symbol_address.
    destruct (Genv.find_symbol ge id0) eqn:FINDSYM; auto.
    exploit agree_sminj_glob0; eauto.
    intros (ofs1 & b1 & b' & FSYM & GLBL & JB).
    rewrite FSYM in FINDSYM; inv FINDSYM. 
    rewrite GLBL.
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
    rewrite H in *. inv PC1. inv H.
    eapply agree_sminj_lbl; eauto.

  - (* Pjmp_s *)
    apply regset_inject_expand; auto.
    inversion MATCHSMINJ. 
    exploit (agree_sminj_glob0 symb s0); eauto.
    intros (ofs1 & b1 & b' & FSYM & LBLOFS & JB). 
    unfold Globalenvs.Genv.symbol_address. rewrite FSYM. 
    rewrite LBLOFS. econstructor; eauto.
    simpl_goal. auto.

  - (* Pjcc *)
    unfold Asm.exec_instr in H6; simpl in H6.
    exploit (eval_testcond_inject j c rs1 rs2); eauto.
    intros.
    destr_eval_testcond; try solve_match_states.
    exploit goto_label_inject; eauto. intros (rs2' & GOTO & RINJ' & MINJ').
    exists rs2', m2. split. simpl. rewrite <- H7. auto.
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
    + apply Val.offset_ptr_inject. eauto.
    + exploit (inject_symbol_sectlabel gm lm j symb s0 Ptrofs.zero); eauto. 
      
  - (* Pallocframe *)
    generalize (RSINJ RSP). intros RSPINJ.
    destruct (Mem.storev Mptr m1
                         (Val.offset_ptr
                            (Val.offset_ptr (rs1 RSP)
                                            (Ptrofs.neg (Ptrofs.repr (align (frame_size frame) 8))))
                            ofs_ra) (rs1 RA)) eqn:STORERA; try inv H6.
    exploit (fun a1 a2 =>
               storev_mapped_inject' j Mptr m1 a1 (rs1 RA) m1' m2 a2 (rs2 RA)); eauto with inject_db.
    intros (m2' & STORERA' & MINJ2).
    destruct (rs1 RSP) eqn:RSP1; simpl in *; try congruence.
    inv RSPINJ.
    eexists; eexists.
    (* Find the resulting state *)
    rewrite <- H5 in STORERA'. rewrite STORERA'. split. eauto.
    (* Solve match states *)
    eapply match_states_intro; eauto.
    eapply nextinstr_pres_inject; eauto.
    repeat eapply regset_inject_expand; eauto.
    eapply Val.inject_ptr; eauto.
    repeat rewrite (Ptrofs.add_assoc i).
    rewrite (Ptrofs.add_commut (Ptrofs.repr delta)). auto.
    eapply store_pres_glob_block_valid; eauto.

  - (* Pfreeframe *)
    generalize (RSINJ RSP). intros.
    destruct (Mem.loadv Mptr m1 (Val.offset_ptr (rs1 RSP) ofs_ra)) eqn:EQRA; try inv H6.
    exploit (fun g a2 => Mem.loadv_inject j g m1' m2 Mptr (Val.offset_ptr (rs1 Asm.RSP) ofs_ra) a2 v); eauto.
    apply Val.offset_ptr_inject. auto.
    intros (v2 & MLOAD2 & VINJ2).
    eexists; eexists. split. simpl.
    setoid_rewrite MLOAD2. auto.
    eapply match_states_intro; eauto with inject_db.

Qed.


Theorem step_simulation:
  forall S1 t S2,
    RawAsm.step ge S1 t S2 ->
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
    intros (id & i' & sid & ofs1 & FITARG & FSYMB & TRANSL).
    exploit (exec_instr_step j rs rs'0 m m'0 rs' m' gm lm i i' id); eauto.
    intros (rs2' & m2' & FEXEC & MS1).
    exists (State rs2' m2'). split; auto.
    eapply FlatAsm.exec_step_internal; eauto.
        
  - (* Builtin *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H.
    inversion 1; subst.
    exploit (agree_sminj_instr gm lm j MATCHSMINJ b b2 f ofs delta (Asm.Pbuiltin ef args res, sz)); auto.
    intros (id & i' & sid & ofs1 & FITARG & FSYMB & TRANSL).
    (* exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst. *)
    monadInv TRANSL. monadInv EQ.
    set (pbseg := {| segblock_id := sid; segblock_start := Ptrofs.repr ofs1; segblock_size := Ptrofs.repr (si_size sz) |}) in *.
    exploit (eval_builtin_args_inject gm lm j m m'0 rs rs'0 (rs Asm.RSP) (rs'0 Asm.RSP) args vargs x0); auto.
    intros (vargs' & EBARGS & ARGSINJ).
    generalize (external_call_inject j vargs vargs' m m'0 m' vres t ef ARGSINJ MINJ H3).
    intros (j' & vres2 & m2' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
    set (rs' := nextinstr_nf (set_res res vres2 (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs'0)) (segblock_size pbseg)).
    exploit (fun b ofs => FlatAsm.exec_step_builtin tge b ofs
                                       ef x0 res rs'0  m'0 vargs' t vres2 rs' m2' pbseg); eauto. 
    (* unfold valid_instr_offset_is_internal in INSTRINTERNAL. *)
    (* eapply INSTRINTERNAL; eauto. *)
    intros FSTEP. eexists; split; eauto.
    eapply match_states_intro with (j:=j'); eauto.
    (* Supposely the following propreties can proved by separation property of injections *)
    + eapply (inject_pres_match_sminj j); eauto.
    (* + eapply (inject_pres_globs_inj_into_flatmem j); eauto. *)
    + eapply (inject_pres_valid_instr_offset_is_internal j); eauto.
    + eapply (inject_pres_extfun_entry_is_external j); eauto.
    + eapply (inject_pres_match_find_funct j); eauto.
    + subst rs'. intros. subst pbseg; simpl.
      assert (regset_inject j' rs rs'0) by 
          (eapply regset_inject_incr; eauto).
      set (dregs := (map Asm.preg_of (Machregs.destroyed_by_builtin ef))) in *.
      generalize (undef_regs_pres_inject j' rs rs'0 dregs H5). intros.
      set (rs1 := (Asm.undef_regs dregs rs)) in *.
      set (rs2 := (Asm.undef_regs dregs rs'0)) in *.
      generalize (fun h => set_res_pres_inject res j' 
                  rs1 rs2 h vres vres2 RESINJ).
      set (rs3 := (Asm.set_res res vres rs1)) in *.
      set (rs4 := (Asm.set_res res vres2 rs2)) in *.
      intros.
      eauto with inject_db.
    + eapply extcall_pres_glob_block_valid; eauto.

  - (* External call *)
    unfold regset_inject in RSINJ. generalize (RSINJ Asm.PC). rewrite H. 
    inversion 1; subst. rewrite Ptrofs.add_zero_l in H6.
    (* exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst. *)
    generalize (extcall_arguments_inject rs rs'0 m m'0 ef args j H1 MINJ RSINJ).
    intros (args2 & ARGSINJ & EXTCALLARGS).
    exploit (external_call_inject j args args2 m m'0 m' res t ef); eauto.
    intros (j' & res' & m2' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
    exploit (fun ofs => FlatAsm.exec_step_external tge b2 ofs ef args2 res'); eauto.
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
      (* * eapply (inject_pres_globs_inj_into_flatmem j); eauto. *)
      * eapply (inject_pres_valid_instr_offset_is_internal j); eauto.
      * eapply (inject_pres_extfun_entry_is_external j); eauto.
      * eapply (inject_pres_match_find_funct j); eauto.
      * assert (regset_inject j' rs rs'0) by 
            (eapply regset_inject_incr; eauto).
        set (dregs := (map Asm.preg_of Conventions1.destroyed_at_call)) in *.
        generalize (undef_regs_pres_inject j' rs rs'0 dregs H4). intros.
        set (rs1 := (Asm.undef_regs dregs rs)) in *.
        set (rs2 := (Asm.undef_regs dregs rs'0)) in *.
        set (cdregs := (CR Asm.ZF :: CR Asm.CF :: CR Asm.PF :: CR Asm.SF :: CR Asm.OF :: nil)) in *.
        generalize (undef_regs_pres_inject j' rs1 rs2 cdregs). intros.
        set (rs3 := (Asm.undef_regs cdregs rs1)) in *.
        set (rs4 := (Asm.undef_regs cdregs rs2)) in *.
        generalize (set_pair_pres_inject j' rs3 rs4 res res' 
                                         (Asm.loc_external_result (ef_sig ef))).
        intros.
        apply regset_inject_expand; auto.
        apply regset_inject_expand; auto.
    * eapply extcall_pres_glob_block_valid; eauto.
Qed.        

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Asm.final_state st1 r -> FlatAsm.final_state st2 r.
Proof.
  intros st1 st2 r MATCH FINAL.
  inv FINAL. inv MATCH. constructor. 
  - red in RSINJ. generalize (RSINJ PC). rewrite H. 
    unfold Vnullptr. destruct Archi.ptr64; inversion 1; auto.
  - red in RSINJ. generalize (RSINJ RAX). rewrite H0.
    inversion 1. auto.
Qed.
  

Theorem transf_program_correct:
  forward_simulation (RawAsm.semantics prog (Pregmap.init Vundef)) (FlatAsm.semantics tprog).
Proof.
  eapply forward_simulation_step with match_states.
  - simpl. admit.
  - simpl. intros s1 IS. 
    exploit transf_initial_states. eauto. eauto.
  - simpl. intros s1 s2 r MS FS. eapply transf_final_states; eauto.
  - simpl. intros s1 t s1' STEP s2 MS. 
    edestruct step_simulation as (STEP' & MS'); eauto.
Admitted.

End PRESERVATION.


End WITHMEMORYMODEL.