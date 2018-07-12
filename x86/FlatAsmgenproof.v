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
Require Import Num.

Open Scope Z_scope.

Ltac destr_if := 
  match goal with 
  | [ |- context [if ?b then _ else _] ] => 
    let eq := fresh "EQ" in
    (destruct b eqn:eq)
  end.

Ltac destr_match := 
  match goal with 
  | [ |- context [match ?b with _ => _ end] ] => 
    let eq := fresh "EQ" in
    (destruct b eqn:eq)
  end.

Ltac destr_match_in H := 
  match type of H with 
  | context [match ?b with _ => _ end] => 
    let eq := fresh "EQ" in
    (destruct b eqn:eq)
  end.

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


Lemma alignw_le : forall x, x <= align x alignw.
Proof.
  intros x. apply align_le. unfold alignw. omega.
Qed.


Lemma divides_align : forall y x,
    y > 0 -> (y | x) -> align x y = x.
Proof.
  intros y x GT DV.
  unfold align. red in DV. destruct DV as [z DV].
  subst. replace (z * y + y - 1) with (z * y + (y - 1)) by omega.
  erewrite Int.Zdiv_shift; eauto.
  erewrite Z_div_mult; eauto. rewrite Z_mod_mult.
  rewrite zeq_true. rewrite Z.add_0_r. auto.
Qed.

Lemma align_idempotent : forall v x,
    x > 0 -> align (align v x) x = align v x.
Proof.
  intros v x H. eapply divides_align; eauto.
  apply align_divides. auto.
Qed.

Lemma alignw_divides:
  forall z,
    (alignw | align z alignw).
Proof.
  intros. apply align_divides. unfold alignw; omega.
Qed.


(** Lemmas about FlatAsmgen that are useful for proving invariants *)

Lemma transl_fun_exists : forall gmap lmap defs gdefs code f id,
    transl_globdefs gmap lmap defs = OK (gdefs, code) ->
    In (id, Some (Gfun (Internal f))) defs ->
    exists f', transl_fun gmap lmap id f = OK f'
          /\ forall i, In i (fn_code f') -> In i code.
Proof.
  induction defs; simpl; intros.
  - contradiction.
  - destruct a. destruct H0.
    + inv H0. monadInv H. destruct x.
      * destruct p. inv EQ2. monadInv EQ.
        eexists; split; eauto.
        intros. rewrite in_app. auto.
      * monadInv EQ.
    + monadInv H. destruct x.
      * destruct p. inv EQ2. 
        exploit IHdefs; eauto.
        intros (f' & TRANSLF & IN). eexists; split; eauto.
        intros. rewrite in_app. auto.
      * inv EQ2. 
        exploit IHdefs; eauto.
Qed.

Definition size_gvar (def: option (AST.globdef Asm.fundef unit)) : Z :=
  match def with
  | Some (Gvar gv) => init_data_list_size (gvar_init gv)
  | _ => 0
  end.

Definition size_extfun (def: option (AST.globdef Asm.fundef unit)) : Z :=
  match def with
  | Some (Gfun (External ef)) => alignw
  | _ => 0
  end.

Definition size_fun (def: option (AST.globdef Asm.fundef unit)) : Z :=
  match def with
  | Some (Gfun (Internal f)) => code_size (Asm.fn_code f)
  | _ => 0
  end.

Lemma align0: align 0 alignw = 0.
Proof.
  reflexivity.
Qed.

Lemma update_instrs_code_size:
  forall i c lmap csize  lmap' csize'
    (UI : update_instrs lmap csize i c = (lmap', csize')),
    csize' = csize + code_size c.
Proof.
  clear.
  unfold update_instrs.
  induction c; simpl; intros; eauto. inv UI. omega.
  apply IHc in UI. omega.    
Qed.

Lemma update_instrs_other:
  forall i i' l (n: i <> i') c lmap csize lmap' csize'
    (UI : update_instrs lmap csize i c = (lmap', csize')),
    lmap' i' l = lmap i' l.
Proof.
  clear.
  unfold update_instrs.
  induction c; simpl; intros; eauto.
  inv UI; auto.
  destruct (update_instr lmap csize i a) eqn:UI1.
  erewrite IHc. 2: apply UI. clear UI.
  unfold update_instr in UI1. repeat destr_in UI1.
  unfold update_label_map. rewrite peq_false by auto. auto.
Qed.

Lemma align_plus:
  forall a b z,
    (z | a) -> z <> 0 ->
    align (a + b) z = a + align b z.
Proof.
  unfold align.
  intros.
  destruct H. subst.
  replace (x * z + b + z - 1) with ((x * z) + (b + z - 1)) by omega.
  rewrite Z_div_plus_full_l; auto.
  rewrite Z.mul_add_distr_r. reflexivity.
Qed.

Section UPDATE_MAPS.

  Variable gmap: GID_MAP_TYPE.
  Variable lmap: LABEL_MAP_TYPE.
  Variables dsize csize efsize: Z.

  Variable i: ident.
  Variable def: option (globdef Asm.fundef unit).

  Variable gmap': GID_MAP_TYPE.
  Variable lmap': LABEL_MAP_TYPE.
  Variables dsize' csize' efsize': Z.

  Hypothesis UPDATE: update_maps_def gmap lmap dsize csize efsize i def = (gmap', lmap', dsize', csize',efsize').

  Lemma update_gmap:
    forall i',
      gmap' i' = if ident_eq i i'
                 then match def with
                      | None => gmap i
                      | Some (Gfun (Internal f)) => Some (code_label csize)
                      | Some (Gfun (External ef)) => Some (extfun_label efsize)
                      | Some (Gvar gvar) => Some (data_label dsize)
                      end
                 else gmap i'.
  Proof.
    unfold update_maps_def in UPDATE.
    intros. destr.
    unfold update_gid_map in UPDATE.
    repeat destr_in UPDATE; rewrite peq_true; auto.
    unfold update_gid_map in UPDATE.
    repeat destr_in UPDATE; try rewrite peq_false; auto.
  Qed.

  Lemma update_lmap:
    forall i' l,
      lmap' i' l = if ident_eq i i'
                   then match def with
                        | Some (Gfun (Internal f)) =>
                          fst (update_instrs lmap csize i (Asm.fn_code f)) i l
                        | _ => lmap i' l
                        end
                   else lmap i' l.
  Proof.
    unfold update_maps_def in UPDATE.
    intros. destr.
    repeat destr_in UPDATE; auto.
    repeat destr_in UPDATE; auto.
    eapply update_instrs_other; eauto.
  Qed.

  Lemma update_dsize:
    dsize' = dsize + align (size_gvar def) alignw.
  Proof.
    unfold update_maps_def in UPDATE.
    repeat destr_in UPDATE; simpl; rewrite ? align0; omega.
  Qed.

  Lemma update_dsize_mono:
    dsize <= dsize'.
  Proof.
    rewrite update_dsize.
    generalize (alignw_le (size_gvar def)).
    cut (0 <= size_gvar def). omega.
    unfold size_gvar. repeat destr; try omega.
    generalize (init_data_list_size_pos (gvar_init v)); omega.
  Qed.

  Lemma update_efsize:
    efsize' = efsize + size_extfun def.
  Proof.
    unfold update_maps_def in UPDATE.
    repeat destr_in UPDATE; simpl; omega.
  Qed.


  Lemma update_efsize_mono:
    efsize <= efsize'.
  Proof.
    rewrite update_efsize.
    unfold size_extfun. unfold alignw. repeat destr; try omega.
  Qed.

  Lemma update_csize_mono:
    csize <= csize'.
  Proof.
    unfold update_maps_def in UPDATE.
    repeat destr_in UPDATE; simpl; rewrite ? align0; try omega.
    eapply update_instrs_code_size in Heqp; eauto. subst.
    etransitivity. 2: apply alignw_le.
    generalize (code_size_non_neg (Asm.fn_code f0)); omega.
  Qed.

  Hypothesis csize_div: (alignw | csize).

  Lemma update_csize:
    csize' = csize + align (size_fun def) alignw.
  Proof.
    unfold update_maps_def in UPDATE.
    repeat destr_in UPDATE; simpl; rewrite ? align0; try omega.
    eapply update_instrs_code_size in Heqp; eauto. subst.
    rewrite align_plus; auto. unfold alignw. congruence.
  Qed.



    Hypothesis dsize_div: (alignw | dsize).
    Hypothesis efsize_div: (alignw | efsize).

  Lemma update_dsize_div:
    (alignw | dsize').
  Proof.
    rewrite update_dsize.
    apply Z.divide_add_r. auto. apply align_divides. unfold alignw; omega.
  Qed.

  Lemma update_csize_div:
    (alignw | csize').
  Proof.
    rewrite update_csize.
    apply Z.divide_add_r. auto. apply align_divides. unfold alignw; omega.
  Qed.

  Lemma update_efsize_div:
    (alignw | efsize').
  Proof.
    rewrite update_efsize.
    apply Z.divide_add_r. auto.
    unfold size_extfun.
    repeat destr; first [ exists 0; omega | exists 1; omega ].
  Qed.

End UPDATE_MAPS.

Definition sum {A: Type} (f: A -> Z) (l: list A)  :=
  fold_left (fun acc e => acc + f e) l 0.

Lemma fold_left_plus:
  forall {A} f (l: list A) d,
    fold_left (fun acc e => acc + f e) l d = d + sum f l.
Proof.
  unfold sum.
  induction l; simpl; intros. omega.
  rewrite IHl.
  rewrite (IHl (f a)). omega.
Qed.

Definition sizes_gvars (defs: list (ident * option (AST.globdef Asm.fundef unit))) : Z :=
  sum (fun d => align (size_gvar (snd d)) alignw) defs.

Definition sizes_extfuns (defs: list (ident * option (AST.globdef Asm.fundef unit))) : Z :=
  sum (fun d => size_extfun (snd d)) defs.

Definition sizes_funs (defs: list (ident * option (AST.globdef Asm.fundef unit))) : Z :=
  sum (fun d => align (size_fun (snd d)) alignw) defs.

Lemma sum_pos:
  forall {A: Type} f (fpos: forall x, 0 <= f x) (l: list A), 0 <= sum f l.
Proof.
  unfold sum.
  induction l; simpl; intros; eauto. omega.
  rewrite fold_left_plus.
  fold (sum f l) in IHl. specialize (fpos a). omega.
Qed.

Lemma sizes_gvars_pos:
  forall d, 0 <= sizes_gvars d.
Proof.
  apply sum_pos.
  intros.
  etransitivity. 2: apply alignw_le.
  unfold size_gvar. repeat destr; try omega.
  generalize (init_data_list_size_pos (gvar_init v)); omega.
Qed.

Lemma sizes_extfuns_pos:
  forall d, 0 <= sizes_extfuns d.
Proof.
  apply sum_pos.
  intros.
  unfold size_extfun. repeat destr; try omega.
  unfold alignw; omega.
Qed.

Lemma sizes_funs_pos:
  forall d, 0 <= sizes_funs d.
Proof.
  apply sum_pos.
  intros.
  etransitivity. 2: apply alignw_le.
  unfold size_fun. repeat destr; try omega.
  generalize (code_size_non_neg (Asm.fn_code f0)); omega.
Qed.

Section UPDATE_MAPS2.

  Variable defs: list (ident * option (globdef Asm.fundef unit)).

  Variable gmap: GID_MAP_TYPE.
  Variable lmap: LABEL_MAP_TYPE.
  Variables dsize csize efsize: Z.

  Variable gmap': GID_MAP_TYPE.
  Variable lmap': LABEL_MAP_TYPE.
  Variables dsize' csize' efsize': Z.

  Hypothesis UPDATE: update_maps gmap lmap dsize csize efsize defs = (gmap', lmap', dsize', csize',efsize').

  Lemma umind:
    forall (P : GID_MAP_TYPE -> LABEL_MAP_TYPE -> Z -> Z -> Z -> Prop)
      (Pstart: P gmap lmap dsize csize efsize)
      (Pstep: forall g l s c e g' l' s' c' e' i d,
          update_maps_def g l s c e i d = (g', l', s', c', e') ->
          P g l s c e ->
          In (i,d) defs ->
          P g' l' s' c' e'),
      P gmap' lmap' dsize' csize' efsize'.
  Proof.
    intros P Pstart.
    revert defs gmap lmap dsize csize efsize Pstart gmap' lmap' dsize' csize' efsize' UPDATE.
    unfold update_maps.
    induction defs; simpl; intros; eauto.
    inv UPDATE. auto.
    destruct a as [i0 def0]. simpl in *.
    destruct (update_maps_def gmap lmap dsize csize efsize i0 def0) as ((((gmap1 & lmap1) & dsize1) & csize1) & efsize1) eqn:UP1.
    eapply IHl. 2: eauto. eapply Pstep; eauto. eauto.
  Qed.
  

  Lemma update_gmap_not_in:
    forall i,
      ~ In i (map fst defs) ->
      gmap' i = gmap i.
  Proof.
    intros.
    apply (umind (fun g l d c e => g i = gmap i)); auto.
    intros.
    erewrite update_gmap. 2: eauto. rewrite pred_dec_false. auto.
    intro; subst. apply in_map with (f:=fst) in H2. simpl in H2. congruence.
  Qed.

  Lemma update_lmap_not_in:
    forall i l,
      ~ In i (map fst defs) ->
      lmap' i l = lmap i l.
  Proof.
    intros.
    eapply (umind (fun g ll d c e => ll i l = lmap i l)); auto.
    intros.    
    erewrite update_lmap. 2: eauto. rewrite pred_dec_false; auto.
    intro; subst. apply in_map with (f:=fst) in H2. simpl in H2. congruence.
  Qed.

  Definition maps := (GID_MAP_TYPE * LABEL_MAP_TYPE * Z * Z * Z)%type.

  Lemma umind_rel_inv:
    forall (inv: maps -> Prop)
      (INVstart: inv (gmap,lmap,dsize,csize,efsize))
      (INV: forall g l s c e g' l' s' c' e' i d,
          update_maps_def g l s c e i d = (g', l', s', c', e') ->
          inv (g,l,s,c,e) -> inv (g',l',s',c',e'))
      {A: Type} (f: maps -> A) (t: _ -> A -> A)
      (Pstep: forall g l s c e g' l' s' c' e' i d,
          update_maps_def g l s c e i d = (g', l', s', c', e') ->
          In (i,d) defs ->
          inv (g,l,s,c,e) ->
          f (g',l',s',c',e') = t d (f (g,l,s,c,e))),
      fold_left (fun (acc : A) (id : ident * option (globdef Asm.fundef unit)) =>
                   t (snd id) acc) defs (f (gmap,lmap,dsize,csize,efsize))
      = f (gmap',lmap',dsize',csize',efsize').
  Proof.
    intros inv INVstart INV A f t.
    revert defs gmap lmap dsize csize efsize gmap' lmap' dsize' csize' efsize' UPDATE INVstart.
    unfold update_maps.
    induction defs; simpl; intros; eauto.
    inv UPDATE. auto.
    destruct a as [i0 def0]. simpl in *.
    destruct (update_maps_def gmap lmap dsize csize efsize i0 def0) as ((((gmap1 & lmap1) & dsize1) & csize1) & efsize1) eqn:UP1.
    erewrite <- Pstep. 2: eauto. 2: eauto.
    eapply IHl; eauto.
    eauto.
  Qed.

  Lemma umind_rel:
    forall {A: Type} (f: maps -> A) (t: _ -> A -> A)
      (Pstep: forall g l s c e g' l' s' c' e' i d,
          update_maps_def g l s c e i d = (g', l', s', c', e') ->
          In (i,d) defs ->
          f (g',l',s',c',e') = t d (f (g,l,s,c,e))),
      fold_left (fun (acc : A) (id : ident * option (globdef Asm.fundef unit)) =>
                   t (snd id) acc) defs (f (gmap,lmap,dsize,csize,efsize))
      = f (gmap',lmap',dsize',csize',efsize').
  Proof.
    intros.
    eapply umind_rel_inv with (inv := fun _ => True); eauto.
  Qed.


  Lemma umind_inv:
    forall (inv: maps -> Prop)
      (INVstart: inv (gmap,lmap,dsize,csize,efsize))
      (INV: forall g l s c e g' l' s' c' e' i d,
          update_maps_def g l s c e i d = (g', l', s', c', e') ->
          inv (g,l,s,c,e) -> inv (g',l',s',c',e')),
      inv (gmap',lmap',dsize',csize',efsize').
  Proof.
    intros inv INVstart INV.
    revert defs gmap lmap dsize csize efsize gmap' lmap' dsize' csize' efsize' UPDATE INVstart.
    unfold update_maps.
    induction defs; simpl; intros; eauto.
    inv UPDATE. auto.
    destruct a as [i0 def0]. simpl in *.
    destruct (update_maps_def gmap lmap dsize csize efsize i0 def0) as ((((gmap1 & lmap1) & dsize1) & csize1) & efsize1) eqn:UP1.
    eapply IHl; eauto.
  Qed.

  Lemma updates_gmap_in:
    forall i s,
      gmap' i = Some s ->
      In i (map fst defs) \/ gmap i = Some s.
  Proof.
    intros.
    destruct (in_dec peq i (map fst defs)); auto.
    rewrite update_gmap_not_in in H; auto.
  Qed.


  Lemma updates_dsize:
    dsize' = dsize + sizes_gvars defs.
  Proof.
    rewrite <- (umind_rel (fun '(g,l,d,c,e) => d) (fun def d => d + align (size_gvar def) alignw)).
    2: intros; eapply update_dsize; eauto.
    rewrite (fold_left_plus (fun e => align (size_gvar (snd e)) alignw) defs dsize).
    reflexivity.
  Qed.

  Lemma updates_efsize:
    efsize' = efsize + sizes_extfuns defs.
  Proof.
    rewrite <- (umind_rel (fun '(g,l,d,c,e) => e) (fun def e => e + size_extfun def)).
    2: intros; eapply update_efsize; eauto.
    rewrite (fold_left_plus (fun e => size_extfun (snd e)) defs efsize).
    reflexivity.
  Qed.

  Hypothesis csize_div: (alignw | csize).

  Lemma updates_csize:
    csize' = csize + sizes_funs defs.
  Proof.
    erewrite <- (fun pf pf2 => umind_rel_inv (fun '(g,l,d,c,e) => (alignw | c)) pf pf2 (fun '(g,l,d,c,e) => c) (fun def c => c + align (size_fun def) alignw)).
    4: intros; eapply update_csize; eauto.
    rewrite (fold_left_plus (fun e => align (size_fun (snd e)) alignw) defs csize).
    reflexivity. auto.
    intros; eapply update_csize_div; eauto.
  Qed.

  Hypothesis efsize_div: (alignw | efsize).
  Hypothesis dsize_div: (alignw | dsize).

  Lemma updates_dsize_div:
    (alignw | dsize').
  Proof.
    eapply (umind_inv (fun '(g,l,d,c,e) => (alignw | d))); eauto.
    intros; eapply update_dsize_div; eauto.
  Qed.

  Lemma updates_csize_div:
    (alignw | csize').
  Proof.
    eapply (umind_inv (fun '(g,l,d,c,e) => (alignw | c))); eauto.
    intros; eapply update_csize_div; eauto.
  Qed.

  Lemma updates_efsize_div:
    (alignw | efsize').
  Proof.
    eapply (umind_inv (fun '(g,l,d,c,e) => (alignw | e))); eauto.
    intros; eapply update_efsize_div; eauto.
  Qed.

  Lemma csize_mono:
    csize <= csize'.
  Proof.
    rewrite updates_csize.
    generalize (sizes_funs_pos defs); omega.
  Qed.


  Lemma dsize_mono:
    dsize <= dsize'.
  Proof.
    rewrite updates_dsize.
    generalize (sizes_gvars_pos defs); omega.
  Qed.

  Lemma efsize_mono:
    efsize <= efsize'.
  Proof.
    rewrite updates_efsize.
    generalize (sizes_extfuns_pos defs); omega.
  Qed.


End UPDATE_MAPS2.

Lemma update_maps_app:
  forall a b gmap lmap dsize csize efsize,
    update_maps gmap lmap dsize csize efsize (a ++ b) =
    let '(gmap', lmap', dsize', csize', efsize') := update_maps gmap lmap dsize csize efsize a in
    update_maps gmap' lmap' dsize' csize' efsize' b.
Proof.
  unfold update_maps. intros.
  repeat destr.
  rewrite fold_left_app. rewrite Heqp. reflexivity.
Qed.

Theorem update_map_gmap_range : forall p gmap lmap dsize csize efsize,
    make_maps p = (gmap, lmap, dsize, csize, efsize) ->
    forall id slbl, gmap id = Some slbl -> In (fst slbl) (code_segid :: data_segid :: extfuns_segid :: nil).
Proof.
  intros p gmap lmap dsize csize efsize UPDATE.
  pattern gmap,  lmap , dsize , csize , efsize.
  eapply umind. apply UPDATE. unfold default_gid_map. congruence.
  intros.
  erewrite update_gmap in H2; eauto.
  unfold code_label, extfun_label, data_label in H2.
  repeat destr_in H2; eauto; simpl; auto.
Qed.

(** Lemmas for proving agree_sminj_instr

  The key is to prove that 'Genv.find_instr', given the label of an instruction,
  will find the instruction iteself. This relies critically on the following two properties:

  1. The labels attached to the generated code are distinct;
  2. The mapping from segment ids to segment blocks provided by the FlatAsm environment
     are injective when its range is restricted to "valid blocks", i.e.,
     blocks that correspond to valid segments;

  These two properties are establish by lemmas in the following module which in turn lead to
  the key lemma.
 **)
Module AGREE_SMINJ_INSTR.

(* The following sequence of lemmas is used to prove 

   'update_map_gmap_range'

*)

Lemma tprog_id_in_seg_lists : forall gmap lmap p dsize csize efsize tp id,
  transl_prog_with_map gmap lmap p dsize csize efsize = OK tp ->
  id = code_segid \/ id = data_segid \/ id = extfuns_segid ->
  In id (map segid (list_of_segments tp)).
Proof.
  intros gmap lmap p dsize csize efsize tp id H H0.
  monadInv H. unfold list_of_segments in *. simpl in *.
  destruct H0. auto.
  destruct H. auto. destruct H. auto. 
Qed.

(* The mapping from global identifers to segment labels generated by
   'update_map' always maps to valid segment labels
   (i.e., labels that will be mapped into valid segment blocks) *)

Lemma update_maps_cons:
  forall defs i def g l d c e,
    update_maps g l d c e ((i,def)::defs) =
    let '(g1,l1,d1,c1,e1) := update_maps_def g l d c e i def in
    update_maps g1 l1 d1 c1 e1 defs.
Proof.
  unfold update_maps. intros. simpl. repeat destr.
Qed.

Theorem update_map_gmap_range : forall p gmap lmap dsize csize efsize tp,
    make_maps p = (gmap, lmap, dsize, csize, efsize) ->
    transl_prog_with_map gmap lmap p dsize csize efsize = OK tp ->
    forall id slbl, gmap id = Some slbl -> In (fst slbl) (map segid (list_of_segments tp)).
Proof.
  intros p gmap lmap dsize csize efsize tp UPDATE TRANS id b GMAP.
  eapply tprog_id_in_seg_lists; eauto.
  exploit update_map_gmap_range; eauto.
  simpl. intuition.
Qed.


(* The following sequence of lemmas is used to prove 

   'transl_funs_gen_valid_code_labels'

*)

Lemma transl_instrs_gen_valid_code_labels : forall instrs gmap lmap i tp sid ofs1 ofs2 ofs' instrs',
  (forall id b, gmap id = Some b -> In (fst b) (map segid (list_of_segments tp))) ->
  gmap i = Some (sid, ofs1) ->
  transl_instrs gmap lmap i sid ofs2 instrs = OK (ofs', instrs') -> 
  code_labels_are_valid init_block (length (list_of_segments tp)) (gen_segblocks tp) instrs'.
Proof.
  induction instrs; intros.
  - monadInv H1. red. intros. contradiction.
  - monadInv H1.
    assert (code_labels_are_valid init_block (length (list_of_segments tp)) (gen_segblocks tp) x1).
      eapply IHinstrs; eauto.
    apply code_labels_are_valid_cons; auto.
    monadInv EQ. simpl.
    exploit gen_segblocks_in_valid; eauto.
Qed.

Lemma transl_fun_gen_valid_code_labels : forall gmap lmap i f f' tp,
  (forall id b, gmap id = Some b -> In (fst b) (map segid (list_of_segments tp))) ->
  transl_fun gmap lmap i f = OK f' -> 
  code_labels_are_valid init_block (length (list_of_segments tp)) (gen_segblocks tp) (fn_code f').
Proof.
  intros gmap lmap i f f' tp IN TRANSLF.
  monadInvX TRANSLF. destruct zle; try inv EQ2. simpl.
  eapply transl_instrs_gen_valid_code_labels; eauto.
Qed.

(* If the mapping from global identifers to segment labels always maps to valid labels,
   then the code generated by 'transl_funs' using the mapping must also have valid labels *)
Lemma transl_globdefs_gen_valid_code_labels : forall defs gmap lmap tdefs code tp,
  (forall id b, gmap id = Some b -> In (fst b) (map segid (list_of_segments tp))) ->
  transl_globdefs gmap lmap defs = OK (tdefs, code) -> 
  code_labels_are_valid init_block (length (list_of_segments tp)) (gen_segblocks tp) code.
Proof.
  induction defs; intros.
  - monadInv H0. red. intros. inv H0.
  - destruct a. monadInv H0. destruct x. destruct p. destruct o. destruct g.
    destruct f. monadInv EQ. inv EQ2.
    apply code_labels_are_valid_app.
    eapply transl_fun_gen_valid_code_labels; eauto.
    eapply IHdefs; eauto.
    monadInvX EQ. inv EQ2. simpl. eapply IHdefs; eauto.
    monadInvX EQ. inv EQ2. simpl. eapply IHdefs; eauto.
    monadInvX EQ. inv EQ2. simpl. eapply IHdefs; eauto.
Qed.


(**************************)
   
Section WITHTRANSF.

Variable prog: Asm.program.
Variable tprog: FlatAsm.program.
Hypothesis TRANSF: transf_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := globalenv tprog.

(* This lemma makes use of 
   
     'update_map_gmap_range' 

   and 
 
     'transl_funs_gen_valid_code_labels' 

    to prove that the generated instructions have
    valid segment labels attached to them *)
   
Lemma target_code_labels_are_valid : 
  code_labels_are_valid 
    init_block (length (list_of_segments tprog)) 
    (Genv.genv_segblocks tge)
    (snd (code_seg tprog)).
Proof.
  unfold transf_program in TRANSF.
  repeat destr_in TRANSF.
  subst tge. 
  eapply code_labels_are_valid_eq_map. intros.
  symmetry. apply genv_gen_segblocks.
  unfold transl_prog_with_map in H0. monadInv H0. simpl.
  eapply transl_globdefs_gen_valid_code_labels; eauto.
  eapply update_map_gmap_range; eauto.
  unfold transl_prog_with_map. rewrite EQ. simpl. auto.
Qed.

(* The key lemma *)
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
  apply gen_segblocks_injective.
  set (tge := globalenv tprog).
  subst sbmap code.
  apply code_labels_are_valid_eq_map with (Genv.genv_segblocks tge).
  apply genv_gen_segblocks.
  apply target_code_labels_are_valid.
Qed.


(*************
   The following sequence of lemmas shows that if an instruction is 
   in the source program, then it is translated into an instruction
   in the target program at certain location 
 **********)

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
    generalize (instr_size_positive a). omega.
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
                      (Ptrofs.repr (Ptrofs.unsigned ofs' + instr_size a))); eauto.
      rewrite Ptrofs.unsigned_repr. auto. 
      generalize (find_instr_ofs_non_negative code (Ptrofs.unsigned ofs - instr_size a) i H).
      generalize (instr_size_positive a).
      generalize (Ptrofs.unsigned_range_2 ofs). intros. omega.
      rewrite Ptrofs.unsigned_repr. eauto. 
      generalize (transl_instrs_ofs_bound code x1 gmap lmap id sid
                                          (Ptrofs.unsigned ofs' + instr_size a) fofs EQ1).
      generalize (Ptrofs.unsigned_range_2 ofs'). 
      generalize (instr_size_positive a). omega.
      intros (i' & ofs1 & TRANSI & SBEQ & IN).
      eexists; eexists; split. eauto. split.
      rewrite SBEQ. f_equal.
      
      rewrite Ptrofs.add_unsigned. repeat rewrite Ptrofs.unsigned_repr.
      replace (Ptrofs.unsigned ofs - instr_size a + (Ptrofs.unsigned ofs' + instr_size a)) with
              (Ptrofs.unsigned ofs + Ptrofs.unsigned ofs') by omega.
      rewrite <- Ptrofs.add_unsigned. auto.
      generalize (transl_instrs_ofs_bound code x1 gmap lmap id sid
                                          (Ptrofs.unsigned ofs' + instr_size a) fofs EQ1).
      generalize (Ptrofs.unsigned_range_2 ofs'). 
      generalize (instr_size_positive a). omega.
      generalize (find_instr_ofs_non_negative code (Ptrofs.unsigned ofs - instr_size a) i H).
      generalize (instr_size_positive a).
      generalize (Ptrofs.unsigned_range_2 ofs). intros. omega.
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

End WITHTRANSF.

End AGREE_SMINJ_INSTR.


(** Lemmas for proving agree_sminj_glob **)
Module AGREE_SMINJ_GLOB.

Section WITHTRANSF.

Variable prog: Asm.program.
Variable tprog: FlatAsm.program.
Hypothesis TRANSF: transf_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := globalenv tprog.

Lemma lnr_transf: list_norepet (map fst (AST.prog_defs prog)).
Proof.
  unfold transf_program in TRANSF.
  repeat destr_in TRANSF.
  destruct w; auto.
Qed.

Lemma update_map_gmap_domain : forall gmap lmap dsize csize efsize id slbl, 
    make_maps prog = (gmap, lmap, dsize, csize, efsize) ->
    gmap id = Some slbl ->
    In id (prog_defs_names prog).
Proof.
  intros gmap lmap dsize csize efsize id slbl UPDATE GMAP.
  unfold make_maps in UPDATE.
  destruct (updates_gmap_in _ _ _ _ _ _ _ _ _ _ _ UPDATE _ _ GMAP) as [IN | EQ]. 2: inv EQ. auto.
Qed.

End WITHTRANSF.

End AGREE_SMINJ_GLOB.

(** Lemmas for proving agree_sminj_lbl **)
Module AGREE_SMINJ_LBL.

Lemma defs_nodup_labels : forall defs f id,
    defs_no_duplicated_labels defs ->
    In (id, Some (Gfun (Internal f))) defs ->
    list_norepet (labels (Asm.fn_code f)).
Proof.
  intros.
  red in H. rewrite Forall_forall in H.
  exploit H. apply in_map. eauto. simpl. auto.
Qed.

Ltac solve_label_pos_inv := 
  match goal with
  | [ |- _ <> Asm.Plabel _ /\ label_pos _ _ _ = Some _] =>
    split; solve_label_pos_inv
  | [ |- _ <> Asm.Plabel _ ] =>
    unfold not; inversion 1
  | [ |- label_pos _ _ _ = Some _ ] => auto
  | _ => idtac
  end.

Lemma label_pos_inv : forall l ofs a instrs z,
    label_pos l ofs (a :: instrs) = Some z ->
    (a = Asm.Plabel l /\ z = ofs + instr_size a) 
    \/ (a <> Asm.Plabel l /\ label_pos l (ofs + instr_size a) instrs = Some z).
Proof.
  intros l ofs a instrs z H.
  simpl in H. unfold Asm.is_label in H; simpl in H.
  destruct a; try now (right; solve_label_pos_inv).
  destruct peq.
  - subst. left. inv H. auto.
  - right. simpl. split. unfold not. inversion 1. congruence.
    auto.
Qed.

Lemma update_instrs_map_pres_lmap_2 : forall instrs l id lmap lmap' csize csize',
    ~ In (Asm.Plabel l) (instrs) ->
    update_instrs lmap csize id instrs = (lmap',csize') ->
    lmap' id l = lmap id l.
Proof.
  unfold update_instrs.
  induction instrs; simpl; intros; auto.
  - inv H0; auto. 
  - assert (Asm.Plabel l <> a /\ ~ In (Asm.Plabel l) (instrs)) as H1
        by (apply not_in_cons; auto). destruct H1.
    erewrite IHinstrs. 2: auto. 2: eauto.
    destr.
    unfold update_label_map. rewrite peq_true. rewrite peq_false. auto.
    unfold is_label in Heqo. destr_in Heqo.
Qed.


Lemma update_instrs_cons:
  forall lmap csize id ins insns,
    update_instrs lmap csize id (ins::insns) =
    let (lmap',csize') := update_instr lmap csize id ins in
    update_instrs lmap' csize' id insns.
Proof.
  Opaque update_instr.
  unfold update_instrs. simpl. intros.
  destr.
  Transparent update_instr.
Qed.

Lemma update_instrs_other_label:
  forall l id ins lmap csize lmap' csize',
    ~ In l (labels ins) ->
    update_instrs lmap csize id ins = (lmap',csize') ->
    lmap' id l = lmap id l.
Proof.
  induction ins; simpl; intros; eauto. inv H0. auto.
  rewrite update_instrs_cons in H0. destr_in H0.
  unfold update_instr in Heqp.
  repeat destr_in Heqp.
  eapply IHins in H0.
  - rewrite H0. unfold update_label_map. rewrite peq_true, peq_false; auto. simpl in H; auto.
  - simpl in H; auto.
  - eapply IHins in H0; eauto.
Qed.

Lemma update_instrs_map_lmap_inversion : forall instrs csize l z ofs id csize' lmap lmap' l'
    (MAXSIZE: csize' <= Ptrofs.max_unsigned)
    (MINSIZE: csize  >= 0)
    (LNR: list_norepet (labels instrs))
    (LPOS: label_pos l ofs instrs = Some z)
    (UI: update_instrs lmap csize id instrs = (lmap', csize'))
    (LM: lmap' id l = Some l'),
    l' = (code_segid , Ptrofs.repr (csize + z - ofs)) /\ 0 <= (csize + z - ofs) <= Ptrofs.max_unsigned.
Proof.
  induction instrs; simpl; intros; auto.
  - inv LPOS.
  - apply label_pos_inv in LPOS. destruct LPOS as [[LAB EQ] | [NLAB LPOS]].
    + subst. simpl in *. subst. simpl in *.
      rewrite update_instrs_cons in UI. destr_in UI.
      erewrite update_instrs_other_label in LM. 3: eauto. 2: inv LNR; auto.
      unfold update_instr in Heqp. repeat destr_in Heqp.
      unfold is_label in Heqo; repeat destr_in Heqo.
      unfold update_label_map in LM.
      rewrite ! peq_true in LM. inv LM. unfold code_label.
      split.
      f_equal. f_equal. omega.
      rewrite (update_instrs_code_size _ _ _ _ _ _ UI) in MAXSIZE.
      generalize (instr_size_positive (Asm.Plabel l1)).
      generalize (code_size_non_neg instrs). omega.
      unfold is_label in Heqo;  simpl in Heqo; repeat destr_in Heqo.
    + rewrite update_instrs_cons in UI. destr_in UI.
      specialize (IHinstrs z0 l z (ofs + instr_size a) id csize' l0 lmap' l').
      inv Heqp.
      exploit IHinstrs; eauto.
      generalize (instr_size_positive a); omega.
      destr_in LNR; auto. inv LNR; auto.
      intros (A & B).
      rewrite A. split. f_equal. f_equal. omega. omega.
Qed.

Lemma label_pos_min_size : forall instrs l ofs ofs', 
    label_pos l ofs instrs = Some ofs' -> ofs <= ofs'.
Proof.
  induction instrs; intros.
  - simpl in *. inv H.
  - simpl in *. 
    generalize (instr_size_positive a). intros H0.
    repeat destr_in H. omega.
    eapply IHinstrs in H2. omega.
Qed.

Lemma size_fun_pos:
  forall o,
    0 <= size_fun o.
Proof.
  intros.
  unfold size_fun. repeat destr; try omega.
  generalize (code_size_non_neg (Asm.fn_code f0)); omega.
Qed.

Lemma update_funs_map_lpos_inversion: forall defs id l f z gmap lmap csize dsize efsize csize' dsize' efsize' gmap' lmap' l'
    (DDISTINCT : list_norepet (map fst defs)) 
    (LDISTINCT : list_norepet (labels (Asm.fn_code f)))
    (MAXSIZE   : csize' <= Ptrofs.max_unsigned)
    (MINSIZE   : csize >= 0)
    (AL: (alignw | csize)),
    In (id, Some (Gfun (Internal f))) defs ->
    label_pos l 0 (Asm.fn_code f) = Some z ->
    update_maps gmap lmap dsize csize efsize defs = (gmap', lmap', dsize', csize', efsize') -> 
    lmap' id l = Some l' ->
    (exists slbl : seglabel, gmap' id = Some slbl 
                        /\ fst slbl = fst l' 
                        /\ Ptrofs.add (snd slbl) (Ptrofs.repr z) = snd l').
Proof.
  induction defs; intros.
  - contradiction.
  - inv DDISTINCT. inv H.  
    + simpl in *.
      rewrite AGREE_SMINJ_INSTR.update_maps_cons in H1. repeat destr_in H1.
      simpl in Heqp. repeat destr_in Heqp.
      erewrite update_gmap_not_in. 2: eauto. 2: auto.
      unfold update_gid_map. rewrite peq_true. 
      eexists. split. eauto. unfold code_label. simpl.
      erewrite update_lmap_not_in in H2. 3: eauto. 2: auto. 2: auto.
      generalize (csize_mono _ _ _ _ _ _ _ _ _ _ _ H3 (alignw_divides _ )).
      intros.
      exploit update_instrs_map_lmap_inversion. 4: eauto. 4: eauto. 4: eauto.
      generalize (alignw_le z3). omega. omega. auto.
      intros (A & B). subst. simpl. split. auto.
      rewrite Ptrofs.add_unsigned.
      f_equal. rewrite Ptrofs.unsigned_repr. rewrite Ptrofs.unsigned_repr.
      omega.
      assert (0 <= z). eapply (label_pos_min_size (Asm.fn_code f) l 0); eauto.
      omega.
      apply update_instrs_code_size in Heqp0.
      generalize (alignw_le z3).
      subst.
      generalize (code_size_non_neg (Asm.fn_code f)). omega. eauto.
    + destruct a.
      rewrite AGREE_SMINJ_INSTR.update_maps_cons in H1. repeat destr_in H1.
      assert (i <> id).
      {
        simpl in *.
        apply in_map with (f:=fst) in H3; simpl in *. congruence.
      }
      eapply IHdefs; auto. eauto. 4: auto. 4: eauto. 4: eauto. auto. 3: auto.
      erewrite update_csize with (csize':=z1). 2: eauto.
      generalize (alignw_le (size_fun o)) (size_fun_pos o); omega.
      auto.
      eapply update_csize_div; eauto.
Qed.

Section WITHTRANSF.

Variable prog: Asm.program.
Variable tprog: FlatAsm.program.
Hypothesis TRANSF: transf_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := globalenv tprog.

Lemma update_map_lmap_inversion : forall id f gmap lmap dsize csize efsize l z l',
    (dsize + csize + efsize) <= Ptrofs.max_unsigned ->
    list_norepet (map fst (AST.prog_defs prog)) ->
    list_norepet (labels (Asm.fn_code f)) ->
    In (id, Some (Gfun (Internal f))) (AST.prog_defs prog) ->
    make_maps prog = (gmap, lmap, dsize, csize, efsize) ->
    label_pos l 0 (Asm.fn_code f) = Some z ->
    lmap id l = Some l' ->
    exists slbl, gmap id = Some slbl /\
            fst slbl = fst l' /\
            Ptrofs.add (snd slbl) (Ptrofs.repr z) = snd l'.
Proof.
  intros id f gmap lmap dsize csize efsize l z l' SZBOUND DDISTINCT LDISTINCT IN UPDATE LPOS LMAP.
  unfold make_maps in UPDATE.
  eapply update_funs_map_lpos_inversion. 8: eauto. all: eauto.
  generalize (dsize_mono _  _ _ _ _ _ _ _ _ _ _ UPDATE).
  generalize (efsize_mono _ _ _ _ _ _ _ _ _ _ _ UPDATE). omega. omega.
  apply Z.divide_0_r.
Qed.

End WITHTRANSF.

End AGREE_SMINJ_LBL.

Section WITHMEMORYMODEL.
  
Context `{memory_model: Mem.MemoryModel }.
Existing Instance inject_perm_all.


Lemma store_init_data_perm : forall ge m m' b b' p i q k prm,
  store_init_data ge m b p i = Some m' -> Mem.perm m' b' q k prm <-> Mem.perm m b' q k prm.
Proof.
  intros ge m m' b b' p i q k prm H.
  unfold store_init_data in H. destruct i; try now (eapply store_perm; eauto).
  inv H. split; auto.
Qed.

Lemma store_init_data_list_perm : forall idl ge m m' b p  b' q k prm,
  store_init_data_list ge m b p idl = Some m' -> Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm.
Proof.
  induction idl; intros.
  - inv H. split; auto.
  - inv H. destr_match_in H1.
    + erewrite <- store_init_data_perm; eauto.
    + inv H1.
Qed.

Lemma store_init_data_stack : forall v ge (m m' : mem) (b : block) (ofs : Z),
       store_init_data ge m b ofs v = Some m' -> Mem.stack m' = Mem.stack m.
Proof.
  intros v ge0 m m' b ofs H. destruct v; simpl in *; try (now eapply Mem.store_stack_blocks; eauto).
  inv H. auto.
Qed.

Lemma store_init_data_list_stack : forall l ge (m m' : mem) (b : block) (ofs : Z),
       store_init_data_list ge m b ofs l = Some m' -> Mem.stack m' = Mem.stack m.
Proof.
  induction l; intros.
  - simpl in H. inv H. auto.
  - simpl in H. destr_match_in H; inv H.
    exploit store_init_data_stack; eauto.
    exploit IHl; eauto.
    intros. congruence.
Qed.

Lemma alloc_global_stack : forall ge smap m def m',
    alloc_global ge smap m def = Some m' ->
    Mem.stack m' = Mem.stack m.
Proof.
  intros ge0 smap m def m' H. 
  destruct def. destruct p. destruct o. destruct g. destruct f.
  - simpl in H. exploit Mem.drop_perm_stack; eauto.
  - simpl in H. exploit Mem.drop_perm_stack; eauto.
  - simpl in H. destr_match_in H; inv H. destr_match_in H1; inv H1.
    exploit Genv.store_zeros_stack; eauto.
    exploit store_init_data_list_stack; eauto.
    exploit Mem.drop_perm_stack; eauto. intros. congruence.
  - simpl in H. inv H. auto.
Qed.

Lemma alloc_globals_stack : forall l ge smap m m',
    alloc_globals ge smap m l = Some m' ->
    Mem.stack m' = Mem.stack m.
Proof. 
  induction l; intros.
  - simpl in H. inv H. auto.
  - simpl in H. destr_match_in H; inv H.
    exploit alloc_global_stack; eauto. intros.
    exploit IHl; eauto. intros. congruence.
Qed.

Lemma alloc_segments_perm_ofs : forall segs m1 m2
                                  (ALLOCSEGS : alloc_segments m1 segs = m2)
                                  (PERMOFS : forall b ofs k p, Mem.perm m1 b ofs k p -> 0 <= ofs < Ptrofs.max_unsigned),
    (forall b ofs k p, Mem.perm m2 b ofs k p -> 0 <= ofs < Ptrofs.max_unsigned).
Proof.
  induction segs. intros.
  - subst. simpl in H. eauto.
  - intros. simpl in ALLOCSEGS.
    destruct (Mem.alloc m1 0 (Ptrofs.unsigned (segsize a))) eqn:ALLOC.
    eapply IHsegs; eauto. 
    intros b1 ofs0 k0 p0 PERM.
    erewrite alloc_perm in PERM; eauto.
    destruct peq. 
    generalize (Ptrofs.unsigned_range_2 (segsize a)). omega.
    eauto.
Qed.

Lemma alloc_segments_stack: forall l m m',
    m' = alloc_segments m l -> Mem.stack m' = Mem.stack m.
Proof.
  induction l; intros.
  - simpl in H. subst. auto.
  - inv H. simpl. destruct (Mem.alloc m 0 (Ptrofs.unsigned (segsize a))) eqn:ALLOC.
    exploit Mem.alloc_stack_blocks; eauto. intros H. rewrite <- H.
    erewrite IHl; eauto.
Qed.

Lemma alloc_segments_nextblock :  forall l m m',
  m' = alloc_segments m l -> Mem.nextblock m' = pos_advance_N (Mem.nextblock m) (length l).
Proof.
  induction l; intros.
  - inv H. simpl. auto.
  - inv H. simpl.
    destruct (Mem.alloc m 0 (Ptrofs.unsigned (segsize a))) eqn:ALLOC.
    erewrite IHl; eauto. exploit Mem.nextblock_alloc; eauto. intros. rewrite H.
    rewrite psucc_advance_Nsucc_eq. auto.
Qed.

Lemma init_mem_stack:
  forall (p: program) m,
    init_mem p = Some m ->
    Mem.stack m = nil.
Proof.
  intros. unfold init_mem in H.
  destruct (Mem.alloc Mem.empty 0 0) eqn:ALLOC.
  exploit Mem.alloc_stack_blocks; eauto. intros.
  exploit alloc_globals_stack; eauto. intros.
  rewrite H1. erewrite alloc_segments_stack; eauto. 
  rewrite Mem.empty_stack in H0. auto.
Qed.

Lemma store_init_data_nextblock : forall v ge m b ofs m',
  store_init_data ge m b ofs v = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros. destruct v; simpl in *; try now (eapply Mem.nextblock_store; eauto).
  inv H. auto.
Qed.
    
Lemma store_init_data_list_nextblock : forall l ge m b ofs m',
  store_init_data_list ge m b ofs l = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction l; intros.
  - inv H. auto.
  - inv H. destr_match_in H1; inv H1.
    exploit store_init_data_nextblock; eauto.
    exploit IHl; eauto. intros. congruence.
Qed.

Remark alloc_global_nextblock:
  forall v ge smap m m',
  alloc_global ge smap m v = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros. destruct v. destruct p. destruct o. destruct g. destruct f.
  - simpl in H. eapply Mem.nextblock_drop; eauto.
  - simpl in H. eapply Mem.nextblock_drop; eauto.
  - simpl in H. destr_match_in H; inv H.
    destr_match_in H1; inv H1.
    exploit Genv.store_zeros_nextblock; eauto.
    exploit store_init_data_list_nextblock; eauto.
    exploit Mem.nextblock_drop; eauto.
    intros. congruence.
  - simpl in H. inv H. auto.
Qed.

Remark alloc_globals_nextblock:
  forall gl ge smap  m m',
  alloc_globals ge smap m gl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction gl; intros.
  - inv H. auto.
  - inv H. destr_match_in H1; inv H1.
    exploit alloc_global_nextblock; eauto.
    exploit IHgl; eauto.
    intros. congruence.
Qed.

Lemma add_global_pres_genv_next : 
  forall def (ge ge' : genv),
  ge' = add_global ge def -> Genv.genv_next ge = Genv.genv_next ge'.
Proof.
  intros. destruct def. destruct p. 
  destruct o. destruct g. destruct f.
  - simpl in *. subst. auto.
  - simpl in *. subst. auto.
  - simpl in *. subst. auto.
  - simpl in *. subst. auto.
Qed.  

Lemma add_globals_pres_genv_next : 
  forall (defs : list (ident * option gdef * segblock)) (ge ge' : genv),
  ge' = add_globals ge defs -> Genv.genv_next ge = Genv.genv_next ge'.
Proof.
  induction defs; intros; simpl in *.
  - subst. auto.
  - exploit IHdefs; eauto. 
    erewrite <- add_global_pres_genv_next; eauto.
Qed.

Lemma init_mem_genv_next: forall p m,
  init_mem p = Some m ->
  Genv.genv_next (globalenv p) = Mem.nextblock m.
Proof.
  unfold init_mem; intros.
  destruct (Mem.alloc Mem.empty 0 0) eqn:ALLOC.
  exploit alloc_globals_nextblock; eauto. 
  exploit Mem.nextblock_alloc; eauto. rewrite Mem.nextblock_empty. intros.
  exploit alloc_segments_nextblock; eauto.
  rewrite <- H1. unfold list_of_segments. simpl. rewrite H0. simpl.
  intros. unfold globalenv. simpl.
  erewrite <- add_globals_pres_genv_next; eauto. simpl. congruence.
Qed.


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

      agree_sminj_lbl : forall id b f l z l',
          Genv.find_symbol ge id = Some b ->
          Genv.find_funct_ptr ge b = Some (Internal f) ->
          label_pos l 0 (Asm.fn_code f) = Some z ->
          lm id l = Some l' ->
          Val.inject mj (Vptr b (Ptrofs.repr z)) (Genv.symbol_address tge l' Ptrofs.zero);
      
    }.

Definition gid_map_for_undef_syms (gm: GID_MAP_TYPE) :=
  forall id, Genv.find_symbol ge id = None -> gm id = None.


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
    if eq_block b (Globalenvs.Genv.genv_next ge) 
    then Some (Genv.genv_next tge, 0)
    else
      match (Genv.invert_symbol ge b) with
      | None => None
      | Some id => 
        match (gmap id) with
        | None => None
        | Some slbl => Some (Genv.symbol_block_offset tge slbl)
        end
      end.

Lemma in_transl_instrs:
  forall gmap lmap i si c o o' sz x1
    (RNG: 0 <= sz <= Ptrofs.max_unsigned)
    (POS: 0 <= o')
    (TI: transl_instrs gmap lmap i si o' c = OK (sz, x1))
    si'
    (IN: In (si', o) (map (fun i1 : instruction * segblock => (segblock_id (snd i1), segblock_start (snd i1))) x1)),
    si' = si /\ o' <= Ptrofs.unsigned o < o' + code_size c.
Proof.
  induction c; simpl; intros; eauto.
  - inv TI. simpl in IN. easy. 
  - monadInv TI. simpl in IN.
    destruct IN as [IN|IN].
    + inv IN. unfold transl_instr in EQ. monadInv EQ. simpl. split; auto.
      rewrite Ptrofs.unsigned_repr.
      generalize (instr_size_positive a) (code_size_non_neg c); omega.
      split. omega.
      generalize (AGREE_SMINJ_INSTR.transl_instrs_ofs_bound _ _ _ _ _ _ _ _ EQ1).
      generalize (instr_size_positive a); omega.
    + generalize (instr_size_positive a); intros.
      eapply IHc in IN. 4: eauto. destruct IN; split; auto. omega. auto. omega.
Qed.


Lemma transl_instrs_diff_labels:
  forall gmap lmap i si c
    (* (lnr : list_norepet (labels c)) *)
    (* (lmap_inj: forall i1 i2 l1 l2 sl1 sl2, (i1,l1) <> (i2,l2) -> lmap i1 l1 = Some sl1 -> lmap i2 l2 = Some sl2 -> *)
    (*                                   sl1 <> sl2) *)
    sz ofs c'
    (RNG: 0 <= sz <= Ptrofs.max_unsigned)
    (POS: 0 <= ofs)
    (TI : transl_instrs gmap lmap i si ofs c = OK (sz, c')),
    list_norepet (map (fun i1 : instruction * segblock => segblock_to_label (snd i1)) c').
Proof.
  induction c; simpl; intros; eauto.
  - inv TI. simpl. constructor.
  - monadInv TI.
    (* trim IHc. *)
    (* { *)
    (*   destr_in lnr. inv lnr; auto. *)
    (* } *)
    (* trim IHc. eauto. *)
    simpl.
    constructor; eauto.
    clear IHc. 
    intro IN.
    unfold transl_instr in EQ. monadInv EQ. simpl in IN.
    unfold segblock_to_label in IN. simpl in IN.
    eapply in_transl_instrs in IN. 4: eauto. 2: auto.
    rewrite Ptrofs.unsigned_repr in IN. 
    generalize (instr_size_positive a). omega. split. auto.
    generalize (AGREE_SMINJ_INSTR.transl_instrs_ofs_bound _ _ _ _ _ _ _ _ EQ1).
    generalize (instr_size_positive a); omega.
    generalize (instr_size_positive a); omega.
    eapply IHc. 3: eauto. auto.
    generalize (instr_size_positive a); omega.
Qed.


Lemma transl_globdef_distinct_code_labels:
  forall gmap lmap i o p c
    (* (GNDL: globdef_no_duplicated_labels o = true) *)
    (TG : transl_globdef gmap lmap i o = OK (Some (p, c))),
    list_norepet (map (fun i0 : instruction * segblock => segblock_to_label (snd i0)) c).
Proof.
  intros.
  unfold transl_globdef in TG.
  repeat destr_in TG.
  - monadInv H0.
    unfold transl_fun in EQ. repeat destr_in EQ.
    monadInv H0. repeat destr_in EQ0.
    simpl. eapply transl_instrs_diff_labels; eauto. split; auto.
    generalize (AGREE_SMINJ_INSTR.transl_instrs_ofs_bound _ _ _ _ _ _ _ _ EQ). generalize (Ptrofs.unsigned_range i0); omega.
    apply Ptrofs.unsigned_range.
  - constructor.
  - monadInv H0. constructor.
Qed.

Lemma transl_globdef_gmap:
  forall gmap lmap i o c,
    transl_globdef gmap lmap i o = OK c ->
    o = None \/ exists s, gmap i = Some s.
Proof.
  intros.
  unfold transl_globdef in H. repeat destr_in H.
  monadInv H1. unfold transl_fun in EQ. destr_in EQ. eauto. eauto. eauto.
Qed.

Lemma transl_globdefs_gmap:
  forall gmap lmap l gdefs c,
    transl_globdefs gmap lmap l = OK (gdefs, c) ->
    Forall (fun '(i,d) => d = None \/ exists s, gmap i = Some s) l.
Proof.
  induction l; simpl; intros.
  constructor.
  destr_in H. monadInv H. subst. constructor; eauto.
  eapply transl_globdef_gmap. eauto.
Qed.


Lemma in_transl_globdef:
  forall gmap lmap i o p0 c
    (EQ : transl_globdef gmap lmap i o = OK (Some (p0, c)))
    x
    (IN: In x (map (fun i0 : instruction * segblock => segblock_to_label (snd i0)) c)),
    exists s,
      gmap i = Some s /\ 
      fst x = fst s /\ Ptrofs.unsigned (snd s) <= Ptrofs.unsigned (snd x) < Ptrofs.unsigned (snd s) + odef_size o.
Proof.
  unfold transl_globdef.
  intros.
  repeat destr_in EQ.
  - monadInv H0. unfold transl_fun in EQ.
    repeat destr_in EQ. eexists; split. eauto. monadInv H0. simpl.
    repeat destr_in EQ0. simpl in *.
    destruct x. simpl in *.
    exploit in_transl_instrs. 3: apply EQ. 3: eauto.
    generalize (AGREE_SMINJ_INSTR.transl_instrs_ofs_bound _ _ _ _ _ _ _ _ EQ). generalize (Ptrofs.unsigned_range i0); omega.
    apply Ptrofs.unsigned_range. auto.
  - easy.
  - monadInv H0. easy.
Qed.

Lemma in_transl_globdefs:
  forall gmap lmap l gdefs code
    (EQ : transl_globdefs gmap lmap l = OK (gdefs, code))
    x
    (IN: In x (map (fun i0 : instruction * segblock => segblock_to_label (snd i0)) code)),
          exists i def s,
            In (i, def) l /\
            gmap i = Some s /\ 
            fst x = fst s /\ Ptrofs.unsigned (snd s) <= Ptrofs.unsigned (snd x) < Ptrofs.unsigned (snd s) + odef_size def.
Proof.
  induction l; simpl; intros; eauto. inv EQ. easy.
  repeat destr_in EQ.
  monadInv H0.
  repeat destr_in EQ2; eauto.
  - specialize (IHl _ _ EQ1).
    rewrite map_app, in_app in IN.
    destruct IN as [IN|IN].
    exploit in_transl_globdef; eauto.
    intros (s & G & FST & RNG).
    exists i, o, s; repeat apply conj; auto; omega.
    exploit IHl; eauto.
    intros (i0 & def & s & INl & G & FST & RNG).
    exists i0, def, s; repeat apply conj; auto; omega.
  - exploit IHl; eauto.
    intros (i0 & def & s & INl & G & FST & RNG).
    exists i0, def, s; repeat apply conj; auto; omega.
Qed.

Definition gmap_inj (gmap: GID_MAP_TYPE) (l: list (ident * option _)): Prop :=
  forall i1 i2 d1 d2 s1 s2 o1 o2,
    In (i1, d1) l ->
    In (i2, d2) l ->
    i1 <> i2 ->
    gmap i1 = Some (s1, o1) ->
    gmap i2 = Some (s2, o2) ->
    s1 <> s2 \/ Ptrofs.unsigned o1 + odef_size d1 <= Ptrofs.unsigned o2 \/ Ptrofs.unsigned o2 + odef_size d2 <= Ptrofs.unsigned o1.

Lemma gmap_inj_inv:
  forall gmap a b,
    gmap_inj gmap (a::b) ->
    gmap_inj gmap b.
Proof.
  unfold gmap_inj; intros; eauto.
  eapply H; simpl; eauto.
Qed.

Ltac ereplace t :=
  match type of t with
  | ?ty => let x := fresh in evar (x : ty); replace t with x; unfold x
  end.

Lemma transl_globdefs_distinct_code_labels:
  forall gmap lmap prog (GINJ: gmap_inj gmap (AST.prog_defs prog)) tgdefs code,
    transl_globdefs gmap lmap (AST.prog_defs prog) = OK (tgdefs, code) ->
    wf_prog prog ->
    code_labels_are_distinct code.
Proof.
  intros gmap lmap prog0 GINJ tgdefs code TG WF. inv WF.
  revert TG GINJ wf_prog_not_empty wf_prog_norepet_defs wf_prog_norepet_labels.
  generalize (AST.prog_defs prog0). intro l.
  intros TG GINJ DNE NDD DNDL.
  red.
  revert l tgdefs code TG GINJ DNE NDD DNDL.
  induction l; simpl; intros; eauto.
  - inv TG. simpl. constructor.
  - inv NDD. inv DNDL. inv DNE. destr_in TG. monadInv TG.
    repeat destr_in EQ2; eauto.
    rewrite map_app. rewrite list_norepet_app.
    repeat apply conj; eauto.
    + eapply transl_globdef_distinct_code_labels; eauto.
    + eapply IHl; eauto using gmap_inj_inv.
    + red.
      intros (sx & ox) (sy & oy) INx INy.
      exploit in_transl_globdef. eauto. eauto.
      simpl. intros (s & G & FST & RNG). subst.
      exploit in_transl_globdefs. eauto. eauto.
      simpl. intros (i0 & def & s' & INl & G' & FST' & RNG'). subst.
      destruct s, s'. simpl in *. intro A; inv A.
      exploit GINJ. left; reflexivity.
      right; eauto.
      intro; subst. apply H1. 
      ereplace i0. apply in_map, INl. reflexivity.
      eauto. eauto. intros [A | A]. congruence. omega.
    + eapply IHl; eauto using gmap_inj_inv.
Qed.

Lemma update_maps_code_lt:
  forall defs g l d c e g' l' d' c' e' i s
    (RNG: 0 <= c <= Ptrofs.max_unsigned)
    (RNG: 0 <= c' <= Ptrofs.max_unsigned)
    (UPDATE: update_maps g l d c e defs = (g', l', d', c', e'))
    (AL: (alignw | c))
    (LNR: list_norepet (map fst defs))
    f
    (IN: In (i, Some (Gfun (Internal f))) defs)
    (* o *)
    (* (POS: 0 <= o < code_size (Asm.fn_code f)) *)
    (BEFORE: g i = None)
    (AFTER: g' i = Some s),
    c <= Ptrofs.unsigned (snd s) /\ Ptrofs.unsigned (snd s) + code_size (Asm.fn_code f) <= c'.
Proof.
  induction defs; simpl; intros; eauto. easy.
  destruct IN.
  - subst.
    rewrite AGREE_SMINJ_INSTR.update_maps_cons in UPDATE. do 4 destr_in UPDATE. subst.
    erewrite update_gmap_not_in in AFTER. 2: eauto. 2: inv LNR; auto.
    erewrite update_gmap in AFTER. 2: eauto.
    rewrite peq_true in AFTER. inv AFTER.
    unfold code_label; simpl.
    rewrite Ptrofs.unsigned_repr; auto.
    exploit update_csize_div. eauto. eauto. intro.
    eapply update_csize in Heqp.
    eapply csize_mono in UPDATE. subst. simpl in UPDATE.
    generalize (alignw_le (code_size (Asm.fn_code f))). omega.
    inv LNR; auto. auto.
  - destruct a. rewrite AGREE_SMINJ_INSTR.update_maps_cons in UPDATE. do 4 destr_in UPDATE. subst.
    exploit update_csize_div; eauto.  intro.
    inv LNR.
    assert (c <= z0). {
      exploit update_csize; eauto. intro; subst.
      generalize (alignw_le (size_fun o)) (AGREE_SMINJ_LBL.size_fun_pos o).
      intros. omega.
    }
    assert (z0 <= c') by (eapply csize_mono; eauto).
    exploit IHdefs. 3: eauto. omega. auto. auto. auto. eauto. eauto. 
    erewrite update_gmap; eauto. rewrite peq_false; auto.
    intro; subst. apply H3.
    apply in_map with (f:= fst) in H. simpl in H; auto. eauto.
    omega.
Qed.

Lemma update_maps_code_lt':
  forall defs g l d c e g' l' d' c' e' i s
    (RNG: 0 <= c <= Ptrofs.max_unsigned)
    (RNG: 0 <= c' <= Ptrofs.max_unsigned)
    (UPDATE: update_maps g l d c e defs = (g', l', d', c', e'))
    (AL: (alignw | c))
    (LNR: list_norepet (map fst defs))
    def
    (IN: In (i, def) defs)
    (BEFORE: g i = None)
    (GMAP: g' i = Some (code_segid, s)),
    c <= Ptrofs.unsigned s /\ Ptrofs.unsigned s + odef_size def <= c'.
Proof.
  intros.
  simpl in *.
  assert (exists f, def = Some (Gfun (Internal f))).
  {
    destruct (in_split _ _ IN) as (bef & aft & EQ). rewrite EQ in *.
    rewrite update_maps_app in UPDATE.
    repeat destr_in UPDATE. simpl in *.
    rewrite AGREE_SMINJ_INSTR.update_maps_cons in H0. repeat destr_in H0.
    erewrite update_gmap_not_in in GMAP. 2: eauto.
    erewrite update_gmap in GMAP. 2: eauto. rewrite peq_true in GMAP.
    repeat destr_in GMAP; unfold code_label, data_label, extfun_label; simpl; eauto.
    erewrite update_gmap_not_in in H0. 2: eauto. congruence.
    rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto.
    simpl in DISJ. intro II; destruct (DISJ i i II (or_introl eq_refl) eq_refl).
    rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto.
    simpl in LNR2; inv LNR2; auto.
  }
  destruct H; subst.
  simpl. exploit update_maps_code_lt. 3: eauto. 5: eauto. all: eauto.
Qed.

Lemma update_maps_data_lt:
  forall defs g l d c e g' l' d' c' e' i s
    (RNG: 0 <= d <= Ptrofs.max_unsigned)
    (RNG: 0 <= d' <= Ptrofs.max_unsigned)
    (UPDATE: update_maps g l d c e defs = (g', l', d', c', e'))
    (LNR: list_norepet (map fst defs))
    gv
    (IN: In (i, Some (Gvar gv)) defs)
    (BEFORE: g i = None)
    (AFTER: g' i = Some s),
    d <= Ptrofs.unsigned (snd s) /\ Ptrofs.unsigned (snd s) + init_data_list_size (gvar_init gv) <= d'.
Proof.
  induction defs; simpl; intros; eauto. easy.
  destruct IN.
  - subst.
    rewrite AGREE_SMINJ_INSTR.update_maps_cons in UPDATE. do 4 destr_in UPDATE. subst.
    erewrite update_gmap_not_in in AFTER. 2: eauto. 2: inv LNR; auto.
    erewrite update_gmap in AFTER. 2: eauto.
    rewrite peq_true in AFTER. inv AFTER.
    unfold code_label; simpl.
    rewrite Ptrofs.unsigned_repr; auto.
    eapply update_dsize in Heqp.
    eapply dsize_mono in UPDATE. subst. simpl in UPDATE.
    generalize (alignw_le (init_data_list_size (gvar_init gv))).
    omega.
  - destruct a. rewrite AGREE_SMINJ_INSTR.update_maps_cons in UPDATE. do 4 destr_in UPDATE. subst.
    inv LNR.
    assert (d <= z1). {
      exploit update_dsize; eauto. intro; subst.
      generalize (alignw_le (size_gvar o)). cut (size_gvar o >= 0).
      intros. omega.
      unfold size_gvar. repeat destr; try omega. apply init_data_list_size_pos.
    }
    assert (z1 <= d') by (eapply dsize_mono; eauto).
    exploit IHdefs. 3: eauto. omega. auto. auto. eauto. eauto. 
    erewrite update_gmap; eauto. rewrite peq_false; auto.
    intro; subst. apply H2.
    apply in_map with (f:= fst) in H. simpl in H; auto. eauto.
    omega.
Qed.

Lemma update_maps_data_lt':
  forall defs g l d c e g' l' d' c' e' i s
    (RNG: 0 <= d <= Ptrofs.max_unsigned)
    (RNG: 0 <= d' <= Ptrofs.max_unsigned)
    (UPDATE: update_maps g l d c e defs = (g', l', d', c', e'))
    (LNR: list_norepet (map fst defs))
    def
    (IN: In (i, def) defs)
    (BEFORE: g i = None)
    (GMAP: g' i = Some (data_segid, s)),
    d <= Ptrofs.unsigned s /\ Ptrofs.unsigned s + odef_size def <= d'.
Proof.
  intros.
  simpl in *.
  assert (exists gv, def = Some (Gvar gv)).
  {
    destruct (in_split _ _ IN) as (bef & aft & EQ). rewrite EQ in *.
    rewrite update_maps_app in UPDATE.
    repeat destr_in UPDATE. simpl in *.
    rewrite AGREE_SMINJ_INSTR.update_maps_cons in H0. repeat destr_in H0.
    erewrite update_gmap_not_in in GMAP. 2: eauto.
    erewrite update_gmap in GMAP. 2: eauto. rewrite peq_true in GMAP.
    repeat destr_in GMAP; unfold code_label, data_label, extfun_label; simpl; eauto.
    erewrite update_gmap_not_in in H0. 2: eauto. congruence.
    rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto.
    simpl in DISJ. intro II; destruct (DISJ i i II (or_introl eq_refl) eq_refl).
    rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto.
    simpl in LNR2; inv LNR2; auto.
  }
  destruct H; subst.
  exploit update_maps_data_lt. 3: eauto. 5: eauto. all: eauto.
Qed.

Lemma update_maps_extfun_lt:
  forall defs g l d c e g' l' d' c' e' i s
    (RNG: 0 <= e <= Ptrofs.max_unsigned)
    (RNG: 0 <= e' <= Ptrofs.max_unsigned)
    (UPDATE: update_maps g l d c e defs = (g', l', d', c', e'))
    (LNR: list_norepet (map fst defs))
    ef
    (IN: In (i, Some (Gfun (External ef))) defs)
    (BEFORE: g i = None)
    (AFTER: g' i = Some s),
    e <= Ptrofs.unsigned (snd s) /\ Ptrofs.unsigned (snd s) + alignw <= e'.
Proof.
  induction defs; simpl; intros; eauto. easy.
  destruct IN.
  - subst.
    rewrite AGREE_SMINJ_INSTR.update_maps_cons in UPDATE. do 4 destr_in UPDATE. subst.
    erewrite update_gmap_not_in in AFTER. 2: eauto. 2: inv LNR; auto.
    erewrite update_gmap in AFTER. 2: eauto.
    rewrite peq_true in AFTER. inv AFTER.
    unfold extfun_label; simpl.
    rewrite Ptrofs.unsigned_repr; auto.
    eapply update_efsize in Heqp.
    eapply efsize_mono in UPDATE. subst. simpl in UPDATE.
    unfold alignw in *.
    omega.
  - destruct a. rewrite AGREE_SMINJ_INSTR.update_maps_cons in UPDATE. do 4 destr_in UPDATE. subst.
    inv LNR.
    assert (e <= z). {
      exploit update_efsize; eauto. intro; subst.
      unfold size_extfun, alignw. repeat destr; omega.
    }
    assert (z <= e') by (eapply efsize_mono; eauto).
    exploit IHdefs. 3: eauto. omega. auto. auto. eauto. eauto. 
    erewrite update_gmap; eauto. rewrite peq_false; auto.
    intro; subst. apply H2.
    apply in_map with (f:= fst) in H. simpl in H; auto. eauto.
    omega.
Qed.

Lemma update_maps_extfun_lt':
  forall defs g l d c e g' l' d' c' e' i s
    (RNG: 0 <= e <= Ptrofs.max_unsigned)
    (RNG: 0 <= e' <= Ptrofs.max_unsigned)
    (UPDATE: update_maps g l d c e defs = (g', l', d', c', e'))
    (LNR: list_norepet (map fst defs))
    def
    (IN: In (i,def) defs)
    (BEFORE: g i = None)
    (GMAP: g' i = Some (extfuns_segid, s)),
    e <= Ptrofs.unsigned s /\ Ptrofs.unsigned s + odef_size def <= e'.
Proof.
  intros.
  simpl in *.
  assert (exists ef, def = Some (Gfun (External ef))).
  {
    destruct (in_split _ _ IN) as (bef & aft & EQ). rewrite EQ in *.
    rewrite update_maps_app in UPDATE.
    repeat destr_in UPDATE. simpl in *.
    rewrite AGREE_SMINJ_INSTR.update_maps_cons in H0. repeat destr_in H0.
    erewrite update_gmap_not_in in GMAP. 2: eauto.
    erewrite update_gmap in GMAP. 2: eauto. rewrite peq_true in GMAP.
    repeat destr_in GMAP; unfold code_label, data_label, extfun_label; simpl; eauto.
    erewrite update_gmap_not_in in H0. 2: eauto. congruence.
    rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto.
    simpl in DISJ. intro II; destruct (DISJ i i II (or_introl eq_refl) eq_refl).
    rewrite map_app in LNR. rewrite list_norepet_app in LNR. destruct LNR as (LNR1 & LNR2 & DISJ); auto.
    simpl in LNR2; inv LNR2; auto.
  }
  destruct H; subst.
  exploit update_maps_extfun_lt. 3: eauto. all: eauto. simpl. auto.
  unfold alignw. omega.
Qed.

Lemma norepet_unique:
  forall {A B} (f: A -> B) (l: list A)
    (LNR: list_norepet (map f l)) a b
    (INA: In a l) (INB: In b l) (EQ: f a = f b),
    a = b.
Proof.
  induction l; simpl; intros; eauto. easy.
  inv LNR. trim IHl. auto.
  destruct INA, INB; subst; eauto.
  apply in_map with (f:=f) in H0. congruence.
  apply in_map with (f:=f) in H. congruence.
Qed.

Lemma update_map_gmap_some :
  forall (prog : Asm.program) (gmap : GID_MAP_TYPE) (lmap : LABEL_MAP_TYPE) (dsize csize efsize : Z) (id : ident)
    defs gdefs def
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize, efsize))
    (BOUND: dsize + csize + efsize <= Ptrofs.max_unsigned)
    (LNR: list_norepet (map fst (AST.prog_defs prog)))
    (DEFS: (defs ++ (id, Some def) :: gdefs) = AST.prog_defs prog),
    exists slbl, gmap id = Some slbl 
           /\ (forall id' def' slbl', In (id', def') defs -> (gmap id' = Some slbl') ->
                                 fst slbl' = fst slbl -> Ptrofs.unsigned (snd slbl') + odef_size def' <= Ptrofs.unsigned (snd slbl))
           /\ (forall id' def' slbl', In (id', def') gdefs -> (gmap id' = Some slbl') ->
                           fst slbl' = fst slbl -> Ptrofs.unsigned (snd slbl) + def_size def <= Ptrofs.unsigned (snd slbl')).     
Proof.
  clear. unfold make_maps.
  intros prog gmap lmap dsize csize efsize id defs gdefs def UPDATE BOUND LNR DEFS.
  rewrite <- DEFS in *. clear prog DEFS.
  rewrite update_maps_app in UPDATE. do 4 destr_in UPDATE. subst.
  rewrite AGREE_SMINJ_INSTR.update_maps_cons in UPDATE.
  do 4 destr_in UPDATE. subst.
  rewrite map_app, list_norepet_app in LNR; destruct LNR as (LNR1 & LNR2 & DISJ); inv LNR2.
  assert (0 <= z1). eapply dsize_mono. eauto.
  assert (0 <= z0). eapply csize_mono. eauto. apply Z.divide_0_r.
  assert (0 <= z). eapply efsize_mono. eauto.
  assert (alignw | z0). eapply updates_csize_div. eauto. apply Z.divide_0_r.
  assert (alignw | z3). eapply update_csize_div with(def:= Some def). unfold update_maps_def.
  eauto. auto.
  assert (z1 <= z4). eapply update_dsize_mono; eauto.
  assert (z0 <= z3). eapply update_csize_mono; eauto.
  assert (z <= z2). eapply update_efsize_mono; eauto.
  assert (z4 <= dsize). eapply dsize_mono. eauto.
  assert (z3 <= csize). eapply csize_mono. eauto. auto.
  assert (z2 <= efsize). eapply efsize_mono. eauto.
  erewrite update_gmap_not_in; eauto.
  simpl in Heqp0. repeat destr_in Heqp0.
  - (* internal function *)
    unfold update_gid_map. rewrite peq_true. eexists; split; eauto.
    split.
    + intros id' def' slbl' IN GM LBLEQ.
      erewrite update_gmap_not_in in GM; eauto.
      unfold update_gid_map in GM. rewrite peq_false in GM.
      destruct slbl'. simpl in *. subst.
      exploit update_maps_code_lt'. 3: apply Heqp. 5: apply IN. 5: reflexivity. all: eauto.
      vm_compute. intuition congruence. omega. apply Z.divide_0_r.
      rewrite Ptrofs.unsigned_repr. omega. omega.
      intro; subst.
      exploit DISJ. apply in_map. eauto. left. reflexivity. reflexivity. auto.
      intro IN'. exploit DISJ. apply in_map, IN. right; apply IN'. auto. auto.
    + intros id' def' slbl' IN GM LBLEQ.
      destruct slbl'. simpl in *. subst.
      exploit update_maps_code_lt'. 3: apply UPDATE. 5: apply IN. all: eauto. omega. omega.
      unfold update_gid_map.
      rewrite peq_false.
      erewrite update_gmap_not_in. 2: eauto. reflexivity. auto.
      intro IN'. exploit DISJ. apply IN'. right; apply in_map, IN. auto. auto.
      intro; subst. apply H1. replace id' with (fst (id', def')) by reflexivity.
      apply in_map; congruence.
      rewrite Ptrofs.unsigned_repr.
      exploit update_instrs_code_size; eauto. intros; subst.
      eapply Z.le_trans. 2: apply H13.
      eapply Z.le_trans. 2: apply alignw_le. omega. omega.
  - (* external function *)
    unfold update_gid_map. rewrite peq_true. eexists; split; eauto.
    split.
    + intros id' def' slbl' IN GM LBLEQ.
      erewrite update_gmap_not_in in GM; eauto.
      unfold update_gid_map in GM. rewrite peq_false in GM.
      destruct slbl'. simpl in *. subst.
      exploit update_maps_extfun_lt'. 3: apply Heqp. 4: apply IN. 4: reflexivity. all: eauto.
      vm_compute. intuition congruence. omega.
      rewrite Ptrofs.unsigned_repr. omega. omega.
      intro; subst. exploit DISJ. apply in_map; eauto. left. reflexivity. reflexivity. auto.
      intro IN'. exploit DISJ. apply in_map, IN. right; apply IN'. auto. auto.
    + intros id' def' slbl' IN GM LBLEQ.
      destruct slbl'. simpl in *. subst.
      exploit update_maps_extfun_lt'. 3: apply UPDATE. all: eauto. omega. omega.
      unfold update_gid_map.
      rewrite peq_false.
      erewrite update_gmap_not_in. 2: eauto. reflexivity. auto.
      intro IN'. exploit DISJ. apply IN'. right; apply in_map, IN. auto. auto.
      intro; subst. apply H1. replace id' with (fst (id', def')) by reflexivity.
      apply in_map. congruence. 
      rewrite Ptrofs.unsigned_repr. unfold alignw. omega. omega.
  - (* variable *)
    unfold update_gid_map. rewrite peq_true. eexists; split; eauto.
    split.
    + intros id' def' slbl' IN GM LBLEQ.
      erewrite update_gmap_not_in in GM; eauto.
      unfold update_gid_map in GM. rewrite peq_false in GM.
      destruct slbl'. simpl in *. subst.
      exploit update_maps_data_lt'. 3: apply Heqp. all: eauto.
      vm_compute. intuition congruence. omega.
      rewrite Ptrofs.unsigned_repr. omega. omega.
      intro; subst. exploit DISJ. apply in_map; eauto. left. reflexivity. reflexivity. auto.
      intro IN'. exploit DISJ. apply in_map, IN. right; apply IN'. auto. auto.
    + intros id' def' slbl' IN GM LBLEQ.
      destruct slbl'. simpl in *. subst.
      exploit update_maps_data_lt'. 3: apply UPDATE. all: eauto. omega. omega.
      unfold update_gid_map.
      rewrite peq_false.
      erewrite update_gmap_not_in. 2: eauto. reflexivity. auto.
      intro IN'. exploit DISJ. apply IN'. right; apply in_map, IN. auto. auto.
      intro; subst. apply H1. replace id' with (fst (id', def')) by reflexivity.
      apply in_map; congruence. 
      rewrite Ptrofs.unsigned_repr by omega.
      intros. eapply Z.le_trans. 2: apply H12.
      generalize (alignw_le (init_data_list_size (gvar_init v))); omega.
Qed.


Lemma make_maps_gmap_inj':
  forall prog0 g' l' d' c' e'
    (lnr : list_norepet (map fst (AST.prog_defs prog0)))
    (mm : make_maps prog0 = (g', l', d', c', e'))
    (bound: d' + c' + e' <= Ptrofs.max_unsigned)
    (* (ne: Forall def_not_empty (map snd (AST.prog_defs prog0))) *)
    l1 l2 l3 i1 i2 d1 d2 s1 s2 o1 o2
    (EQ: AST.prog_defs prog0 = l1 ++ (i1, d1) :: l2 ++ (i2, d2) :: l3)
    (G1 : g' i1 = Some (s1, o1))
    (G2 : g' i2 = Some (s2, o2)),
    s1 <> s2 \/ Ptrofs.unsigned o1 + odef_size d1 <= Ptrofs.unsigned o2 \/ Ptrofs.unsigned o2 + odef_size d2 <= Ptrofs.unsigned o1.
Proof.
  intros.
  destruct (peq s1 s2); auto. subst.
  right.
  destruct d1.
  - exploit update_map_gmap_some; eauto.
    rewrite G1.
    intros (s & G & O1 & O2). inv G. eapply O2 in G2; eauto. rewrite in_app. right; left; reflexivity.
  - unfold make_maps in mm.
    rewrite EQ in mm.
    rewrite update_maps_app in mm. repeat destr_in mm.
    rewrite AGREE_SMINJ_INSTR.update_maps_cons in H0. repeat destr_in H0.
    rewrite EQ in lnr.
    rewrite map_app, list_norepet_app in lnr.
    destruct lnr as (lnr1 & lnr2 & disj).
    assert (g' i1 = None).
    erewrite update_gmap_not_in. 2: eauto.
    erewrite update_gmap. 2: eauto. rewrite peq_true.
    erewrite update_gmap_not_in. 2: eauto. reflexivity.
    auto. intro IN. exploit disj. apply IN. left. reflexivity. reflexivity. auto.
    inv lnr2; auto. inv lnr2.  auto. congruence.
Qed.

Lemma app_cons_assoc:
  forall {A} (l1: list A) a l2 b l3,
    (l1 ++ a :: l2) ++ b :: l3 = l1 ++ a :: l2 ++ b :: l3.
Proof.
  induction l1; simpl; intros. reflexivity.
  rewrite IHl1. auto.  
Qed.


Lemma update_maps_gmap_inj:
  forall prog g' l' d' c' e'
    (lnr: list_norepet (map fst (AST.prog_defs prog)))
    (mm: make_maps prog = (g', l', d', c', e'))
    (bound: d' + c' + e' <= Ptrofs.max_unsigned),
    gmap_inj g' (AST.prog_defs prog).
Proof.
  red; intros.
  destruct (in_split _ _ H) as (l1 & l2 & EQ). rewrite EQ in H0.
  rewrite in_app in H0.
  destruct H0 as [IN2 | IN2].
  destruct (in_split _ _ IN2) as (l3 & l4 & EQ'). subst.
  exploit make_maps_gmap_inj'. 4: rewrite EQ, app_cons_assoc; reflexivity. all: eauto. intuition.
  destruct IN2 as [EQ2 | IN2]. inv EQ2. congruence.
  destruct (in_split _ _ IN2) as (l3 & l4 & EQ'). subst.
  exploit make_maps_gmap_inj'. 4: rewrite EQ; reflexivity. all: eauto. 
Qed.

Theorem init_meminj_match_sminj : forall gmap lmap dsize csize efsize m,
    dsize + csize + efsize <= Ptrofs.max_unsigned ->
    Genv.init_mem prog = Some m ->
    make_maps prog = (gmap,lmap,dsize,csize,efsize) ->
    transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog ->
    match_sminj gmap lmap (init_meminj gmap).
Proof.   
  intros gmap lmap dsize csize efsize m MAX INITMEM UPDATE TRANS. 
  generalize TRANSF. intros TRANSF'.
  unfold match_prog in TRANSF'. 
  unfold transf_program in TRANSF'. 
  repeat destr_in TRANSF'.
  unfold make_maps in Heqp. inv UPDATE.
  monadInv H0.   
  rename x into tgdefs. rename x0 into code.
  constructor.
  - (* agree_sminj_instr *) 
    intros b b' f ofs ofs' i FPTR FINST INITINJ.
    unfold init_meminj in INITINJ. fold ge in INITINJ.
    destruct (eq_block b (Globalenvs.Genv.genv_next ge)); inversion INITINJ. 
    subst ofs' b' b. clear INITINJ.
    + exfalso. subst ge. eapply Genv.genv_next_find_funct_ptr_absurd; eauto. 
    + destruct (Genv.invert_symbol ge b) eqn:INVSYM; inversion H1.
      repeat destr_in H2.
      clear INITINJ.
      rewrite Ptrofs.repr_unsigned. rename i0 into id.
      apply Genv.invert_find_symbol in INVSYM.
      exploit (Genv.find_symbol_funct_ptr_inversion prog); eauto.
      intros FINPROG.
      exploit transl_fun_exists; eauto. intros (f' & TRANSLFUN' & INR).
      exploit AGREE_SMINJ_INSTR.find_instr_transl_fun; eauto. 
      intros (i' & ofs1 & TRANSINSTR & SEGLBL & IN).
      exists id, i', (fst s), ofs1. split. 
      unfold segblock_to_label in SEGLBL. inversion SEGLBL.
      apply INR in IN.
      eapply AGREE_SMINJ_INSTR.find_instr_self; eauto.
      simpl.
      eapply transl_globdefs_distinct_code_labels; eauto.
      eapply update_maps_gmap_inj; eauto.
      inv w; auto.
      split; auto.

  - (* agree_sminj_glob *)
    intros id gloc GMAP.
    assert (In id (prog_defs_names prog)) 
      by (eapply AGREE_SMINJ_GLOB.update_map_gmap_domain; eauto).
    exploit Genv.find_symbol_exists_1; eauto.
    intros (b & FIND).
    esplit. exists b. esplit. split. auto. split.
    unfold Genv.symbol_address. unfold Genv.label_to_ptr. auto.
    unfold init_meminj.       
    destruct eq_block. exfalso. subst b. eapply Genv.find_symbol_genv_next_absurd; eauto.    
    apply Genv.find_invert_symbol in FIND. subst ge. rewrite FIND. rewrite GMAP.
    unfold Genv.symbol_block_offset. unfold Genv.label_to_block_offset.
    repeat rewrite offset_seglabel_zero. auto.

  - (* agree_sminj_lbl *)
    intros id b f l z l' FINDSYM FINDPTR LPOS LPOS'.
    subst ge. 
    exploit Genv.find_symbol_funct_ptr_inversion; eauto. intros INDEFS.
    exploit transl_fun_exists; eauto.
    intros (f' & TRANSLF & INCODE).
    set (ge := Genv.globalenv prog).
    exploit AGREE_SMINJ_LBL.update_map_lmap_inversion; eauto.
    inv w; auto. inv w; auto. 
    eapply AGREE_SMINJ_LBL.defs_nodup_labels; eauto.

    intros (slbl & GMAP & LEQ & OFSEQ).
    unfold Genv.symbol_address. unfold Genv.label_to_ptr. 
    apply Val.inject_ptr with (Ptrofs.unsigned (snd slbl)).   
    unfold init_meminj. destruct eq_block.
    subst b. exfalso. 
    eapply Genv.find_symbol_genv_next_absurd; eauto.
    erewrite Genv.find_invert_symbol; eauto.
    rewrite offset_seglabel_zero. 
    unfold Genv.symbol_block_offset. unfold Genv.label_to_block_offset.
    rewrite GMAP. rewrite LEQ. auto.
    rewrite offset_seglabel_zero. rewrite Ptrofs.repr_unsigned. symmetry.
    rewrite Ptrofs.add_commut. auto.
Qed.

Lemma alloc_pres_def_frame_inj : forall m1 lo hi m1' b,
    Mem.alloc m1 lo hi = (m1', b) ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  unfold def_frame_inj. intros.
  apply Mem.alloc_stack_blocks in H. rewrite H. auto.
Qed.

(** Proving initial memory injection **)

Definition partial_genv defs : Globalenvs.Genv.t Asm.fundef unit := 
  let emptyge := (Globalenvs.Genv.empty_genv Asm.fundef unit prog.(AST.prog_public)) in
  Globalenvs.Genv.add_globals emptyge defs.

Definition globs_meminj (gmap: GID_MAP_TYPE) : meminj :=
  let ge := Genv.globalenv prog in
  let tge := globalenv tprog in
  fun b =>
      match (Genv.invert_symbol ge b) with
      | None => None
      | Some id =>
        match (gmap id) with
        | None => None
        | Some slbl => Some (Genv.symbol_block_offset tge slbl)
        end
      end.


Lemma find_symbol_add_global_eq : forall (F V: Type) (ge:Globalenvs.Genv.t F V) i def,
    Globalenvs.Genv.find_symbol (Globalenvs.Genv.add_global ge (i, def)) i = Some (Globalenvs.Genv.genv_next ge).
Proof.
  intros F V ge0 i def. unfold Genv.find_symbol.
  unfold Genv.add_global. simpl. rewrite PTree.gss. auto.
Qed.

Lemma find_symbol_add_global_neq : forall (F V: Type) (ge:Globalenvs.Genv.t F V) i i' def,
    i <> i' -> 
    Globalenvs.Genv.find_symbol (Globalenvs.Genv.add_global ge (i, def)) i' = 
    Globalenvs.Genv.find_symbol ge i'.
Proof.
  intros F V ge0 i i' def H. unfold Genv.find_symbol.
  unfold Genv.add_global. simpl. rewrite PTree.gso; auto.
Qed.

Lemma fold_left_le:
  forall b l o o',
    fold_left (fun (a: option positive) (p: positive * positive) => if eq_block b (snd p) then Some (fst p) else a) l o = o' ->
    match o, o' with
    | Some _, None => False
    | _, _ => True
    end.
Proof.
  induction l; simpl; intros; eauto.
  subst; destr.
  eapply IHl in H.
  repeat destr_in H; destr.
  destr_in Heqo0.
Qed.

Lemma fold_left_none_not_in:
  forall b l o,
    fold_left (fun (a: option positive) (p: positive * positive) => if eq_block b (snd p) then Some (fst p) else a) l o = None ->
    ~ In b (map snd l).
Proof.
  induction l; simpl; intros; eauto.
  destr_in H.
  apply fold_left_le in H. easy.
  eapply IHl in H; eauto. intuition.
Qed.


Lemma not_in_fold_left_none:
  forall b l,
    ~ In b (map snd l) ->
    fold_left (fun (a: option positive) (p: positive * positive) => if eq_block b (snd p) then Some (fst p) else a) l None = None.
Proof.
  induction l; simpl; intros; eauto.
  rewrite peq_false by intuition.
  apply IHl. intuition.
Qed.

Lemma invert_add_global_genv_next : forall (F V: Type) (ge:Globalenvs.Genv.t F V) id def,
    Genv.invert_symbol (Genv.add_global ge (id, def)) (Globalenvs.Genv.genv_next ge) = Some id.
Proof.
  intros. apply Genv.find_invert_symbol.
  apply find_symbol_add_global_eq.
Qed.

Lemma partial_genv_invert_symbol : forall defs id def,
    Genv.invert_symbol (partial_genv (defs ++ (id, def) :: nil)) (Globalenvs.Genv.genv_next (partial_genv defs)) = Some id.
Proof.
  intros defs id def. unfold partial_genv. 
  rewrite Genv.add_globals_app. simpl.
  apply invert_add_global_genv_next.
Qed.

Lemma partial_genv_find_symbol_eq : forall defs id def,
    Genv.find_symbol (partial_genv (defs ++ (id, def) :: nil)) id = Some (Globalenvs.Genv.genv_next (partial_genv defs)).
Proof.
  intros defs id def. apply Genv.invert_find_symbol.
  apply partial_genv_invert_symbol.
Qed.

Lemma partial_genv_find_symbol_neq : forall defs id id' def,
    id <> id' -> 
    Genv.find_symbol (partial_genv (defs ++ (id, def) :: nil)) id' = Genv.find_symbol (partial_genv defs) id'.
Proof.
  intros defs id id' def H. unfold partial_genv. rewrite Genv.add_globals_app.
  simpl. rewrite find_symbol_add_global_neq; auto.
Qed.


Lemma partial_genv_find_symbol_inversion : forall defs x b,
  Genv.find_symbol (partial_genv defs) x = Some b ->
  In x (map fst defs).
Proof.
  unfold partial_genv. intros defs x b.
  eapply Genv.add_globals_preserves.
  - intros.
    destruct (peq x id). subst.
    rewrite find_symbol_add_global_eq in H1. inv H1. apply in_map with (f:= fst) in H0; auto.
    rewrite find_symbol_add_global_neq in H1 by auto. eauto.
  - setoid_rewrite PTree.gempty. congruence.
Qed.

Lemma invert_symbol_add_global_none : forall defs id def b,
    ~In id (map fst defs) ->
    Genv.invert_symbol (Genv.add_global (partial_genv defs) (id, def)) b = None ->
    Genv.invert_symbol (partial_genv defs) b = None.
Proof.
  intros defs id def b NOTIN INVSYM.
  destruct (Genv.invert_symbol (partial_genv defs) b) eqn:INVSYM'; auto.
  apply Genv.invert_find_symbol in INVSYM'.
  assert (id <> i) as FINDSYM. 
  {
    exploit partial_genv_find_symbol_inversion; eauto. 
    intros IN EQ. subst. congruence.
  }
  eapply find_symbol_add_global_neq in FINDSYM; eauto.
  rewrite INVSYM' in FINDSYM.
  apply Genv.find_invert_symbol in FINDSYM. 
  rewrite INVSYM in FINDSYM. inv FINDSYM.
Qed.

Lemma update_map_gmap_none :
  forall (prog : Asm.program) (gmap : GID_MAP_TYPE) (lmap : LABEL_MAP_TYPE) (dsize csize efsize : Z) (id : ident)
    (DEFSNAMES: list_norepet (map fst (AST.prog_defs prog)))
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize, efsize))
    (IN: In (id, None) (AST.prog_defs prog)),
    gmap id = None.
Proof.
  intros. unfold make_maps in UPDATE.
  eapply umind with (P := fun g l s c e => g id = None). eauto. reflexivity.
  intros.
  erewrite update_gmap. 2: eauto. destr. subst.
  exploit @norepet_unique. apply DEFSNAMES. apply IN. apply H1. reflexivity. intro A; inv A. auto.
Qed.



Definition fun_non_empty (def: AST.globdef Asm.fundef unit) : Prop :=
  match def with
  | Gfun (Internal f) =>
    (0 < length (Asm.fn_code f))%nat
  | _ => True
  end.

Definition defs_funs_non_empty (defs: list (ident * option (AST.globdef Asm.fundef unit))) : Prop :=
  Forall (fun '(id, def) =>
            match def with
            | None => True
            | Some def' => fun_non_empty def'
            end
         ) defs.

Lemma defs_funs_non_empty_cons_inv : forall a l,
  defs_funs_non_empty (a::l) -> defs_funs_non_empty l.
Proof.
  unfold defs_funs_non_empty. intros a l H.
  inv H. auto.
Qed.

Lemma drop_perm_pres_def_frame_inj : forall m1 lo hi m1' b p,
    Mem.drop_perm m1 b lo hi p = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  unfold def_frame_inj. intros.
  apply Mem.drop_perm_stack in H. rewrite H. auto.
Qed.

Lemma transl_fun_inversion : forall gmap lmap id f f',
    transl_fun gmap lmap id f = OK f' ->
    exists slbl, gmap id = Some slbl /\ fn_range f' = mkSegBlock (fst slbl) (snd slbl) (Ptrofs.repr (Asm.code_size (Asm.fn_code f))).
Proof.
  intros gmap lmap id f f' H. monadInvX H.
  destruct zle; monadInv EQ2. simpl. eexists. split; eauto.
Qed.

Lemma partial_genv_invert_symbol_pres : forall defs id def b,
    ~ In id (map fst defs) ->
    b <> Globalenvs.Genv.genv_next (partial_genv defs) ->
    Genv.invert_symbol (partial_genv (defs ++ (id, def) :: nil)) b = Genv.invert_symbol (partial_genv defs) b.
Proof.
  intros defs id def b NOTIN H.
  unfold partial_genv. rewrite Genv.add_globals_app. simpl.
  match goal with
  | [ |- ?a = _ ] =>
    let eq := fresh "EQ" in
    destruct a eqn:eq
  end.
  - apply Genv.invert_find_symbol in EQ. symmetry. apply Genv.find_invert_symbol.
    destruct (ident_eq id i). subst i.
    rewrite find_symbol_add_global_eq in EQ. inv EQ.
    contradiction.
    erewrite find_symbol_add_global_neq in EQ; eauto.
  - symmetry. eapply invert_symbol_add_global_none in EQ; eauto.
Qed.


Lemma partial_genv_next : forall defs def,
    Globalenvs.Genv.genv_next (partial_genv (defs ++ def :: nil)) =
    Pos.succ (Globalenvs.Genv.genv_next (partial_genv defs)).
Proof.
  intros. unfold partial_genv.
  rewrite Genv.add_globals_app. simpl. auto.
Qed.

Lemma defs_names_distinct_not_in : forall(F V:Type) (defs:list (ident * option (AST.globdef F V))) id def gdefs,
    list_norepet (map fst (defs ++ (id, def) :: gdefs)) -> ~In id (map fst defs).
Proof.
  intros F V defs id def gdefs LNR.
  rewrite map_app, list_norepet_app in LNR.
  destruct LNR as (A & B & C).
  intro IN.
  exploit C. eauto. left; reflexivity. reflexivity. auto.
Qed.

Lemma defs_names_distinct_prefix_neq : forall (F V:Type) (defs1: list (ident * option (AST.globdef F V)))
                                         id def defs2 id' def',
    list_norepet (map fst (defs1 ++ (id, def) :: defs2)) ->
    In (id', def') defs1 -> id <> id'.
Proof.
  intros F V defs1 id def defs2 id' def' DISTINCT IN.
  assert (~ In id (map fst defs1)). eapply defs_names_distinct_not_in; eauto.
  unfold not. intros. subst.
  exploit (in_map fst defs1); eauto.
Qed.


Lemma find_symbol_add_globals_inversion : 
  forall (F V:Type) (defs: list (ident * option (AST.globdef F V))) id r ge,
    Genv.find_symbol (Genv.add_globals ge defs) id = r ->
    (exists def, In (id, def) defs) \/ Genv.find_symbol ge id = r.
Proof.
  induction defs; intros.
  - simpl in H. auto.
  - simpl in H. exploit IHdefs; eauto.
    intros [L | R].
    + destruct L as [def' IN].
      left. exists def'. apply in_cons. auto.
    + destruct a. destruct (ident_eq id i).
      subst. rewrite find_symbol_add_global_eq in R. left. eexists. simpl. left. eauto.
      erewrite find_symbol_add_global_neq in R; eauto.
Qed.

Lemma find_symbol_inversion_1 : forall defs (x : ident) (b : block),
    Genv.find_symbol (partial_genv defs) x = Some b -> exists def, In (x, def) defs.
Proof.
  unfold partial_genv. intros.
  exploit find_symbol_add_globals_inversion; eauto.
  intros [L | R]. auto.
  exploit Genv.find_symbol_empty_genv_absurd; eauto. contradiction.
Qed.


Lemma store_zeros_mapped_inject:
  forall (f : meminj) (g : frameinj) (m1 : mem) (b1 : block) (ofs n : Z) 
    (n1 m2 : mem) (b2 : block) (delta : Z),
    Mem.weak_inject f g m1 m2 ->
    store_zeros m1 b1 ofs n = Some n1 ->
    f b1 = Some (b2, delta) ->
    exists n2 : mem, store_zeros m2  b2 (ofs+delta) n = Some n2 /\ Mem.weak_inject f g n1 n2.
Proof.
  intros until n1. functional induction (store_zeros m1 b1 ofs n); intros.
  - inv H0. exists m2. split; auto. rewrite store_zeros_equation.
    rewrite e. auto.
  - exploit Mem.store_mapped_weak_inject; eauto. unfold Vzero. eauto. 
    intros (n2 & STORE & WINJ).
    exploit IHo; eauto. intros (n3 & STOREZEROS & WINJ'). exists n3. split; eauto.
    rewrite store_zeros_equation. rewrite e. 
    unfold Vzero. rewrite STORE. replace (p + delta + 1) with (p + 1 + delta) by omega. auto.
  - inv H0.
Qed.

Lemma store_zeros_pres_def_frame_inj : forall m1 b lo hi m1',
    store_zeros m1 b lo hi = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  intros m1 b lo hi m1' H.
  functional induction (store_zeros m1 b lo hi); intros.
  - inv H. auto.
  - exploit IHo; eauto. intros.
    exploit Mem.store_stack_blocks; eauto.
    intros. unfold def_frame_inj in *. rewrite H1 in *. auto.
  - inv H.
Qed.

Lemma store_init_data_list_mapped_inject_aux : forall v v' gmap g m1 m1' m2 b1 b2 delta ofs,
    Mem.weak_inject (globs_meminj gmap) g m1 m1' ->
    transl_init_data_list gmap v = OK v' -> 
    (globs_meminj gmap) b1 = Some (b2, delta) ->
    Genv.store_init_data_list ge m1 b1 ofs v = Some m2 ->
    exists m2', store_init_data_list tge m1' b2 (ofs+delta) v' = Some m2'
           /\ Mem.weak_inject (globs_meminj  gmap) g m2 m2'.
Proof.
  induction v; intros.
  - monadInv H0. simpl in H2. inv H2. exists m1'. split; auto.
  - monadInv H0. simpl in H2. destr_match_in H2; inv H2.
    unfold Genv.store_init_data in EQ0. destruct a.
    + monadInv EQ. exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). simpl in H3.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl. 
      rewrite STORE. replace (ofs + delta + 1) with (ofs + 1 + delta) by omega.
      auto.
    + monadInv EQ. exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). simpl in H3.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl. 
      rewrite STORE. replace (ofs + delta + 2) with (ofs + 2 + delta) by omega.
      auto.
    + monadInv EQ. exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). simpl in H3.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl. 
      rewrite STORE. replace (ofs + delta + 4) with (ofs + 4 + delta) by omega.
      auto.
    + monadInv EQ. exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). simpl in H3.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl. 
      rewrite STORE. replace (ofs + delta + 8) with (ofs + 8 + delta) by omega.
      auto.
    + monadInv EQ. exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). simpl in H3.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl. 
      rewrite STORE. replace (ofs + delta + 4) with (ofs + 4 + delta) by omega.
      auto.
    + monadInv EQ. exploit Mem.store_mapped_weak_inject; eauto.
      intros (n2 & STORE & WINJ). simpl in H3.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl. 
      rewrite STORE. replace (ofs + delta + 8) with (ofs + 8 + delta) by omega.
      auto.
    + monadInv EQ. simpl in H3. inv EQ0.
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl. 
      replace (ofs + delta + (Z.max z 0)) with (ofs + (Z.max z 0) + delta) by omega.
      auto.
    + monadInvX EQ. simpl in H3. destr_match_in EQ0; inv EQ0.
      exploit Mem.store_mapped_weak_inject; eauto. 
      econstructor. unfold globs_meminj. apply Genv.find_invert_symbol in EQ.
      unfold ge in EQ. rewrite EQ. rewrite EQ2. 
      unfold Genv.symbol_block_offset. unfold Genv.label_to_block_offset. eauto.
      rewrite Ptrofs.repr_unsigned. eauto.
      intros (n2 & STORE & WINJ). 
      exploit IHv; eauto. intros (n3 & STOREL & WINJ').
      exists n3. split; eauto. simpl. 
      unfold Genv.symbol_address. unfold Genv.label_to_ptr. 
      unfold offset_seglabel. destruct s. simpl. simpl in STORE. unfold tge. 
      rewrite Ptrofs.add_commut. rewrite STORE.
      replace (ofs + delta + (if Archi.ptr64 then 8 else 4)) with (ofs + (if Archi.ptr64 then 8 else 4) + delta) by omega.
      auto.
Qed.

Lemma store_init_data_list_mapped_inject : forall gmap g m1 m1' m2 v v' b1 b2 delta ofs,
    Mem.weak_inject (globs_meminj gmap) g m1 m1' ->
    transl_gvar gmap v = OK v' -> 
    (globs_meminj gmap) b1 = Some (b2, delta) ->
    Genv.store_init_data_list ge m1 b1 ofs (gvar_init v) = Some m2 ->
    exists m2', store_init_data_list tge m1' b2 (ofs+delta) (FlatAsmGlobdef.gvar_init unit v') = Some m2'
           /\ Mem.weak_inject (globs_meminj  gmap) g m2 m2'.
Proof.
  intros gmap g m1 m1' m2 v v' b1 b2 delta ofs WINJ TRANSLV F STOREL.
  monadInv TRANSLV. simpl.
  eapply store_init_data_list_mapped_inject_aux; eauto.
Qed.

Lemma store_init_data_pres_def_frame_inj : forall m1 b1 ofs v m1',
    Genv.store_init_data ge m1 b1 ofs v = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  intros. unfold Genv.store_init_data in H.
  destruct v; try now (exploit Mem.store_stack_blocks; eauto; unfold def_frame_inj; congruence).
  inv H. auto.
  destr_match_in H; inv H.
  exploit Mem.store_stack_blocks; eauto; unfold def_frame_inj; congruence.
Qed.

Lemma store_init_data_list_pres_def_frame_inj : forall gv m1 b1 ofs  m1',
    Genv.store_init_data_list ge m1 b1 ofs gv = Some m1' ->
    def_frame_inj m1 = def_frame_inj m1'.
Proof.
  induction gv; intros.
  - inv H. auto.
  - inv H. destr_match_in H1; inv H1.
    exploit store_init_data_pres_def_frame_inj; eauto. intros.
    rewrite H. exploit IHgv; eauto.
Qed.

Lemma transl_init_data_pres_size : forall gmap v v', 
    transl_init_data gmap v = OK v' ->
    (init_data_size v = FlatAsmGlobdef.init_data_size v').
Proof.
  intros gmap v v' H.
  unfold transl_init_data in H.
  destruct v; try now (monadInv H; eauto).
  monadInvX H. simpl. auto.
Qed.

Lemma transl_init_data_list_pres_size : forall gmap v v', 
    transl_init_data_list gmap v = OK v' ->
    (init_data_list_size v = FlatAsmGlobdef.init_data_list_size v').
Proof.
  induction v; intros.
  - monadInv H. auto.
  - monadInv H. simpl.
    erewrite transl_init_data_pres_size; eauto.
    erewrite IHv; eauto.
Qed.

Lemma transl_gvar_pres_size : forall gmap v v', 
    transl_gvar gmap v = OK v' ->
    (init_data_list_size (gvar_init v)) =
    (FlatAsmGlobdef.init_data_list_size (FlatAsmGlobdef.gvar_init unit v')).
Proof.
  intros gmap v v' TRANSLV.
  monadInv TRANSLV. simpl.
  eapply transl_init_data_list_pres_size; eauto.
Qed.

Lemma transl_gvar_pres_perm : forall gmap v (v':FlatAsmGlobdef.globvar unit), 
    transl_gvar gmap v = OK v' ->
    Genv.perm_globvar v = FlatAsmGlobdef.perm_globvar v'.
Proof.
  intros gmap v v' H.
  monadInv H. unfold FlatAsmGlobdef.perm_globvar. simpl.
  auto.
Qed.

Lemma defs_names_distinct_not_in_tail : forall(F V:Type) (defs:list (ident * option (AST.globdef F V))) id def gdefs,
    list_norepet (map fst (defs ++ (id, def) :: gdefs)) -> ~In id (map fst gdefs).
Proof.
  intros F V defs id def gdefs LNR.
  rewrite map_app, list_norepet_app in LNR.
  destruct LNR as (A & B & C).
  intro IN. simpl in B. inv B. congruence.
Qed.

Lemma genv_find_symbol_next : forall defs id def gdefs,
    list_norepet (map fst (AST.prog_defs prog)) ->
    AST.prog_defs prog = (defs ++ (id, def) :: gdefs) ->
    Genv.find_symbol (Genv.globalenv prog) id = Some (Globalenvs.Genv.genv_next (partial_genv defs)).
Proof.
  intros defs id def gdefs NORPT H. unfold Genv.globalenv. rewrite H.
  rewrite Genv.add_globals_app. simpl.
  match goal with
  | [ |- Genv.find_symbol (Genv.add_globals ?ge' ?defs') ?id' = _ ] =>
    exploit (find_symbol_add_globals_inversion Asm.fundef unit defs' id' 
                                               (Genv.find_symbol (Genv.add_globals ge' defs') id')); eauto
  end.
  intros [L | R].
  - destruct L as [def' IN].
    rewrite H in NORPT. 
    assert (~In id (map fst gdefs)). eapply defs_names_distinct_not_in_tail; eauto.
    assert (In (fst (id, def')) (map fst gdefs)). apply in_map. auto.
    simpl in H1. congruence.
  - rewrite <- R.
    erewrite find_symbol_add_global_eq; eauto.
Qed.


Lemma genv_invert_symbol_next : forall defs id def gdefs,
    list_norepet (map fst (AST.prog_defs prog)) ->
    AST.prog_defs prog = (defs ++ (id, def) :: gdefs) ->
    Genv.invert_symbol (Genv.globalenv prog) (Globalenvs.Genv.genv_next (partial_genv defs)) = Some id.
Proof.
  intros defs id def gdefs NORPT H. 
  apply Genv.find_invert_symbol. eapply genv_find_symbol_next; eauto.
Qed.

Definition aligned (ofs:Z) := forall chunk, (align_chunk chunk | ofs).

Lemma chunk_divides_alignw: forall chunk,
  (align_chunk chunk | alignw).
Proof.
  intros. unfold alignw. destruct chunk; simpl; red.
  - exists 8; omega.
  - exists 8; omega.
  - exists 4; omega.
  - exists 4; omega.
  - exists 2; omega.
  - exists 1; omega.
  - exists 2; omega.
  - exists 2; omega.
  - exists 2; omega.
  - exists 2; omega.
Qed.

Lemma alignw_aligned : forall i,
  (alignw | i) -> aligned i.
Proof.
  unfold aligned. intros.
  apply Zdivides_trans with alignw; auto.
  apply chunk_divides_alignw.
Qed.


Lemma update_map_gmap_aligned : 
  forall defs gmap lmap dsize csize efsize
    gmap1 lmap1 dsize1 csize1 efsize1 slbl i
    (UPDATE: (gmap,lmap,dsize, csize, efsize) = update_maps gmap1 lmap1 dsize1 csize1 efsize1 defs)
    (CSZALN: (alignw | csize1))
    (CSZBOUND: csize <= Ptrofs.max_unsigned)
    (CSZPOS: 0 <= csize1)
    (EFSZALN: (alignw | efsize1))
    (EFSZBOUND: efsize <= Ptrofs.max_unsigned)
    (EFSZPOS: 0 <= efsize1)
    (DSZALN: (alignw | dsize1))
    (DSZBOUND: dsize <= Ptrofs.max_unsigned)
    (DSZPOS: 0 <= dsize1)
    (GMAPALN: forall i' slbl', gmap1 i' = Some slbl' -> aligned (Ptrofs.unsigned (snd slbl')))
    (GMAP: gmap i = Some slbl),
    aligned (Ptrofs.unsigned (snd slbl)).
Proof.
  induction defs; intros.
  assert (csize1 <= csize). eapply csize_mono; eauto.
  - inv UPDATE. eauto.
  - destruct a. destruct o. destruct g. destruct f.
    + cbn in UPDATE. 
      destruct (update_instrs lmap1 csize1 i0 (Asm.fn_code f)) as [lmap' csize'] eqn:UPDATEINSTRS.
      eapply IHdefs; eauto. 
      apply align_divides. unfold alignw. omega.
      apply Zle_trans with csize'; try apply alignw_le.
      exploit update_instrs_code_size; eauto. intros.
      generalize (code_size_non_neg (Asm.fn_code f)). intros.
      omega.
      intros i' slbl' GMAP'.
      unfold update_gid_map in GMAP'. destruct peq. 
      subst. inv GMAP'. unfold code_label. simpl. 
      rewrite Ptrofs.unsigned_repr. apply alignw_aligned. auto.
      assert (align csize' alignw <= csize).
      { eapply csize_mono; eauto. apply align_divides. unfold alignw. omega. }
      generalize (alignw_le csize'). intros.
      exploit update_instrs_code_size; eauto. intros.
      generalize (code_size_non_neg (Asm.fn_code f)). intros.
      omega.
      eauto.
    + cbn in UPDATE. 
      eapply IHdefs; eauto.
      red in EFSZALN. destruct EFSZALN.
      red. exists (x+1). rewrite H. rewrite Z.mul_add_distr_r. omega.
      unfold alignw. omega.
      intros i' slbl' GMAP'.
      unfold update_gid_map in GMAP'. destruct peq. 
      subst. inv GMAP'. unfold extfun_label. simpl. 
      rewrite Ptrofs.unsigned_repr. apply alignw_aligned. auto.
      assert (efsize1 + alignw <= efsize).
      { eapply efsize_mono; eauto. }
      unfold alignw in H. omega.
      eauto.
    + cbn in UPDATE. 
      eapply IHdefs; eauto.
      apply Z.divide_add_r; auto.
      apply align_divides. 
      unfold alignw. omega.
      generalize (alignw_le (init_data_list_size (gvar_init v))). intros.
      generalize (init_data_list_size_pos (gvar_init v)). intros. omega.
      intros i' slbl' GMAP'.
      unfold update_gid_map in GMAP'. destruct peq. 
      subst. inv GMAP'. unfold data_label. simpl. 
      rewrite Ptrofs.unsigned_repr. apply alignw_aligned. auto.
      assert (dsize1 + align (init_data_list_size (gvar_init v)) alignw <= dsize).
      { eapply dsize_mono; eauto. }
      assert (0 <= align (init_data_list_size (gvar_init v)) alignw).
      { 
        apply Zle_trans with (init_data_list_size (gvar_init v)).
        generalize (init_data_list_size_pos (gvar_init v)). omega.
        apply alignw_le.
      }
      omega.
      eauto.
    + cbn in UPDATE.
      eapply IHdefs; eauto.
Qed.      

Lemma make_maps_sizes_pos : 
  forall prog gmap lmap dsize csize efsize,
    make_maps prog = (gmap, lmap, dsize, csize, efsize) ->
    dsize >= 0 /\ csize >= 0 /\ efsize >= 0.
Proof.
  intros prog0 gmap lmap dsize csize efsize H.
  unfold make_maps in H.
  assert (0 <= csize).  
  { eapply csize_mono; eauto. unfold alignw. red. exists 0. omega. }
  assert (0 <= dsize).  
  { eapply dsize_mono; eauto. }
  assert (0 <= efsize).  
  { eapply efsize_mono; eauto. }
  omega.
Qed.

Lemma one_le_ptrofs_max_unsigned : 1 <= Ptrofs.max_unsigned.
Proof.
  unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus.
  unfold Ptrofs.wordsize.
  generalize Wordsize_Ptrofs.wordsize_not_zero. intros.
  destruct Wordsize_Ptrofs.wordsize. congruence.
  rewrite two_power_nat_S. 
  generalize (two_power_nat_pos n). intros. omega.
Qed.

Lemma prog_odef_size_pos : forall defs id odef gdefs,
    defs ++ (id, odef) :: gdefs = AST.prog_defs prog ->
    def_not_empty odef.
Proof.
  intros defs id odef gdefs DEFSTAIL.
  unfold match_prog in TRANSF. unfold transf_program in TRANSF. repeat destr_in TRANSF.
  inv w. rewrite <- DEFSTAIL in wf_prog_not_empty. red in wf_prog_not_empty.
  rewrite Forall_forall in wf_prog_not_empty. 
  specialize (wf_prog_not_empty odef).
  cut (def_not_empty odef); auto. 
  apply wf_prog_not_empty. rewrite map_app. simpl. rewrite in_app. right. apply in_eq.
Qed.  

Lemma make_maps_ofs_ordering : 
  forall prog defs1 defs2 i1 i2 def1 def2 slbl1 slbl2
    gmap lmap dsize csize efsize 
    (SZMAX: dsize + csize + efsize <= Ptrofs.max_unsigned)
    (NORPT: list_norepet (map fst (AST.prog_defs prog)))
    (DEFS: AST.prog_defs prog = defs1 ++ defs2)
    (UPDATE: (gmap, lmap, dsize, csize, efsize) = make_maps prog)
    (IN1: In (i1, def1) defs1) 
    (IN2: In (i2, def2) defs2)
    (GMAP1: gmap i1 = Some slbl1)
    (GMAP2: gmap i2 = Some slbl2)
    (SAMESEG: fst slbl1 = fst slbl2),
    odef_size def1 + Ptrofs.unsigned (snd slbl1) <= Ptrofs.unsigned (snd slbl2).
Proof.
  intros. destruct def2 as [def2|].
  - apply in_split in IN2. destruct IN2 as (defs3 & defs4 & DEFS2).
    subst.
    exploit (update_map_gmap_some prog0 gmap lmap dsize csize efsize i2 
                                  (defs1 ++ defs3) defs4 def2); eauto.
    rewrite <- app_assoc. auto.
    intros (slbl & GMAP2' & BND1 & BND2).
    rewrite GMAP2' in GMAP2. inv GMAP2.
    rewrite Zplus_comm. eapply BND1; eauto.
    rewrite in_app. auto.
  - exploit update_map_gmap_none; eauto. rewrite DEFS.
    erewrite in_app. right. eauto. intros. congruence.
Qed.

Lemma code_size_upper_bound': 
  forall defs gmap lmap dsize csize efsize id f 
    gmap1 lmap1 dsize1 csize1 efsize1
    (CZPOS: 0 <= csize1)
    (UPDATE: update_maps gmap1 lmap1 dsize1 csize1 efsize1 defs = (gmap, lmap, dsize, csize, efsize))
    (IN: In (id, Some (Gfun (Internal f))) defs),
    code_size (Asm.fn_code f) <= csize.
Proof.
  induction defs. intros. inv IN.
  intros. inv IN.
  - unfold update_maps in UPDATE. simpl in UPDATE.
    destruct (update_instrs lmap1 csize1 id (Asm.fn_code f)) eqn:UPDATEINSTRS.
    assert (align z alignw <= csize).
    { eapply csize_mono; eauto. apply alignw_divides. }
    generalize (alignw_le z). intros.
    exploit update_instrs_code_size; eauto. intros. subst.
    omega.
  - unfold update_maps in UPDATE. simpl in UPDATE. destruct a.
    destruct (update_maps_def gmap1 lmap1 dsize1 csize1 efsize1 i o) eqn:EQ.
    destruct p. destruct p. destruct p.
    eapply (IHdefs _ _ _ _ _ _ _ g l z1 z0 z); eauto.
    assert (csize1 <= z0).
    { eapply update_csize_mono; eauto. }
    omega.
Qed.

Lemma code_size_upper_bound: 
  forall defs prog gmap lmap dsize csize efsize id f gdefs
    (MAKEMAPS: make_maps prog = (gmap, lmap, dsize, csize, efsize))
    (PROG: defs ++ (id, Some (Gfun (Internal f))) :: gdefs = AST.prog_defs prog),
    code_size (Asm.fn_code f) <= csize.
Proof.
  intros. unfold make_maps in MAKEMAPS.
  eapply code_size_upper_bound'; eauto. omega.
  rewrite <- PROG. rewrite in_app. right. apply in_eq.
Qed.

Lemma transf_prog_code_size_pos: forall prog tprog id f
    (TRANSF: transf_program prog = OK tprog)
    (IN: In (id, Some (Gfun (Internal f))) (AST.prog_defs prog)),
    0 < Asm.code_size (Asm.fn_code f).
Proof.
  intros. unfold transf_program in TRANSF0.
  repeat destr_in TRANSF0. destruct w.
  red in wf_prog_not_empty. 
  erewrite Forall_forall in wf_prog_not_empty; eauto.
  generalize (in_map snd (AST.prog_defs prog0) (id, Some (Gfun (Internal f))) IN).
  simpl. intros IN'. 
  exploit wf_prog_not_empty; eauto.
Qed.


Lemma alloc_globals_inject : 
  forall gdefs tgdefs defs m1 m2 m1' gmap lmap  code dsize csize efsize
    (DEFNAMES: list_norepet (map fst (AST.prog_defs prog)))
    (DEFSTAIL: defs ++ gdefs = AST.prog_defs prog)
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize, efsize))
    (BOUND: dsize + csize + efsize <= Ptrofs.max_unsigned)
    (TRANSPROG: transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog)
    (TRANSG: transl_globdefs gmap lmap gdefs = OK (tgdefs, code))
    (MINJ: Mem.weak_inject (globs_meminj gmap) (def_frame_inj m1) m1 m1')
    (ALLOCG: Genv.alloc_globals ge m1 gdefs = Some m2)
    (BLOCKEQ : Mem.nextblock m1 = Globalenvs.Genv.genv_next (partial_genv defs))
    (BLOCKEQ' : Mem.nextblock m1' = (pos_advance_N init_block (length (list_of_segments tprog))))
    (STK' : Mem.stack m1' = nil)
    (PERMOFS : forall b ofs k p, Mem.perm m1' b ofs k p -> 0 <= ofs < Ptrofs.max_unsigned)
    (OFSBOUND: forall id b def ofs k p, 
        Genv.find_symbol (partial_genv defs) id = Some b -> 
        In (id, (Some def)) defs -> Mem.perm m1 b ofs k p ->
        ofs < def_size def)
    (FINDVALIDSYM: forall id b ofs k p,
       Genv.find_symbol ge id = Some b ->
       Mem.perm m1 b ofs k p ->
       Genv.find_symbol (partial_genv defs) id = Some b)
    (DEFSPERM: forall id odef slbl b' delta,
       In (id, odef) gdefs ->
       gmap id = Some slbl ->
       Genv.symbol_block_offset tge slbl = (b', delta) ->
       (forall ofs k p, 0 <= ofs < odef_size odef -> Mem.perm m1' b' (delta+ofs) k p)),
    exists m2', alloc_globals tge (Genv.genv_segblocks tge) m1' tgdefs = Some m2'
           /\ Mem.weak_inject (globs_meminj gmap) (def_frame_inj m2) m2 m2'.
Proof.
  induction gdefs; intros.
  - monadInv TRANSG. inv ALLOCG. rewrite app_nil_r in DEFSTAIL. subst defs.
    simpl. eexists; split; eauto.
  - destruct a. destruct o. 
    + destruct g. destruct f.
      * (** the head of gdefs is an internal function **)
        monadInv TRANSG. destruct x; monadInv EQ. inv EQ2.
        simpl in ALLOCG. destr_match_in ALLOCG; try now inversion ALLOCG.
        destruct (Mem.alloc m1 0 1) eqn:ALLOCF.
        exploit Mem.alloc_result; eauto using ALLOCF. intros.
        exploit update_map_gmap_some; eauto. 
        intros (slbl & GMAP & OFSRANGE & OFSRANGE2).

        (* globs_meminj *)
        assert (globs_meminj gmap b = Some (gen_segblocks tprog (fst slbl), Ptrofs.unsigned (snd slbl))) as BINJ.
        {
          unfold globs_meminj. subst. rewrite BLOCKEQ.
          exploit genv_invert_symbol_next; eauto. intros INVSYM.
          setoid_rewrite INVSYM. rewrite GMAP.
          unfold Genv.symbol_block_offset. unfold Genv.label_to_block_offset.
          rewrite genv_gen_segblocks. auto.
        }

        (* alloc mapped injection *)
        exploit (Mem.alloc_left_mapped_weak_inject 
                   (globs_meminj gmap) (def_frame_inj m1) m1 m1' 0 1 m0
                   b (gen_segblocks tprog (fst slbl)) (Ptrofs.unsigned (snd slbl))
                   BINJ MINJ ALLOCF); eauto.
        (* valid block *)
        exploit AGREE_SMINJ_INSTR.update_map_gmap_range; eauto. intros.
        exploit (gen_segblocks_in_valid tprog); eauto. intros SEGBVALID.
        red in SEGBVALID. destruct SEGBVALID. red.
        rewrite BLOCKEQ'. auto.
        (* valid offset *)
        apply Ptrofs.unsigned_range_2.
        (* preservation of permission *)
        intros ofs k p OFS INJPERM.
        exploit (fun id odef slbl b' => DEFSPERM id odef slbl b' (Ptrofs.unsigned (snd slbl))); eauto. 
        apply in_eq.
        unfold Genv.symbol_block_offset. unfold Genv.label_to_block_offset.
        unfold tge. rewrite genv_gen_segblocks. auto.
        instantiate (1:=ofs).
        exploit prog_odef_size_pos; eauto. intros.
        assert (ofs = 0) by omega. subst. split; auto. omega.
        rewrite Zplus_comm. eauto.
        (* correct alignment *)
        red. intros.
        eapply update_map_gmap_aligned; eauto.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS & EFPOS). omega.
        omega.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS & EFPOS). omega.
        omega.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS & EFPOS). omega.
        omega.
        unfold default_gid_map. intros. congruence.
        (* alloced memory has not been injected before *)
        intros b0 delta' ofs k p GINJ PERM' OFSABSURD.
        unfold globs_meminj in GINJ.
        destr_match_in GINJ; try now inv GINJ.
        destr_match_in GINJ; try now inv GINJ.
        unfold Genv.symbol_block_offset in GINJ. unfold Genv.label_to_block_offset in GINJ.
        rewrite genv_gen_segblocks in GINJ.
        inv GINJ.
        assert (fst s = fst slbl).
        { 
          eapply gen_segblocks_injective; eauto. 
          apply gen_segblocks_in_valid; eauto. 
          eapply AGREE_SMINJ_INSTR.update_map_gmap_range; eauto.
        }
        apply Genv.invert_find_symbol in EQ2.
        exploit FINDVALIDSYM; eauto. intros.
        exploit find_symbol_inversion_1; eauto. intros (def' & IN).
        destruct def'.
        exploit OFSBOUND; eauto. intros.
        assert (Ptrofs.unsigned (snd s) + def_size g <= Ptrofs.unsigned (snd slbl)).
        { eapply (fun sl => OFSRANGE _ _ sl  IN); eauto. } 
        omega.

        assert (In (i0, None) (AST.prog_defs prog)).
        { rewrite <- DEFSTAIL. rewrite in_app. auto. }
        exploit update_map_gmap_none; eauto. congruence.
        (* stack frame is public *)
        intros fi INSTK o k pp PERM INJPERM.
        rewrite STK' in INSTK. inv INSTK.
        (* get the new weak injection *)
        intros MINJ'.
        erewrite alloc_pres_def_frame_inj in MINJ'; eauto.

        (* drop_perm injection *)
        exploit transf_prog_code_size_pos; eauto.
        rewrite <- DEFSTAIL. rewrite in_app. right. apply in_eq. intros.
        exploit (fun j g m1 m2 b1 b2 delta =>
                   Mem.drop_extended_parallel_weak_inject j g m1 m2 b1 b2 delta 
                                                          0 1 0 (Asm.code_size (Asm.fn_code f))); eauto using MINJ'. 
        (* inject perm *)
        red. simpl. auto. omega.
        (* hi *)
        omega.
        (* range perm *)
        simpl. red. intros ofs OFS.
        replace ofs with (Ptrofs.unsigned (snd slbl) + (ofs - (Ptrofs.unsigned (snd slbl)))) by omega.
        eapply DEFSPERM with (ofs:= ofs-Ptrofs.unsigned(snd slbl)); eauto. apply in_eq.
        unfold Genv.symbol_block_offset. unfold Genv.label_to_block_offset.
        unfold tge. erewrite genv_gen_segblocks; eauto.
        simpl. omega.
        (* source memory have no permission on extended regions *)
        intros b' delta' ofs' k p BINJ' PERM' OFS. destruct OFS. omega.
        unfold globs_meminj in BINJ'. destr_match_in BINJ'; inv BINJ'.
        destr_match_in H3; inv H3. erewrite genv_gen_segblocks in H2.
        generalize (gen_segblocks_injective tprog). intros SEGSINJ.
        red in SEGSINJ. 
        assert (fst s = fst slbl) as LBLEQ.
        { 
          eapply SEGSINJ; eauto.
          eapply gen_segblocks_in_valid; eauto.
          eapply AGREE_SMINJ_INSTR.update_map_gmap_range; eauto.
        }
        exploit Mem.perm_alloc_inv; eauto.
        destruct eq_block. 
        (** b' = Mem.nextblock m1 **)
        subst.
        rewrite BLOCKEQ in EQ2.
        erewrite genv_invert_symbol_next in EQ2; eauto. inv EQ2.
        rewrite GMAP in EQ3. inv EQ3. intros. omega.
        (** b' <> Mem.nextblock m1 **)
        intros PERM''.
        exploit FINDVALIDSYM; eauto. apply Genv.invert_find_symbol. exact EQ2. 
        intros FINDSYM'.
        exploit find_symbol_inversion_1; eauto. intros (def' & IN). destruct def'.
        exploit OFSBOUND; eauto. intros OFS'. 
        assert (Ptrofs.unsigned (snd s) + odef_size (Some g) <= Ptrofs.unsigned (snd slbl)) as SZBND.
        { eapply OFSRANGE; eauto. }
        simpl in SZBND. omega.
        exploit update_map_gmap_none; eauto.
        rewrite <- DEFSTAIL. rewrite in_app. left. apply IN.
        intros. congruence.
        (* introduce the weak injection *)
        intros (m2' & DROP & MINJ'').
        erewrite drop_perm_pres_def_frame_inj in MINJ''; eauto.

        (* apply the induction hypothesis *)
        assert ((defs ++ (i, Some (Gfun (Internal f))) :: nil) ++ gdefs = AST.prog_defs prog) as DEFSTAIL'.
        rewrite <- DEFSTAIL. rewrite <- app_assoc. simpl. auto.
        exploit (IHgdefs x0 (defs ++ (i, Some (Gfun (Internal f))) :: nil) m); eauto using MINJ'', DEFSTAIL'.
        (* nextblock *)
        erewrite Mem.nextblock_drop; eauto.
        erewrite Mem.nextblock_alloc; eauto. rewrite BLOCKEQ.      
        rewrite partial_genv_next. auto.
        (* nextblock' *)
        erewrite Mem.nextblock_drop; eauto.
        (* stack *)
        erewrite Mem.drop_perm_stack; eauto.
        (* perm ofs *)
        intros b0 ofs k p PERM.
        exploit Mem.perm_drop_4; eauto.
        (* ofsbound *)
        intros id b0 def ofs k p FINDSYM IN PERM'.
        rewrite in_app in IN. destruct IN as [IN | IN].
        assert (i <> id). 
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq in FINDSYM; eauto.
        assert (b <> b0). 
        {
          unfold not. subst. rewrite BLOCKEQ. intros. subst. 
          eapply Genv.find_symbol_genv_next_absurd; eauto.
        }
        erewrite (drop_perm_perm _ _ _ _ _ _ EQ) in PERM'. destruct PERM' as [PERM' PIN].
        exploit Mem.perm_alloc_inv; eauto using ALLOCF. 
        rewrite dec_eq_false; auto. intros. eapply OFSBOUND; eauto.

        inv IN. inv H1. 
        rewrite partial_genv_find_symbol_eq in FINDSYM. inv FINDSYM.
        rewrite <- BLOCKEQ in PERM'.
        erewrite (drop_perm_perm _ _ _ _ _ _ EQ) in PERM'. destruct PERM' as [PERM' PIN].
        exploit Mem.perm_alloc_inv; eauto using ALLOCF. 
        rewrite dec_eq_true. intros.
        simpl. assert (ofs = 0). omega. subst.
        eapply (prog_odef_size_pos defs id (Some (Gfun (Internal f)))); eauto.

        inv H1.
        (* findvalidsym *)
        intros id b0 ofs k p FINDSYM PERM.
        erewrite drop_perm_perm in PERM; eauto. destruct PERM as [PERM COND].
        erewrite alloc_perm in PERM; eauto. destruct peq.
        subst. rewrite BLOCKEQ.
        rewrite BLOCKEQ in FINDSYM. apply Genv.find_invert_symbol in FINDSYM.
        unfold ge in FINDSYM. erewrite genv_invert_symbol_next in FINDSYM; eauto. inv FINDSYM.
        erewrite partial_genv_find_symbol_eq; eauto.
        exploit FINDVALIDSYM; eauto. intros FINDSYM'.
        apply find_symbol_inversion_1 in FINDSYM'. destruct FINDSYM' as [DEF' FINDSYM'].
        assert (i <> id). 
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq; eauto.
        (* defs perm *)
        intros id odef slbl0 b' delta IN GMAP' SYMOFS ofs k p OFS.
        eapply Mem.perm_drop_3; eauto. 
        destruct (eq_block b' (gen_segblocks tprog (fst slbl))); auto.
        right. right.
        unfold Genv.symbol_block_offset in SYMOFS. unfold Genv.label_to_block_offset in SYMOFS. inv SYMOFS.
        unfold tge in H2. rewrite genv_gen_segblocks in H2.
        assert (odef_size (Some (Gfun (Internal f))) + Ptrofs.unsigned (snd slbl) <= Ptrofs.unsigned (snd slbl0)) as SZBND.
        { 
          eapply (make_maps_ofs_ordering prog (defs ++ (i, Some (Gfun (Internal f))) :: nil) gdefs
                                           i id (Some (Gfun (Internal f))) odef); eauto.
          rewrite in_app. right. apply in_eq.
          generalize (gen_segblocks_injective tprog). unfold injective_on_valid_segs.
          intros INJECTIVE. eapply INJECTIVE; eauto.
          eapply gen_segblocks_in_valid; eauto.
          eapply AGREE_SMINJ_INSTR.update_map_gmap_range; eauto.
        }
        simpl in SZBND.
        exploit prog_odef_size_pos; eauto. intros. simpl in H. omega.
        eapply DEFSPERM; eauto. apply in_cons; auto.

        (* finish this case *)
        intros (m3' & ALLOCG' & MINJ_FINAL).
        exists m3'. split; auto. simpl. 
        exploit transl_fun_inversion; eauto.
        intros (slbl' & GMAP' & FRANGE).
        rewrite GMAP in GMAP'. inv GMAP'. rewrite FRANGE. simpl.
        unfold tge. rewrite genv_gen_segblocks. setoid_rewrite Ptrofs.unsigned_repr.
        rewrite Z.add_comm. setoid_rewrite DROP. auto. 
        simpl. 
        assert (code_size (Asm.fn_code f) <= csize). 
        eapply code_size_upper_bound; eauto.
        exploit make_maps_sizes_pos; eauto. intros (DSZPOS & CSZPOS & EFSZPOS).
        omega.

      * (** the head of gdefs is an external function **)
        monadInv TRANSG. destruct (gmap i) eqn:ILBL; try now inversion EQ.
        destruct s. monadInv EQ. monadInv EQ2.
        simpl in ALLOCG. destr_match_in ALLOCG; try now inversion ALLOCG.
        destruct (Mem.alloc m1 0 1) eqn:ALLOCF.
        exploit Mem.alloc_result; eauto using ALLOCF. intros.
        exploit update_map_gmap_some; eauto. 
        intros (slbl & GMAP & OFSRANGE & OFSRANGE2).

        (* globs_meminj *)
        assert (globs_meminj gmap b = Some (gen_segblocks tprog (fst slbl), Ptrofs.unsigned (snd slbl))) as BINJ.
        {
          unfold globs_meminj. subst. rewrite BLOCKEQ.
          exploit genv_invert_symbol_next; eauto. intros INVSYM.
          setoid_rewrite INVSYM. rewrite GMAP.
          unfold Genv.symbol_block_offset. unfold Genv.label_to_block_offset.
          rewrite genv_gen_segblocks. auto.
        }

        (* alloc mapped injection *)
        exploit (Mem.alloc_left_mapped_weak_inject 
                   (globs_meminj gmap) (def_frame_inj m1) m1 m1' 0 1 m0
                   b (gen_segblocks tprog (fst slbl)) (Ptrofs.unsigned (snd slbl))
                   BINJ MINJ ALLOCF); eauto.
        (* valid block *)
        exploit AGREE_SMINJ_INSTR.update_map_gmap_range; eauto. intros.
        exploit (gen_segblocks_in_valid tprog); eauto. intros SEGBVALID.
        red in SEGBVALID. destruct SEGBVALID. red.
        rewrite BLOCKEQ'. auto.
        (* valid offset *)
        apply Ptrofs.unsigned_range_2.
        (* preservation of permission *)
        intros ofs k p OFS INJPERM.
        exploit (fun id odef slbl b' => DEFSPERM id odef slbl b' (Ptrofs.unsigned (snd slbl))); eauto. 
        apply in_eq.
        unfold Genv.symbol_block_offset. unfold Genv.label_to_block_offset.
        unfold tge. rewrite genv_gen_segblocks. auto.
        instantiate (1:=ofs).
        exploit prog_odef_size_pos; eauto. intros.
        rewrite Zplus_comm. eauto.
        (* correct alignment *)
        red. intros.
        eapply update_map_gmap_aligned; eauto.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS & EFPOS). omega.
        omega.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS & EFPOS). omega.
        omega.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS & EFPOS). omega.
        omega.
        unfold default_gid_map. intros. congruence.
        (* alloced memory has not been injected before *)
        intros b0 delta' ofs k p GINJ PERM' OFSABSURD.
        unfold globs_meminj in GINJ.
        destr_match_in GINJ; try now inv GINJ.
        destr_match_in GINJ; try now inv GINJ.
        unfold Genv.symbol_block_offset in GINJ. unfold Genv.label_to_block_offset in GINJ.
        rewrite genv_gen_segblocks in GINJ.
        inv GINJ.
        assert (fst s0 = fst slbl).
        { 
          eapply gen_segblocks_injective; eauto. 
          apply gen_segblocks_in_valid; eauto. 
          eapply AGREE_SMINJ_INSTR.update_map_gmap_range; eauto.
        }
        apply Genv.invert_find_symbol in EQ0.
        exploit FINDVALIDSYM; eauto. intros.
        exploit find_symbol_inversion_1; eauto. intros (def' & IN).
        destruct def'.
        exploit OFSBOUND; eauto. intros.
        assert (Ptrofs.unsigned (snd s0) + def_size g <= Ptrofs.unsigned (snd slbl)).
        { eapply (fun sl => OFSRANGE _ _ sl  IN); eauto. } 
        omega.

        assert (In (i1, None) (AST.prog_defs prog)).
        { rewrite <- DEFSTAIL. rewrite in_app. auto. }
        exploit update_map_gmap_none; eauto. congruence.
        (* stack frame is public *)
        intros fi INSTK o k pp PERM INJPERM.
        rewrite STK' in INSTK. inv INSTK.
        (* get the new weak injection *)
        intros MINJ'.
        erewrite alloc_pres_def_frame_inj in MINJ'; eauto.

        (* drop_perm injection *)
        exploit Mem.drop_parallel_weak_inject; eauto using MINJ'. 
        red. simpl. auto. 
        intros (m2' & DROP & MINJ'').
        erewrite drop_perm_pres_def_frame_inj in MINJ''; eauto.

        (* apply the induction hypothesis *)
        assert ((defs ++ (i, Some (Gfun (External e))) :: nil) ++ gdefs = AST.prog_defs prog) as DEFSTAIL'.
        rewrite <- DEFSTAIL. rewrite <- app_assoc. simpl. auto.
        exploit (IHgdefs x0 (defs ++ (i, Some (Gfun (External e))) :: nil) m); eauto using MINJ'', DEFSTAIL'.
        (* nextblock *)
        erewrite Mem.nextblock_drop; eauto.
        erewrite Mem.nextblock_alloc; eauto. rewrite BLOCKEQ.      
        rewrite partial_genv_next. auto.
        (* nextblock' *)
        erewrite Mem.nextblock_drop; eauto.
        (* stack *)
        erewrite Mem.drop_perm_stack; eauto.
        (* perm ofs *)
        intros b0 ofs k p PERM.
        exploit Mem.perm_drop_4; eauto.
        (* ofsbound *)
        intros id b0 def ofs k p FINDSYM IN PERM'.
        rewrite in_app in IN. destruct IN as [IN | IN].
        assert (i <> id). 
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq in FINDSYM; eauto.
        assert (b <> b0). 
        {
          unfold not. subst. rewrite BLOCKEQ. intros. subst. 
          eapply Genv.find_symbol_genv_next_absurd; eauto.
        }
        erewrite (drop_perm_perm _ _ _ _ _ _ EQ) in PERM'. destruct PERM' as [PERM' PIN].
        exploit Mem.perm_alloc_inv; eauto using ALLOCF. 
        rewrite dec_eq_false; auto. intros. eapply OFSBOUND; eauto.

        inv IN. inv H0. 
        rewrite partial_genv_find_symbol_eq in FINDSYM. inv FINDSYM.
        rewrite <- BLOCKEQ in PERM'.
        erewrite (drop_perm_perm _ _ _ _ _ _ EQ) in PERM'. destruct PERM' as [PERM' PIN].
        exploit Mem.perm_alloc_inv; eauto using ALLOCF. 
        rewrite dec_eq_true. intros.
        simpl. assert (ofs = 0). omega. subst.
        omega.

        inv H0.
        (* findvalidsym *)
        intros id b0 ofs k p FINDSYM PERM.
        erewrite drop_perm_perm in PERM; eauto. destruct PERM as [PERM COND].
        erewrite alloc_perm in PERM; eauto. destruct peq.
        subst. rewrite BLOCKEQ.
        rewrite BLOCKEQ in FINDSYM. apply Genv.find_invert_symbol in FINDSYM.
        unfold ge in FINDSYM. erewrite genv_invert_symbol_next in FINDSYM; eauto. inv FINDSYM.
        erewrite partial_genv_find_symbol_eq; eauto.
        exploit FINDVALIDSYM; eauto. intros FINDSYM'.
        apply find_symbol_inversion_1 in FINDSYM'. destruct FINDSYM' as [DEF' FINDSYM'].
        assert (i <> id). 
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq; eauto.
        (* defs perm *)
        intros id odef slbl0 b' delta IN GMAP' SYMOFS ofs k p OFS.
        eapply Mem.perm_drop_3; eauto. 
        destruct (eq_block b' (gen_segblocks tprog (fst slbl))); auto.
        right. right.
        unfold Genv.symbol_block_offset in SYMOFS. unfold Genv.label_to_block_offset in SYMOFS. inv SYMOFS.
        unfold tge in H1. rewrite genv_gen_segblocks in H1.
        assert (odef_size (Some (Gfun (External e))) + Ptrofs.unsigned (snd slbl) <= Ptrofs.unsigned (snd slbl0)) as SZBND.
        { 
          eapply (make_maps_ofs_ordering prog (defs ++ (i, Some (Gfun (External e))) :: nil) gdefs
                                           i id (Some (Gfun (External e))) odef); eauto.
          rewrite in_app. right. apply in_eq.
          generalize (gen_segblocks_injective tprog). unfold injective_on_valid_segs.
          intros INJECTIVE. eapply INJECTIVE; eauto.
          eapply gen_segblocks_in_valid; eauto.
          eapply AGREE_SMINJ_INSTR.update_map_gmap_range; eauto.
        }
        assert (odef_size (Some (Gfun (External e))) = 1) as EFSIZE by reflexivity.
        rewrite EFSIZE in SZBND. omega.
        eapply DEFSPERM; eauto. apply in_cons; auto.

        (* finish this case *)
        intros (m3' & ALLOCG' & MINJ_FINAL).
        exists m3'. split; auto. simpl.
        rewrite GMAP in ILBL. inv ILBL.
        unfold tge. rewrite genv_gen_segblocks. setoid_rewrite Ptrofs.unsigned_repr.
        rewrite Z.add_comm. setoid_rewrite DROP. auto. 
        generalize one_le_ptrofs_max_unsigned. omega.
 
      * (** the head of gdefs is a global variable **)
        monadInv TRANSG. destruct (gmap i) eqn:ILBL; try now inversion EQ.
        destruct s. monadInv EQ. monadInv EQ2.
        simpl in ALLOCG. 
        destr_match_in ALLOCG; try now inversion ALLOCG.
        destr_match_in EQ.
        destr_match_in EQ; try now inversion EQ.
        destr_match_in EQ; try now inversion EQ.
        rename EQ2 into ALLOCINIT.
        rename EQ3 into STOREZERO.
        rename EQ4 into STOREINIT.
        rename EQ into DROP.
        exploit Mem.alloc_result; eauto using ALLOCINIT. intros.
        exploit update_map_gmap_some; eauto. 
        intros (slbl & GMAP & OFSRANGE & OFSRANGE2).

        (* globs_meminj *)
        assert (globs_meminj gmap b = Some (gen_segblocks tprog (fst slbl), Ptrofs.unsigned (snd slbl))) as BINJ.
        {
          unfold globs_meminj. subst. rewrite BLOCKEQ.
          exploit genv_invert_symbol_next; eauto. intros INVSYM.
          setoid_rewrite INVSYM. rewrite GMAP.
          unfold Genv.symbol_block_offset. unfold Genv.label_to_block_offset.
          rewrite genv_gen_segblocks. auto.
        }

        (* alloc mapped injection *)
        exploit (Mem.alloc_left_mapped_weak_inject 
                   (globs_meminj gmap) (def_frame_inj m1) m1 m1' 0 (init_data_list_size (gvar_init v)) m0
                   b (gen_segblocks tprog (fst slbl)) (Ptrofs.unsigned (snd slbl))
                   BINJ MINJ ALLOCINIT); eauto.
        (* valid block *)
        exploit AGREE_SMINJ_INSTR.update_map_gmap_range; eauto. intros.
        exploit (gen_segblocks_in_valid tprog); eauto. intros SEGBVALID.
        red in SEGBVALID. destruct SEGBVALID. red.
        rewrite BLOCKEQ'. auto.
        (* valid offset *)
        apply Ptrofs.unsigned_range_2.
        (* preservation of permission *)
        intros ofs k p OFS INJPERM.
        exploit (fun id odef slbl b' => DEFSPERM id odef slbl b' (Ptrofs.unsigned (snd slbl))); eauto. 
        apply in_eq.
        unfold Genv.symbol_block_offset. unfold Genv.label_to_block_offset.
        unfold tge. rewrite genv_gen_segblocks. auto.
        instantiate (1:=ofs).
        exploit prog_odef_size_pos; eauto. intros.
        rewrite Zplus_comm. eauto.
        (* correct alignment *)
        red. intros.
        eapply update_map_gmap_aligned; eauto.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS & EFPOS). omega.
        omega.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS & EFPOS). omega.
        omega.
        unfold alignw. red. exists 0. omega.
        exploit make_maps_sizes_pos; eauto. intros (DPOS & CPOS & EFPOS). omega.
        omega.
        unfold default_gid_map. intros. congruence.
        (* alloced memory has not been injected before *)
        intros b0 delta' ofs k p GINJ PERM' OFSABSURD.
        unfold globs_meminj in GINJ.
        destr_match_in GINJ; try now inv GINJ.
        destr_match_in GINJ; try now inv GINJ.
        unfold Genv.symbol_block_offset in GINJ. unfold Genv.label_to_block_offset in GINJ. 
        rewrite genv_gen_segblocks in GINJ. inv GINJ.
        assert (fst s0 = fst slbl).
        { 
          eapply gen_segblocks_injective; eauto. 
          apply gen_segblocks_in_valid; eauto. 
          eapply AGREE_SMINJ_INSTR.update_map_gmap_range; eauto.
        }
        apply Genv.invert_find_symbol in EQ.
        exploit FINDVALIDSYM; eauto. intros.
        exploit find_symbol_inversion_1; eauto. intros (def' & IN).
        destruct def'.
        exploit OFSBOUND; eauto. intros.
        assert (Ptrofs.unsigned (snd s0) + def_size g <= Ptrofs.unsigned (snd slbl)).
        { eapply (fun sl => OFSRANGE _ _ sl IN); eauto. } 
        omega.

        assert (In (i1, None) (AST.prog_defs prog)).
        { rewrite <- DEFSTAIL. rewrite in_app. auto. }
        exploit update_map_gmap_none; eauto. congruence.
        (* stack frame is public *)
        intros fi INSTK o k pp PERM INJPERM.
        rewrite STK' in INSTK. inv INSTK.
        (* get the new weak injection *)
        intros MINJ'.
        erewrite alloc_pres_def_frame_inj in MINJ'; eauto.

        (* store_zeros injection *)
        exploit store_zeros_mapped_inject; eauto.
        intros (m2' & STOREZERO' & MINJZ).       
        erewrite (store_zeros_pres_def_frame_inj m0) in MINJZ; eauto.
        
        (* store_init_data_list inject *)
        exploit store_init_data_list_mapped_inject; eauto. 
        intros (m3' & STOREINIT' & MINJSI).        
        erewrite store_init_data_list_pres_def_frame_inj in MINJSI; eauto.
        
        (* dorp_perm inject *)
        exploit Mem.drop_parallel_weak_inject; eauto.
        red. simpl. auto.
        intros (m4' & DROP' & MINJDR).
        erewrite drop_perm_pres_def_frame_inj in MINJDR; eauto.
        
        (* apply the induction hypothesis *)
        assert ((defs ++ (i, Some (Gvar v)) :: nil) ++ gdefs = AST.prog_defs prog) as DEFSTAIL'.
        rewrite <- DEFSTAIL. rewrite <- app_assoc. simpl. auto.
        exploit (IHgdefs x0 (defs ++ (i, Some (Gvar v)) :: nil) m); eauto using MINJDR, DEFSTAIL'.
        (* nextblock *)
        erewrite Mem.nextblock_drop; eauto.
        erewrite Genv.store_init_data_list_nextblock; eauto.
        erewrite Genv.store_zeros_nextblock; eauto.
        erewrite Mem.nextblock_alloc; eauto. rewrite BLOCKEQ.      
        rewrite partial_genv_next. auto.
        (* nextblock' *)
        erewrite (Mem.nextblock_drop m3'); eauto.
        erewrite (store_init_data_list_nextblock _ _ m2'); eauto.
        erewrite Genv.store_zeros_nextblock; eauto.
        (* stack *)
        erewrite (Mem.drop_perm_stack m3'); eauto.
        erewrite (store_init_data_list_stack _ _ m2'); eauto.
        erewrite (Genv.store_zeros_stack m1'); eauto.
        (* perm ofs *)
        intros b0 ofs k p PERM.
        exploit Mem.perm_drop_4; eauto. intros PERM'.
        erewrite <- (store_init_data_list_perm _ _ m2') in PERM'; eauto.
        erewrite <- (Genv.store_zeros_perm _ _ _ _ m1') in PERM'; eauto. 
        (* perm *)
        intros id b0 def ofs k p FINDSYM IN PERM'.
        rewrite in_app in IN. destruct IN as [IN | IN].

        assert (i <> id). 
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq in FINDSYM; eauto.
        assert (b <> b0). 
        {
          unfold not. subst. rewrite BLOCKEQ. intros. subst. 
          eapply Genv.find_symbol_genv_next_absurd; eauto.
        }
        erewrite (drop_perm_perm _ _ _ _ _ _ DROP) in PERM'. destruct PERM' as [PERM' PIN].
        erewrite <- (Genv.store_init_data_list_perm _ _ _ _ _ _ _ _ _ STOREINIT) in PERM'; eauto.
        erewrite <- (Genv.store_zeros_perm _ _ _ _ _ _ _ _ STOREZERO) in PERM'; eauto.
        exploit Mem.perm_alloc_inv; eauto using ALLOCINIT. 
        rewrite dec_eq_false; auto. intros. eapply OFSBOUND; eauto.

        inv IN. inv H0. 
        rewrite partial_genv_find_symbol_eq in FINDSYM. inv FINDSYM.
        rewrite <- BLOCKEQ in PERM'.
        erewrite (drop_perm_perm _ _ _ _ _ _ DROP) in PERM'. destruct PERM' as [PERM' PIN].
        erewrite <- (Genv.store_init_data_list_perm _ _ _ _ _ _ _ _ _ STOREINIT) in PERM'; eauto.
        erewrite <- (Genv.store_zeros_perm _ _ _ _ _ _ _ _ STOREZERO) in PERM'; eauto.
        exploit Mem.perm_alloc_inv; eauto using ALLOCINIT. 
        rewrite dec_eq_true. intros.
        simpl. omega. 

        inv H0.
        
        (* findvalidsym *)
        intros id b0 ofs k p FINDSYM PERM.
        erewrite drop_perm_perm in PERM; eauto. destruct PERM as [PERM COND].
        erewrite <- Genv.store_init_data_list_perm in PERM; eauto.
        erewrite <- Genv.store_zeros_perm in PERM; eauto.
        erewrite alloc_perm in PERM; eauto. destruct peq.
        subst. rewrite BLOCKEQ.
        rewrite BLOCKEQ in FINDSYM. apply Genv.find_invert_symbol in FINDSYM.
        unfold ge in FINDSYM. erewrite genv_invert_symbol_next in FINDSYM; eauto. inv FINDSYM.
        erewrite partial_genv_find_symbol_eq; eauto.
        exploit FINDVALIDSYM; eauto. intros FINDSYM'.
        apply find_symbol_inversion_1 in FINDSYM'. destruct FINDSYM' as [DEF' FINDSYM'].
        assert (i <> id).
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq; eauto.
        (* defs perm *)
        intros id odef slbl0 b' delta IN GMAP' SYMOFS ofs k p OFS.
        eapply Mem.perm_drop_3; eauto. 
        destruct (eq_block b' (gen_segblocks tprog (fst slbl))); auto.
        right. right.
        unfold Genv.symbol_block_offset in SYMOFS. unfold Genv.label_to_block_offset in SYMOFS. inv SYMOFS.
        unfold tge in H1. rewrite genv_gen_segblocks in H1.
        assert (odef_size (Some (Gvar v)) + Ptrofs.unsigned (snd slbl) <= Ptrofs.unsigned (snd slbl0)) as SZBND.
        { 
          eapply (make_maps_ofs_ordering prog (defs ++ (i, Some (Gvar v)) :: nil) gdefs
                                           i id (Some (Gvar v)) odef); eauto.
          rewrite in_app. right. apply in_eq.
          generalize (gen_segblocks_injective tprog). unfold injective_on_valid_segs.
          intros INJECTIVE. eapply INJECTIVE; eauto.
          eapply gen_segblocks_in_valid; eauto.
          eapply AGREE_SMINJ_INSTR.update_map_gmap_range; eauto.          
        }
        assert (odef_size (Some (Gvar v)) = init_data_list_size (gvar_init v)) as EFSIZE by reflexivity.
        rewrite EFSIZE in SZBND. omega.
        erewrite <- store_init_data_list_perm; eauto.
        erewrite <- Genv.store_zeros_perm; eauto.
        eapply DEFSPERM; eauto. apply in_cons; auto.

        (* Finish this case *)
        intros (m5' & ALLOCG' & MINJ_FINAL).
        exists m5'. split; auto. simpl.
        rewrite GMAP in ILBL. inv ILBL.
        unfold tge. rewrite genv_gen_segblocks. 
        erewrite <- transl_gvar_pres_size; eauto.
        setoid_rewrite STOREZERO'.
        unfold tge in STOREINIT'. setoid_rewrite STOREINIT'.
        rewrite Z.add_comm. 
        erewrite <- transl_gvar_pres_perm; eauto.
        setoid_rewrite DROP'. auto.
        
    + (* THE head of gdefs is None *)
      monadInv TRANSG. simpl in ALLOCG.
      set (mz := Mem.alloc m1 0 0) in *. destruct mz eqn:ALLOCZ. subst mz.
      eapply (IHgdefs tgdefs (defs ++ (i, None) :: nil) m m2); eauto.
      rewrite <- DEFSTAIL. rewrite List.app_assoc_reverse. simpl. auto.
      assert (gmap i = None).
      { 
        eapply update_map_gmap_none; eauto. 
        rewrite <- DEFSTAIL. apply in_app. right. apply in_eq.
      }

      (* globs_meminj *)
      assert (globs_meminj gmap b = None) as BINJ.
      {
        exploit Mem.alloc_result; eauto using ALLOCZ. intros. subst b.
        unfold globs_meminj. rewrite BLOCKEQ.       
        erewrite genv_invert_symbol_next; eauto. rewrite H. congruence.
      }

      exploit Mem.alloc_left_unmapped_weak_inject; eauto using MINJ.
      intros MINJ'.
      erewrite alloc_pres_def_frame_inj in MINJ'; eauto.
      (* next block *)
      unfold partial_genv. rewrite Genv.add_globals_app. simpl.
      exploit Mem.nextblock_alloc; eauto. intros NB. rewrite NB. f_equal.
      rewrite BLOCKEQ. unfold partial_genv. auto.

      (* perm *)
        intros id b0 def ofs k p FINDSYM IN PERM'.
        rewrite in_app in IN. destruct IN as [IN | IN].

        assert (i <> id). 
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq in FINDSYM; eauto.
        assert (b <> b0). 
        {
          exploit Mem.alloc_result; eauto using ALLOCZ. intros. subst b.
          unfold not. rewrite BLOCKEQ. intros. subst. 
          eapply Genv.find_symbol_genv_next_absurd; eauto.
        }
        exploit Mem.perm_alloc_inv; eauto using ALLOCZ. 
        rewrite dec_eq_false; auto. intros. eapply OFSBOUND; eauto.

        inv IN. inv H. 

        inv H.

        (* findvalidsym *)
        intros id b0 ofs k p FINDSYM PERM.
        erewrite alloc_perm in PERM; eauto. destruct peq.
        subst. exploit Mem.alloc_result; eauto using ALLOCZ. intros. subst.
        rewrite BLOCKEQ.
        rewrite BLOCKEQ in FINDSYM. apply Genv.find_invert_symbol in FINDSYM.
        unfold ge in FINDSYM. erewrite genv_invert_symbol_next in FINDSYM; eauto. inv FINDSYM.
        erewrite partial_genv_find_symbol_eq; eauto.
        exploit FINDVALIDSYM; eauto. intros FINDSYM'.
        apply find_symbol_inversion_1 in FINDSYM'. destruct FINDSYM' as [DEF' FINDSYM'].
        assert (i <> id). 
        {
          eapply defs_names_distinct_prefix_neq; eauto.
          rewrite <- DEFSTAIL in DEFNAMES. eauto.
        }
        erewrite partial_genv_find_symbol_neq; eauto.
        (* defs perm *)
        intros id odef slbl0 b' delta IN GMAP' SYMOFS ofs k p OFS.
        eapply DEFSPERM; eauto. apply in_cons; auto.
Qed.

Lemma globs_meminj_domain_valid : forall gmap lmap dsize csize efsize m2 b p
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize, efsize))
    (ALLOCG: Genv.alloc_globals ge Mem.empty (AST.prog_defs prog) = Some m2)
    (TRANSPROG: transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog)
    (INJ: globs_meminj gmap b = Some p),
    Mem.valid_block m2 b. 
Proof.
  intros. unfold globs_meminj in INJ. 
  destr_match_in INJ; inv INJ. destr_match_in H0; inv H0.
  assert (Genv.init_mem prog = Some m2) as INITM by auto.
  apply Genv.invert_find_symbol in EQ.
  eapply Genv.find_symbol_not_fresh; eauto.
Qed.

Lemma alloc_all_globals_inject : 
  forall tgdefs m2 m1' gmap lmap  code dsize csize efsize
    (DEFNAMES: list_norepet (map fst (AST.prog_defs prog)))
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize, efsize))
    (TRANSPROG: transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog)
    (TRANSG: transl_globdefs gmap lmap (AST.prog_defs prog) = OK (tgdefs, code))
    (BOUND: dsize + csize + efsize <= Ptrofs.max_unsigned)
    (MINJ: Mem.weak_inject (globs_meminj gmap) (def_frame_inj Mem.empty) Mem.empty m1')
    (BLOCKEQ: Mem.nextblock m1' = (pos_advance_N init_block (length (list_of_segments tprog))))
    (STK: Mem.stack m1' = nil)
    (PERMOFS : forall b ofs k p, Mem.perm m1' b ofs k p -> 0 <= ofs < Ptrofs.max_unsigned)
    (DEFSPERM: forall id odef slbl b' delta,
       In (id, odef) (AST.prog_defs prog) ->
       gmap id = Some slbl ->
       Genv.symbol_block_offset tge slbl = (b', delta) ->
       (forall ofs k p, 0 <= ofs < odef_size odef -> Mem.perm m1' b' (delta+ofs) k p))
    (ALLOCG: Genv.alloc_globals ge Mem.empty (AST.prog_defs prog) = Some m2),
    exists m2', alloc_globals tge (Genv.genv_segblocks tge) m1' tgdefs = Some m2'
           /\ Mem.inject (globs_meminj gmap) (def_frame_inj m2) m2 m2'.
Proof.
  intros. exploit (alloc_globals_inject (AST.prog_defs prog) tgdefs nil); eauto.
  rewrite Mem.nextblock_empty; eauto.
  intros id b def ofs k p FINDSYM IN PERM. inv IN.
  intros id b ofs k p FINDSYM PERM.
  exploit Mem.perm_empty; eauto. contradiction.
  intros (m2' & ALLOCG' & WINJ). exists m2'. split; auto.
  eapply Mem.weak_inject_to_inject; eauto.
  intros. eapply globs_meminj_domain_valid; eauto.
Qed.


Lemma globs_meminj_ofs_pos : forall gmap b b' delta,
    globs_meminj gmap b = Some (b', delta) -> delta >= 0.
Proof.
  unfold globs_meminj. intros. destr_match_in H; inv H.
  destr_match_in H1; inv H1. generalize (Ptrofs.unsigned_range (snd s)).
  omega.
Qed.


Lemma alloc_segments_weak_inject: forall gmap lmap dsize csize efsize m
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize, efsize))
    (TRANSPROG: transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog)
    (NEXTBLOCK: Mem.nextblock m = init_block)
    (STACK: Mem.stack m = nil),
    Mem.weak_inject (globs_meminj gmap) (def_frame_inj Mem.empty) 
                    Mem.empty (alloc_segments m (list_of_segments tprog)).
Proof.
  intros. unfold def_frame_inj. erewrite Mem.empty_stack; eauto.
  eapply Mem.empty_weak_inject; eauto.
  - erewrite  alloc_segments_stack; eauto.
  - intros b b' delta H. eapply globs_meminj_ofs_pos; eauto.
  - intros b b' delta H. unfold globs_meminj in H.
    destr_match_in H; inv H.
    destr_match_in H1; inv H1. 
    exploit AGREE_SMINJ_INSTR.update_map_gmap_range; eauto. intros IN.
    generalize TRANSF. intros TRANSF'.
    red in TRANSF'. unfold transf_program in TRANSF'. repeat destr_in TRANSF'. inv UPDATE.
    destruct w.
    exploit gen_segblocks_in_valid; eauto. intros SEGBVALID.
    red in SEGBVALID. destruct SEGBVALID.
    red. rewrite genv_gen_segblocks.
    unfold init_block in H1. simpl in H1.
    erewrite alloc_segments_nextblock; eauto.
    rewrite NEXTBLOCK. unfold init_block. simpl.
    auto.
Qed.

Lemma alloc_global_ext : forall f1 f2 ge m def,
    (forall x, f1 x = f2 x) -> alloc_global ge f1 m def = alloc_global ge f2 m def.
Proof.
  intros f1 f2 ge0 m def H.
  destruct def. destruct p. destruct o. destruct g.
  - simpl. rewrite (H (segblock_id s)). auto.
  - simpl. rewrite (H (segblock_id s)). auto.
  - simpl. auto.
Qed.

Lemma alloc_globals_ext : forall defs f1 f2 ge m,
    (forall x, f1 x = f2 x) -> alloc_globals ge f1 m defs = alloc_globals ge f2 m defs.
Proof.
  induction defs. intros.
  - simpl. auto.
  - intros f1 f2 ge0 m H. simpl. erewrite alloc_global_ext; eauto. 
    destr_match. erewrite IHdefs; eauto. auto.
Qed.

Definition find_segsize (segs: list segment) id : option ptrofs :=
  match (List.find (fun s => ident_eq (segid s) id) segs) with
  | None => None
  | Some s => Some (segsize s)
  end.

Definition gen_segs dsize csize efsize : list segment :=
  (mkSegment data_segid (Ptrofs.repr dsize)) 
    :: (mkSegment code_segid (Ptrofs.repr csize))
    :: (mkSegment extfuns_segid (Ptrofs.repr efsize)) :: nil.

Lemma update_maps_gmap_ofs_le_segsize :
  forall defs (gmap : GID_MAP_TYPE) (lmap : LABEL_MAP_TYPE) (dsize csize efsize : Z) (id : ident)
    def slbl
    gmap1 lmap1 dsize1 csize1 efsize1
    (DZLBND: dsize1 >= 0)
    (DZUBND: dsize <= Ptrofs.max_unsigned)
    (CZALNG: (alignw | csize1))
    (CZLBND: csize1 >= 0)
    (CZUBND: csize <= Ptrofs.max_unsigned)
    (EFZLBND: efsize1 >= 0)
    (EFZUBND: efsize <= Ptrofs.max_unsigned)
    (UPDATE: update_maps gmap1 lmap1 dsize1 csize1 efsize1 defs = (gmap, lmap, dsize, csize, efsize))
    (NORPT: list_norepet (map fst defs))
    (IN: In (id, Some def) defs)
    (GMAP: gmap id = Some slbl),
    exists sz, find_segsize (gen_segs dsize csize efsize) (fst slbl) = Some sz /\
          (Ptrofs.unsigned (snd slbl)) + (def_size def) <= Ptrofs.unsigned sz.
Proof.
  induction defs. intros.
  - inv IN.
  - intros. 
    assert (dsize1 <= dsize) as DSZLE. eapply dsize_mono; eauto.
    assert (csize1 <= csize) as CSZLE. eapply csize_mono; eauto.
    assert (efsize1 <= efsize) as EFSZLE. eapply efsize_mono; eauto.
    inv IN. 
    + destruct def. destruct f.
      * unfold update_maps in UPDATE. simpl in UPDATE.
        destruct (update_instrs lmap1 csize1 id (Asm.fn_code f)) eqn:UPDINSTRS.
        exploit update_instrs_code_size; eauto. intros. subst. simpl. 
        inv NORPT. exploit update_gmap_not_in; eauto.
        intros GMAP'. rewrite GMAP in GMAP'.
        unfold update_gid_map in GMAP'. rewrite peq_true in GMAP'. inv GMAP'.
        unfold code_label. simpl. 
        exists (Ptrofs.repr csize). split; auto.
        repeat rewrite Ptrofs.unsigned_repr.
        apply Zle_trans with (align (csize1 + code_size (Asm.fn_code f)) alignw).
        apply alignw_le. eapply csize_mono; eauto. apply alignw_divides.
        split; auto. omega. omega.
      * unfold update_maps in UPDATE. simpl in UPDATE.
        simpl. 
        inv NORPT. exploit update_gmap_not_in; eauto.
        intros GMAP'. rewrite GMAP in GMAP'.
        unfold update_gid_map in GMAP'. rewrite peq_true in GMAP'. inv GMAP'.
        unfold extfun_label. simpl. 
        exists (Ptrofs.repr efsize). split; auto.
        repeat rewrite Ptrofs.unsigned_repr.
        apply Zle_trans with (efsize1 + alignw). unfold alignw. omega.
        eapply efsize_mono; eauto. omega. omega.
      * unfold update_maps in UPDATE. simpl in UPDATE.
        simpl. 
        inv NORPT. exploit update_gmap_not_in; eauto.
        intros GMAP'. rewrite GMAP in GMAP'.
        unfold update_gid_map in GMAP'. rewrite peq_true in GMAP'. inv GMAP'.
        unfold data_label. simpl. 
        exists (Ptrofs.repr dsize). split; auto.
        repeat rewrite Ptrofs.unsigned_repr.
        apply Zle_trans with (dsize1 + align (init_data_list_size (gvar_init v)) alignw).
        generalize (alignw_le (init_data_list_size (gvar_init v))). omega. 
        eapply dsize_mono; eauto. omega. omega.
    + inv NORPT. unfold update_maps in UPDATE. simpl in UPDATE. 
      destruct a. 
      destruct (update_maps_def gmap1 lmap1 dsize1 csize1 efsize1 i o) eqn:UPDDEF.
      destruct p. destruct p. destruct p. 
      eapply (IHdefs _ _ _ _ _ id def slbl g l z1 z0 z); eauto.
      assert (dsize1 <= z1). eapply update_dsize_mono; eauto. omega.
      eapply update_csize_div; eauto.
      assert (csize1 <= z0). eapply update_csize_mono; eauto. omega.
      assert (efsize1 <= z). eapply update_efsize_mono; eauto. omega.
Qed.

Lemma transl_prog_segs : forall gmap lmap prog dsize csize efsize tprog,
    transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog ->
    list_of_segments tprog = gen_segs dsize csize efsize.
Proof.
  intros. monadInv H. unfold list_of_segments.
  simpl. unfold gen_segs. auto.
Qed.
 
Lemma make_maps_gmap_ofs_le_segsize :
  forall (gmap : GID_MAP_TYPE) (lmap : LABEL_MAP_TYPE) (dsize csize efsize : Z) (id : ident)
    def slbl
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize, efsize))
    (IN: In (id, Some def) (AST.prog_defs prog))
    (GMAP: gmap id = Some slbl),
    exists sz, find_segsize (list_of_segments tprog) (fst slbl) = Some sz /\
          (Ptrofs.unsigned (snd slbl)) + (def_size def) <= Ptrofs.unsigned sz.
Proof.
  intros.
  generalize TRANSF. intros TRANSF'.
  unfold match_prog, transf_program in TRANSF'.
  repeat destr_in TRANSF'.
  inv UPDATE.
  unfold make_maps in Heqp.
  assert (0 <= dsize). eapply dsize_mono; eauto.
  assert (0 <= csize). eapply csize_mono; eauto. apply Z.divide_0_r.
  assert (0 <= efsize). eapply efsize_mono; eauto.
  erewrite transl_prog_segs; eauto.
  eapply update_maps_gmap_ofs_le_segsize; eauto; try omega.
  apply Z.divide_0_r.
  destruct w. auto.
Qed.

Lemma alloc_segments_perm: forall segs m b m' ofs k p
  (ALLOCSEGS: m' = alloc_segments m segs)
  (PERM: Mem.perm m b ofs k p),
  Mem.perm m' b ofs k p.
Proof.
  induction segs; intros.
  - inv ALLOCSEGS. simpl. auto.
  - inv ALLOCSEGS. simpl.
    destruct (Mem.alloc m 0 (Ptrofs.unsigned (segsize a))) eqn:ALLOC.
    eapply IHsegs; eauto.
    eapply Mem.perm_alloc_1; eauto.
Qed.    
      

Lemma alloc_segments_acc_segblocks_perm : forall segs m m' sid sz k p ofs smap
    (ALLOCSEGS: m' = alloc_segments m segs)
    (FINDSZ: find_segsize segs sid = Some sz)
    (SMAP: smap = acc_segblocks (Mem.nextblock m) (map segid segs) (fun id => undef_seg_block))
    (OFSBND: 0 <= ofs < Ptrofs.unsigned sz),
    Mem.perm m' (smap sid) ofs k p.
Proof.
  induction segs; intros.
  - inv FINDSZ.
  - simpl in ALLOCSEGS.
    destruct (Mem.alloc m 0 (Ptrofs.unsigned (segsize a))) eqn:ALLOC.
    rewrite map_cons in SMAP. simpl in SMAP. subst.
    destruct ident_eq.
    + unfold find_segsize in FINDSZ.
      simpl in FINDSZ.  subst. setoid_rewrite peq_true in FINDSZ.
      inv FINDSZ. exploit Mem.nextblock_alloc; eauto. intros NB.
      exploit Mem.alloc_result; eauto. intros. subst.
      eapply alloc_segments_perm; eauto.
      apply Mem.perm_implies with (p1:=Freeable); auto.
      eapply Mem.perm_alloc_2; eauto.
      constructor.
    + unfold find_segsize in FINDSZ.
      simpl in FINDSZ.  setoid_rewrite peq_false in FINDSZ; auto.
      eapply IHsegs; eauto.
      erewrite <- Mem.nextblock_alloc; eauto.
Qed.      

Lemma init_mem_pres_inject : forall m gmap lmap dsize csize efsize
    (UPDATE: make_maps prog = (gmap, lmap, dsize, csize, efsize))
    (TRANSPROG: transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog)
    (INITMEM: Genv.init_mem prog = Some m),
    exists m', init_mem tprog = Some m' /\ Mem.inject (globs_meminj gmap) (def_frame_inj m) m m'. 
Proof. 
  unfold Genv.init_mem, init_mem. intros.
  destruct (Mem.alloc Mem.empty 0 0) eqn:IALLOC. 
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK. 
  rewrite Mem.nextblock_empty in NEXTBLOCK. simpl in NEXTBLOCK.
  exploit alloc_segments_weak_inject; eauto.
  erewrite Mem.alloc_stack_blocks; eauto. 
  erewrite Mem.empty_stack; eauto.
  intros SINJ.
  set (m1 := alloc_segments m0 (list_of_segments tprog)) in *.
  generalize (alloc_all_globals_inject). intro AAGI.
  generalize TRANSF. intros TRANSF'. unfold match_prog in TRANSF'.
  unfold transf_program in TRANSF'.
  destruct (check_wellformedness prog) eqn:WF; try congruence. repeat destr_in TRANSF'.
  unfold transl_prog_with_map in H0. monadInv H0. 
  rename EQ into TRANSGLOBS.
  rewrite H0 in *. inversion UPDATE. subst g l z1 z0 z.
  exploit AAGI; eauto using INITMEM, SINJ, Mem.inject_ext.
  - clear H0. inv w. auto.
  - exploit alloc_segments_nextblock; eauto. intros.
    unfold m1. rewrite H. simpl. rewrite NEXTBLOCK. auto.
  - unfold m1. erewrite alloc_segments_stack; eauto.
    erewrite Mem.alloc_stack_blocks; eauto.
    erewrite Mem.empty_stack; eauto.
  - eapply alloc_segments_perm_ofs; eauto. unfold m1; auto.
    intros b0 ofs k p PERM. erewrite alloc_perm in PERM; eauto.
    destruct peq. omega. apply Mem.perm_empty in PERM. contradiction.
  - intros id odef slbl b' delta IN GMAP SYMOFS ofs k p OFS.
    destruct odef as [def|].
    + exploit make_maps_gmap_ofs_le_segsize; eauto.
      intros (sz & FINDSEGSZ & BND). simpl in OFS.
      unfold Genv.symbol_block_offset in SYMOFS.
      unfold Genv.label_to_block_offset in SYMOFS. inversion SYMOFS.
      subst delta b'. unfold tge. rewrite H0.
      rewrite genv_gen_segblocks.
      unfold m1. rewrite H0.      
      eapply alloc_segments_acc_segblocks_perm; eauto.
      unfold gen_segblocks. rewrite NEXTBLOCK. reflexivity.
      generalize (Ptrofs.unsigned_range_2 (snd slbl)); eauto. intros.
      omega.
    + simpl in OFS. omega.
  - intros (m1' & ALLOC' & MINJ).
    exists m1'. split. subst. simpl.
    erewrite (alloc_globals_ext _ _ (Genv.genv_segblocks tge)); eauto. 
    intros x1. subst tge. rewrite genv_gen_segblocks. rewrite H0. auto.
    auto.
Qed.

Lemma find_funct_ptr_next :
  Genv.find_funct_ptr ge (Globalenvs.Genv.genv_next ge) = None.
Proof.
  unfold Globalenvs.Genv.find_funct_ptr. 
  destruct (Genv.find_def ge (Globalenvs.Genv.genv_next ge)) eqn:EQ; auto.
  destruct g; auto.
  unfold Genv.find_def in EQ.
  apply Globalenvs.Genv.genv_defs_range in EQ.
  exploit Plt_strict; eauto. contradiction.
Qed.

Lemma match_sminj_incr : forall gmap lmap j j',
    (forall b, b <> Globalenvs.Genv.genv_next ge -> j' b = j b) ->
    inject_incr j j' ->
    match_sminj gmap lmap j -> match_sminj gmap lmap j'.
Proof.
  intros gmap lmap j j' INJINV INJINCR MSMINJ. constructor.
  - intros b b' f ofs ofs' i FINDPTR FINDINSTR J.
    eapply (agree_sminj_instr gmap lmap j MSMINJ); eauto. 
    exploit (INJINV b).
    unfold not. intros. 
    subst b. rewrite find_funct_ptr_next in FINDPTR. congruence.
    intros. congruence.

  - intros id gloc H. 
    exploit (agree_sminj_glob gmap lmap j MSMINJ); eauto. 
    intros (ofs' & b & b' & FSYM & SYMADDR & MAP).
    exists ofs', b, b'. split; auto. 

  - intros id b f l z l' FSYM FPTR LPOS LMAP.
    exploit (agree_sminj_lbl gmap lmap j MSMINJ); eauto.
Qed.

Lemma push_new_stage_def_frame_inj : forall m,
    def_frame_inj (Mem.push_new_stage m) = (1%nat :: def_frame_inj m).
Proof.
  unfold def_frame_inj. intros.
  erewrite Mem.push_new_stage_stack. simpl. auto.
Qed.



(* Definition advance_next {A:Type} (gl: list A) (x: positive) := *)
(*   List.fold_left (fun n g => Psucc n) gl x. *)

(* Lemma advance_next_lt_succ : forall (A:Type) (l:list A) i, *)
(*     Plt i  (advance_next l (Pos.succ i)). *)
(* Proof. *)
(*   induction l; intros. *)
(*   -  simpl. apply Plt_succ. *)
(*   - simpl. apply Plt_trans with (Pos.succ i). *)
(*     apply Plt_succ. apply IHl. *)
(* Qed. *)

(* Lemma acc_segblocks_upper_bound : forall l i f, *)
(*   (forall id, Plt (f id) i) -> *)
(*   (forall id, Plt (acc_segblocks i l f id) (advance_next l i)). *)
(* Proof. *)
(*   induction l; intros. *)
(*   - simpl in *. auto. *)
(*   - simpl in *. destruct ident_eq.  *)
(*     + subst. apply advance_next_lt_succ. *)
(*     + apply IHl. intros. apply Plt_trans with i. apply H. *)
(*       apply Plt_succ. *)
(* Qed. *)

(* Lemma gen_segblocks_upper_bound : forall p id, *)
(*   Plt (gen_segblocks p id) (advance_next (list_of_segments p) init_block). *)
(* Proof. *)
(*   intros. unfold gen_segblocks. *)
(*   eapply acc_segblocks_upper_bound; eauto.  *)
(*   intros. unfold undef_seg_block, init_block. apply Plt_succ. *)
(* Qed. *)

Lemma init_meminj_genv_next_inv : forall gmap b delta
    (MINJ: init_meminj gmap b = Some (Genv.genv_next tge, delta)),
    b = Globalenvs.Genv.genv_next ge.
Proof.
  intros.
  unfold init_meminj in MINJ. destruct eq_block; inv MINJ.
  - unfold ge. auto.
  - destr_match_in H0; inv H0.
    destr_match_in H1; inv H1.
    rewrite genv_gen_segblocks in H0. unfold tge in H0.
    unfold globalenv in H0.
    erewrite <- add_globals_pres_genv_next in H0; eauto. simpl in H0.
    generalize (gen_segblocks_upper_bound tprog (fst s)). simpl.
    rewrite H0. intros. apply Plt_strict in H. contradiction.
Qed.


Lemma genv_internal_codeblock_add_globals:
  forall l g,
    Genv.genv_internal_codeblock (add_globals g l) = Genv.genv_internal_codeblock g.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl. unfold add_global. 
  destruct a, p, o; auto.
  destruct g0; auto.
Qed.


Lemma genv_segblocks_add_globals:
  forall l g,
    Genv.genv_segblocks (add_globals g l) = Genv.genv_segblocks g.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl. unfold add_global. 
  destruct a, p, o; auto.
  destruct g0; auto.
Qed.


Lemma update_map_funct:
  forall gmap lmap dsize csize efsize b f i s,
    make_maps prog = (gmap, lmap, dsize, csize, efsize) ->
    list_norepet (map fst (AST.prog_defs prog)) ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    Genv.invert_symbol ge b = Some i ->
    gmap i = Some s ->
    fst s = code_segid.
Proof.
  unfold make_maps. intros gmap lmap dsize csize efsize b f i s UM LNR FFP IVS GM.
  exploit @Genv.find_symbol_funct_ptr_inversion. reflexivity.
  apply Genv.invert_find_symbol. unfold ge in IVS. apply IVS.
  eauto.
  intros.
  eapply (umind _ _ _ _ _ _ _ _ _ _ _ UM (fun g l d c e => forall s, g i = Some s -> In (i, Some (Gfun (Internal f))) (AST.prog_defs prog) -> fst s = code_segid)).
  inversion 1.
  - intros.
    erewrite update_gmap in H3. 2: eauto.
    destr_in H3; eauto.
    subst.
    exploit @norepet_unique. apply LNR. apply H4. apply H2. reflexivity. intro A; inv A. inv H3.
    reflexivity.
  - auto.
  - auto.
Qed.

Lemma update_map_ext_funct:
  forall gmap lmap dsize csize efsize b f i s,
    make_maps prog = (gmap, lmap, dsize, csize, efsize) ->
    list_norepet (map fst (AST.prog_defs prog)) ->
    Genv.find_funct_ptr ge b = Some (External f) ->
    Genv.invert_symbol ge b = Some i ->
    gmap i = Some s ->
    fst s = extfuns_segid.
Proof.
  unfold make_maps. intros gmap lmap dsize csize efsize b f i s UM LNR FFP IVS GM.
  exploit @Genv.find_symbol_funct_ptr_inversion. reflexivity.
  apply Genv.invert_find_symbol. unfold ge in IVS. apply IVS.
  eauto.
  intros.
  eapply (umind _ _ _ _ _ _ _ _ _ _ _ UM (fun g l d c e => forall s, g i = Some s -> In (i, Some (Gfun (External f))) (AST.prog_defs prog) -> fst s = extfuns_segid)).
  inversion 1.
  - intros.
    erewrite update_gmap in H3. 2: eauto.
    destr_in H3; eauto.
    subst.
    exploit @norepet_unique. apply LNR. apply H4. apply H2. reflexivity. intro A; inv A. inv H3.
    reflexivity.
  - auto.
  - auto.
Qed.

Lemma transl_prog_seg_code:
  forall gmap lmap dsize csize efsize,
    transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog ->
    segid (fst (code_seg tprog)) = code_segid.
Proof.
  unfold transl_prog_with_map.
  intros. monadInvX H. simpl. auto.
Qed.

Lemma transl_prog_seg_data:
  forall gmap lmap dsize csize efsize,
    transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog ->
    segid (data_seg tprog) = data_segid.
Proof.
  unfold transl_prog_with_map.
  intros. monadInvX H. simpl. auto.
Qed.

Lemma transl_prog_seg_ext:
  forall gmap lmap dsize csize efsize,
    transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog ->
    segid (extfuns_seg tprog) = extfuns_segid.
Proof.
  unfold transl_prog_with_map.
  intros. monadInvX H. simpl. auto.
Qed.

Lemma valid_instr_offset_is_internal_init:
  forall gmap lmap dsize csize efsize j,
    transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog ->
    make_maps prog = (gmap, lmap, dsize, csize, efsize) ->
    list_norepet (map fst (AST.prog_defs prog)) ->                   
    (forall b, b <> Globalenvs.Genv.genv_next ge -> j b = init_meminj gmap b) ->
    valid_instr_offset_is_internal j.
Proof.
  intros gmap lmap dsize csize efsize j TP UM LNR INJ b b' f ofs i ofs' FFP FI JB.
  assert (b <> Globalenvs.Genv.genv_next ge).
  {
    unfold Genv.find_funct_ptr in FFP. destr_in FFP.
    unfold Genv.find_def in Heqo. eapply Globalenvs.Genv.genv_defs_range in Heqo.
    apply Plt_ne. auto.
  }
  rewrite INJ in JB; auto.
  unfold init_meminj in JB.
  rewrite pred_dec_false in JB by auto.
  destr_in JB. repeat destr_in JB.
  unfold tge.
  unfold globalenv. simpl.
  rewrite genv_internal_codeblock_add_globals. simpl.
  rewrite genv_segblocks_add_globals. simpl.
  unfold gen_segblocks. simpl.
  unfold gen_internal_codeblock.
  unfold proj_sumbool. destr. exfalso; apply n; clear n.
  exploit update_map_funct; eauto. intro EQ. rewrite EQ.
  rewrite pred_dec_false. rewrite pred_dec_true.
  rewrite pred_dec_false. rewrite pred_dec_true; auto.
  erewrite transl_prog_seg_code; eauto. erewrite transl_prog_seg_data; eauto. unfold code_segid, data_segid. congruence.
  erewrite transl_prog_seg_code; eauto.
  erewrite transl_prog_seg_data; eauto. unfold code_segid, data_segid. congruence.
Qed.

Lemma extfun_target_block:
    forall gmap lmap dsize csize efsize j,
    transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog ->
    make_maps prog = (gmap, lmap, dsize, csize, efsize) ->
    list_norepet (map fst (AST.prog_defs prog)) ->                   
    (forall b, b <> Globalenvs.Genv.genv_next ge -> j b = init_meminj gmap b) ->
    forall b b' f ofs 
      (FFP : Genv.find_funct_ptr ge b = Some (External f))
      (JB: j b = Some (b', ofs)),
      b' = extfuns_segid.
Proof.
  intros gmap lmap dsize csize efsize j TP UM LNR INJ b b' f ofs FFP JB.
  assert (b <> Globalenvs.Genv.genv_next ge).
  {
    unfold Genv.find_funct_ptr in FFP. destr_in FFP.
    unfold Genv.find_def in Heqo. eapply Globalenvs.Genv.genv_defs_range in Heqo.
    apply Plt_ne. auto.
  }
  rewrite INJ in JB; auto.
  unfold init_meminj in JB.
  rewrite pred_dec_false in JB by auto.
  repeat destr_in JB.
  unfold tge.
  unfold globalenv. simpl.
  rewrite genv_segblocks_add_globals. simpl.
  unfold gen_segblocks. simpl.
  exploit update_map_ext_funct; eauto. intro EQ. rewrite EQ.
  rewrite pred_dec_false. rewrite pred_dec_false. rewrite pred_dec_true.
  unfold extfuns_segid. auto.
  erewrite transl_prog_seg_ext; eauto.
  erewrite transl_prog_seg_code; eauto; unfold code_segid, extfuns_segid; congruence.
  erewrite transl_prog_seg_data; eauto; unfold extfuns_segid, data_segid; congruence.
Qed.

Lemma genv_defs_add_globals_notin:
  forall defs g b o s
    (NIN: forall i d sb, In (i, Some d, sb) defs -> Genv.symbol_address g (segblock_to_label sb) Ptrofs.zero <> Vptr b o)
    (SA: Genv.symbol_address g (segblock_to_label s) Ptrofs.zero = Vptr b o),
    Genv.genv_defs (add_globals g defs) b o = Genv.genv_defs g b o.
Proof.
  induction defs; simpl; intros; eauto.
  erewrite IHdefs; eauto.
  - unfold add_global.
    repeat destr. simpl. apply pred_dec_false.
    apply not_eq_sym.
    eapply NIN. eauto.
  - intros.
    revert NIN.
    unfold Genv.symbol_address.
    unfold Genv.label_to_ptr.
    erewrite <- add_global_pres_genv_segblocks. 2: eauto.
    intro NIN; eapply NIN. eauto.
  - rewrite <- SA.
    unfold Genv.symbol_address.
    unfold Genv.label_to_ptr. f_equal.
    symmetry; eapply add_global_pres_genv_segblocks. eauto.
Qed.

Lemma symbol_address_add_global:
  forall g d s o,
    Genv.symbol_address (add_global g d) s o = Genv.symbol_address g s o.
Proof.
  unfold Genv.symbol_address, Genv.label_to_ptr.
  intros.
  f_equal. symmetry. eapply add_global_pres_genv_segblocks. eauto.
Qed.

Fixpoint filter_map {A B: Type} (f: A -> option B) (l: list A): list B :=
  match l with
    nil => nil
  | a::r => match f a with
             Some b => b :: filter_map f r
           | None => filter_map f r
           end
  end.

Lemma in_filter_map_iff {A B} (f: A -> option B) : forall l x,
    In x (filter_map f l) <-> (exists y, f y = Some x /\ In y l).
Proof.
  induction l; simpl; intros.
  split. easy. intros (y & EQ & F); auto.
  destr. simpl. rewrite IHl.
  split.
  intros [EQ | (y & EQ & INy)]; subst; eauto.
  intros (y & EQ & [EQ1 | IN]); subst; eauto. left; congruence.
  rewrite IHl.
  split.
  intros (y & EQ & INy); subst; eauto.
  intros (y & EQ & [EQ1 | IN]); subst; eauto. congruence.
Qed.

Lemma filter_map_ext:
  forall {A B} (f g: A -> option B) (EXT: forall x, f x = g x) l,
    filter_map f l = filter_map g l.
Proof.
  induction l; simpl; intros; eauto.
  rewrite EXT. destr.
Qed.

Lemma list_norepet_filter_map:
  forall {A B} (f: A -> option B) a l,
    list_norepet (filter_map f (a::l)) ->
    list_norepet (filter_map f l).
Proof.
  simpl; intros.
  destr_in H; inv H; auto.
Qed.
      
Lemma genv_defs_add_globals:
  forall
    (* defs gmap lmap dsize csize efsize gmap' lmap' dsize' csize' efsize' *)
    (* (UM : update_maps gmap lmap dsize csize efsize defs = (gmap', lmap', dsize', csize', efsize')) *)
    (* gmap *)
    tdefs
    g
    (* s i *)
    (* (GM: gmap i = Some s) *)
    i f s
    (DEFS: In (i, Some (FlatAsmGlobdef.Gfun (V:=unit) f), s) tdefs)
    b o
    (LNR: list_norepet (filter_map (fun '(i,d,s) => match d with
                                                   None => None
                                                 | Some _ => Some (Genv.symbol_address g (segblock_to_label s) Ptrofs.zero)
                                                 end) tdefs))
    (SA: Genv.symbol_address g (segblock_to_label s) Ptrofs.zero = Vptr b o),
    Genv.genv_defs (add_globals g tdefs) b o = Some f.
Proof.
  intros.
  unfold Genv.symbol_address in SA.
  unfold Genv.label_to_ptr in SA.
  unfold offset_seglabel in SA. destr_in SA. simpl in SA. inv SA.
  rewrite Ptrofs.add_zero in *.
  revert g i s0 i0 s f LNR Heqs0 DEFS.
  induction tdefs; intros. easy.
  destruct DEFS.
  - subst. simpl.
    erewrite genv_defs_add_globals_notin.
    + unfold add_global. simpl. rewrite Heqs0.
      unfold Genv.symbol_address, Genv.label_to_ptr. simpl. rewrite Ptrofs.add_zero. rewrite pred_dec_true; auto.
    + intros.
      intro EQ.
      inv LNR. apply H2. apply in_filter_map_iff. eexists; split. 2: apply H. simpl. auto.
      rewrite Heqs0. revert EQ. unfold Genv.symbol_address, Genv.label_to_ptr. simpl. rewrite Ptrofs.add_zero.
      intro A; inv A; auto. rewrite Ptrofs.add_zero. auto.
    + rewrite ! Heqs0. unfold Genv.symbol_address, Genv.label_to_ptr. simpl. rewrite Ptrofs.add_zero. auto.
  - erewrite <- IHtdefs.
    rewrite <- (add_global_pres_genv_segblocks a g _ eq_refl). eauto. 2: eauto. 2: eauto.
    erewrite filter_map_ext in LNR.
    eapply list_norepet_filter_map. apply LNR. simpl. intros.
    repeat destr. subst.
    rewrite symbol_address_add_global. auto.
Qed.

Lemma transl_extfun_exists : forall gmap lmap defs gdefs code f id o,
    transl_globdefs gmap lmap defs = OK (gdefs, code) ->
    In (id, Some (Gfun (External f))) defs ->
    gmap id = Some (extfuns_segid, o) ->
    exists s,
      In (id, Some (FlatAsmGlobdef.Gfun (External f)), s) gdefs /\
      segblock_id s = extfuns_segid /\ segblock_start s = o.
Proof.
  induction defs; simpl; intros.
  - contradiction.
  - destruct a. monadInv H.
    destruct H0.
    + inv H. simpl in EQ. repeat destr_in EQ. inv EQ2. inv H1.  eexists; split. left; eauto.
      split. reflexivity. simpl. auto.
    + repeat destr_in EQ2; eauto.
      edestruct IHdefs as (s & IN & EQs); eauto.
      eexists; split. right; eauto. auto.
Qed.


Lemma transl_globdef_ident:
  forall gmap lmap i def p0 c,
    transl_globdef gmap lmap i def = OK (Some (p0,c)) ->
    fst (fst p0) = i.
Proof.
  intros.
  unfold transl_globdef in H. repeat destr_in H.
  monadInv H1. simpl. auto. simpl; auto. 
  monadInv H1. simpl. auto.
Qed.


Lemma transl_globdefs_in_defs:
  forall gmap lmap defs gdefs c,
    transl_globdefs gmap lmap defs = OK (gdefs, c) ->
    forall i,
      In i (map fst (map fst gdefs)) ->
      In i (map fst defs).
Proof.
  induction defs; simpl; intros; eauto. inv H. easy.
  repeat destr_in H.
  monadInv H2.
  repeat destr_in EQ2; eauto.
  simpl in H0. destruct H0.
  - subst.
    left; simpl. symmetry. eapply transl_globdef_ident; eauto.
  - eauto.
Qed.

Lemma transl_globdefs_norepet:
  forall gmap lmap defs gdefs c,
    transl_globdefs gmap lmap defs = OK (gdefs, c) ->
    list_norepet (map fst defs) ->
    list_norepet (map fst (map fst gdefs)).
Proof.
  induction defs; simpl; intros; eauto. inv H. constructor.
  repeat destr_in H.
  monadInv H2.
  inv H0.
  repeat destr_in EQ2; eauto.
  simpl. constructor; eauto.
  intro IN.
  eapply transl_globdefs_in_defs in IN; eauto.
  erewrite transl_globdef_ident in IN; eauto.
Qed.

Lemma in_transl_globdefs'':
  forall gmap lmap l gdefs code,
    transl_globdefs gmap lmap l = OK (gdefs, code) ->
    forall i o s,
      In (i, o, s) gdefs ->
      exists d sb c,
        In (i,d) l /\
        transl_globdef gmap lmap i d = OK (Some (i, o, sb, c)).
Proof.
  induction l; simpl; intros; eauto. inv H; easy.
  repeat destr_in H. monadInv H2.
  destruct o0.
  - simpl in *. repeat destr_in EQ. monadInv H1. inv EQ2. simpl in *.
    unfold transl_fun in EQ. repeat destr_in EQ. monadInv H1. repeat destr_in EQ0. simpl in *.
    destruct H0 as [H0|H0]. inv H0.
    do 3 eexists; split; simpl; eauto. simpl. unfold transl_fun. rewrite Heqo0. rewrite EQ. simpl. destr.
    edestruct IHl as (d & sb & c & IN & TG); eauto.
    exists d, sb, c; repeat apply conj; eauto.
    inv EQ2. simpl in *.
    destruct H0 as [H0|H0]. inv H0.
    do 3 eexists; split; simpl; eauto. simpl. rewrite Heqo0. eauto.
    edestruct IHl as (d & sb & c & IN & TG); eauto.
    exists d, sb, c; repeat apply conj; eauto.
    monadInv H1. inv EQ2. simpl in *.
    unfold transl_gvar in EQ. monadInv EQ.
    destruct H0 as [H0|H0]. inv H0.
    do 3 eexists; split; simpl; eauto. simpl. rewrite Heqo0. unfold transl_gvar. rewrite EQ0. simpl. eauto.
    edestruct IHl as (d & sb & c & IN & TG); eauto.
    exists d, sb, c; repeat apply conj; eauto.
  - simpl in *. inv EQ. inv EQ2.
    edestruct IHl as (d & sb & c & IN & TG); eauto.
    exists d, sb, c; repeat apply conj; eauto.
Qed.

Lemma in_transl_globdefs':
  forall gmap lmap l gdefs code,
    transl_globdefs gmap lmap l = OK (gdefs, code) ->
    forall i o s,
      In (i, o, s) gdefs ->
      exists sb,
        gmap i = Some sb /\
        segblock_id s = fst sb /\
        segblock_start s = snd sb.
Proof.
  induction l; simpl; intros; eauto. inv H; easy.
  repeat destr_in H. monadInv H2.
  destruct o0.
  - simpl in *. repeat destr_in EQ. monadInv H1. inv EQ2. simpl in *.
    unfold transl_fun in EQ. repeat destr_in EQ. monadInv H1. repeat destr_in EQ0. simpl in *.
    destruct H0 as [H0|H0]. inv H0. rewrite Heqo0.
    eexists; repeat apply conj; simpl; eauto.
    eapply IHl; eauto.
    inv EQ2. simpl in *.
    destruct H0 as [H0|H0]. inv H0. rewrite Heqo0.
    eexists; split; simpl; eauto.
    eapply IHl; eauto.
    monadInv H1. inv EQ2. simpl in *.
    unfold transl_gvar in EQ. monadInv EQ. simpl in *.
    destruct H0 as [H0|H0]. inv H0. rewrite Heqo0.
    eexists; split; simpl; eauto.
    eapply IHl; eauto.
  - simpl in *. inv EQ. inv EQ2.
    eapply IHl; eauto.
Qed.

Lemma list_map_norepet_kv:
  forall {A B C}  (key: A -> B) (val: A -> option C)
    (l: list A)
    (lnr: list_norepet (map key l))
    (inj: forall a1 a2 v1 v2, In a1 l -> In a2 l -> key a1 <> key a2 -> val a1 = Some v1 -> val a2 = Some v2 -> v1 <> v2),
    list_norepet (filter_map val l).
Proof.
  induction l; simpl; intros. constructor.
  inv lnr.
  trim IHl. auto.
  trim IHl. eauto.
  destr.
  constructor; eauto.
  intro IN. rewrite in_filter_map_iff in IN.
  rewrite in_map_iff in H1.
  destruct IN as (x & EQ & IN).
  eapply inj. 4: apply EQ. auto. auto. intro KEY.
  apply H1. exists x; split; auto. eauto. auto.
Qed.

Lemma extfun_transf:
  forall gmap lmap dsize csize efsize j,
    wf_prog prog ->
    transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog ->
    make_maps prog = (gmap, lmap, dsize, csize, efsize) ->
    dsize + csize + efsize <= Ptrofs.max_unsigned ->
    list_norepet (map fst (AST.prog_defs prog)) ->                   
    (forall b, b <> Globalenvs.Genv.genv_next ge -> j b = init_meminj gmap b) ->
    forall b b' f ofs 
      (FFP : Genv.find_funct_ptr ge b = Some (External f))
      (JB: j b = Some (b', ofs)),
      Genv.find_funct tge (Vptr b' (Ptrofs.repr ofs)) = Some (External f).
Proof.
  intros gmap lmap dsize csize efsize j WF TP UM SZ LNR INJ b b' f ofs FFP JB.
  assert (b <> Globalenvs.Genv.genv_next ge).
  {
    unfold Genv.find_funct_ptr in FFP. destr_in FFP.
    unfold Genv.find_def in Heqo. eapply Globalenvs.Genv.genv_defs_range in Heqo.
    apply Plt_ne. auto.
  }
  rewrite INJ in JB; auto.
  unfold init_meminj in JB.
  rewrite pred_dec_false in JB by auto.
  repeat destr_in JB.
  unfold tge, Genv.find_funct.
  unfold globalenv. simpl.
  rewrite genv_segblocks_add_globals. simpl.
  unfold gen_segblocks. simpl.
  exploit update_map_ext_funct; eauto. intro EQ. rewrite EQ.
  rewrite pred_dec_false. rewrite pred_dec_false. rewrite pred_dec_true.
  2: erewrite transl_prog_seg_ext; eauto.
  2: erewrite transl_prog_seg_code; eauto; unfold code_segid, extfuns_segid; congruence.
  2: erewrite transl_prog_seg_data; eauto; unfold extfuns_segid, data_segid; congruence.
  exploit @Genv.find_symbol_funct_ptr_inversion. reflexivity.
  apply Genv.invert_find_symbol. eauto. eauto. intro IN.
  unfold transl_prog_with_map in TP. monadInv TP. simpl in *.
  destruct s. simpl in *. subst s.
  edestruct transl_extfun_exists as (ss & INs & EQs & EQo); eauto.
  destruct ss; simpl in *. subst segblock_id segblock_start.
  erewrite genv_defs_add_globals. eauto.
  eauto.
  unfold Genv.symbol_address. simpl. unfold Genv.label_to_ptr. simpl.
  {
    eapply list_map_norepet_kv. rewrite <- map_map. eapply transl_globdefs_norepet; eauto.
    simpl.
    intros ((i1 & o1) & s1) ((i2 & o2) & s2) v1 v2 IN1 IN2 DIFF. simpl in DIFF.
    destruct o1, o2; try congruence.
    destruct (in_transl_globdefs' _ _ _ _ _ EQ0 _ _ _ IN1) as (sb1 & G1 & SI1 & SS1).
    destruct (in_transl_globdefs' _ _ _ _ _ EQ0 _ _ _ IN2) as (sb2 & G2 & SI2 & SS2).
    destruct (in_transl_globdefs'' _ _ _ _ _ EQ0 _ _ _ IN1) as (d1 & ? & ? & INl1 & TG1).
    destruct (in_transl_globdefs'' _ _ _ _ _ EQ0 _ _ _ IN2) as (d2 & ? & ? & INl2 & TG2).
    rewrite ! Ptrofs.add_zero. intros A B VEQ. subst v2. rewrite <- B in A.
    clear B.
    inversion A. clear A.
    destruct s1, s2, sb1, sb2. simpl in *. subst s0 i4 s i3 segblock_start0.
    exploit update_maps_gmap_inj. eauto. eauto. auto. apply INl1. apply INl2. auto. eauto. eauto.
    destruct (peq segblock_id segblock_id0).
    - subst segblock_id0.
      intros [A | A]. congruence.
      assert (odef_size d1 <= 0 \/ odef_size d2 <= 0). omega.
      clear A. clear H2.
      destruct d1; simpl in TG1; try congruence.
      destruct d2; simpl in TG2; try congruence. simpl in H0.
      clear - WF INl1 INl2 H0.
      inv WF. red in wf_prog_not_empty. rewrite Forall_forall in wf_prog_not_empty.
      exploit wf_prog_not_empty. apply in_map, INl1.
      exploit wf_prog_not_empty. apply in_map, INl2. simpl.
      unfold def_not_empty. simpl. omega.
    - intros _. apply n. clear n. repeat destr_in H2.
      exploit update_map_gmap_range. eauto. apply G1.
      exploit update_map_gmap_range. eauto. apply G2. simpl. clear H1. intuition subst; congruence.
  }
  unfold Genv.symbol_address. simpl. unfold Genv.label_to_ptr.
  simpl. f_equal. rewrite Ptrofs.add_zero. rewrite Ptrofs.repr_unsigned. auto.   
Qed.

Lemma extfun_entry_is_external_init:
  forall gmap lmap dsize csize efsize j,
    transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog ->
    make_maps prog = (gmap, lmap, dsize, csize, efsize) ->
    list_norepet (map fst (AST.prog_defs prog)) ->                   
    (forall b, b <> Globalenvs.Genv.genv_next ge -> j b = init_meminj gmap b) ->
    extfun_entry_is_external j.
Proof.
  intros gmap lmap dsize csize efsize j TP UM LNR INJ b b' f ofs FFP JB.
  assert (b <> Globalenvs.Genv.genv_next ge).
  {
    unfold Genv.find_funct_ptr in FFP. destr_in FFP.
    unfold Genv.find_def in Heqo. eapply Globalenvs.Genv.genv_defs_range in Heqo.
    apply Plt_ne. auto.
  }
  rewrite INJ in JB; auto.
  unfold init_meminj in JB.
  rewrite pred_dec_false in JB by auto.
  destr_in JB. repeat destr_in JB.
  unfold tge.
  unfold globalenv. simpl.
  rewrite genv_internal_codeblock_add_globals. simpl.
  rewrite genv_segblocks_add_globals. simpl.
  unfold gen_segblocks. simpl.
  unfold gen_internal_codeblock.
  unfold proj_sumbool. destr. contradict e.
  exploit update_map_ext_funct; eauto. intro EQ. rewrite EQ.
  rewrite pred_dec_false. rewrite pred_dec_false. rewrite pred_dec_true.
  rewrite pred_dec_false. rewrite pred_dec_true; eauto. congruence.
  erewrite transl_prog_seg_code; eauto. erewrite transl_prog_seg_data; eauto. unfold code_segid, data_segid. congruence.
  erewrite transl_prog_seg_ext; eauto.
  erewrite transl_prog_seg_code; eauto. unfold code_segid, extfuns_segid. congruence.
  erewrite transl_prog_seg_data; eauto. unfold extfuns_segid, data_segid. congruence.
Qed.

Lemma transl_globdefs_get_seg_block : 
  forall defs id def gmap lmap tdefs code
    (NORPT: list_norepet (map fst defs))
    (IN: In (id, Some def) defs)
    (TRANSL: transl_globdefs gmap lmap defs = OK (tdefs, code)),
  exists sb, get_seg_block id tdefs = Some sb 
        /\ gmap id = Some (segblock_to_label sb).
Proof.
  induction defs. intros.
  - inv IN.
  - intros. inv IN.
    + monadInv TRANSL.
      destruct x. 
      * destruct p. inv EQ2. 
        destruct def. destruct f.
        (* Internal function *)
        monadInv EQ. exists (fn_range x).
        split. unfold get_seg_block. simpl. 
        setoid_rewrite peq_true. auto.
        monadInvX EQ0. destruct zle; monadInv EQ4. simpl.
        unfold segblock_to_label. simpl. auto.
        (* External function *)
        destruct (gmap id) eqn:GMAP. destruct s.
        inv EQ. eexists. split.
        unfold get_seg_block. simpl. 
        setoid_rewrite peq_true. auto.
        unfold segblock_to_label. simpl. auto.
        inv EQ.
        (* Global variable *)
        destruct (gmap id) eqn:GMAP. destruct s.
        monadInv EQ. eexists. split.
        unfold get_seg_block. simpl. 
        setoid_rewrite peq_true. auto.
        unfold segblock_to_label. simpl. auto.
        inv EQ.
      * inv EQ2.
        destruct def. destruct f. monadInv EQ.
        destruct (gmap id) eqn:GMAP. destruct s. monadInv EQ.
        monadInv EQ.
        destruct (gmap id) eqn:GMAP. destruct s. monadInv EQ.
        monadInv EQ.
    + monadInvX TRANSL. 
      * inv NORPT.
        exploit IHdefs; eauto. 
        intros (sb & GSB & GMAP).
        exists sb. split; auto.
        destruct p0. destruct p. 
        assert (i0 = i).
        {
          destruct g. destruct f. monadInv EQ0; auto.
          destr_match_in EQ0. destruct s0; monadInv EQ0; auto.
          monadInv EQ0.
          destr_match_in EQ0. destruct s0; monadInv EQ0; auto.
          monadInv EQ0.
        }
        subst.
        unfold get_seg_block. simpl.
        destruct ident_eq. subst.
        assert (In (fst (i, Some def)) (map fst defs)).
        { eapply in_map with (f:=fst); eauto. }
        simpl in H0. congruence.
        simpl. auto.
      * destruct g. destruct f. monadInv EQ0.
        destr_match_in EQ0. destruct s. monadInv EQ0.
        monadInv EQ0.
        destr_match_in EQ0. destruct s. monadInv EQ0.
        monadInv EQ0.
      * inv NORPT.
        eapply IHdefs; eauto.
Qed.

Lemma transl_prog_get_seg_block : 
  forall id def prog gmap lmap dsize csize efsize tprog
    (NORPT: list_norepet (map fst (AST.prog_defs prog)))
    (IN: In (id, Some def) (AST.prog_defs prog))
    (TRANSL: transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog),
  exists sb, get_seg_block id (prog_defs tprog) = Some sb 
        /\ gmap id = Some (segblock_to_label sb).
Proof.
  intros. monadInv TRANSL. simpl.
  eapply transl_globdefs_get_seg_block; eauto.
Qed.
  

Lemma transl_prog_pres_main_id : forall gmap lmap prog dsize csize efsize tprog,
    transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog ->
    AST.prog_main prog = prog_main tprog.
Proof.
  intros. monadInv H. simpl. auto.
Qed.

Lemma main_ptr_inject:
  forall gmap lmap dsize csize efsize
    (MATCH_SMINJ: match_sminj gmap lmap (init_meminj gmap))
    (MAKEMAPS: make_maps prog = (gmap, lmap, dsize, csize, efsize))
    (TRANSL: transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog),
    Val.inject (init_meminj gmap)
               (Globalenvs.Genv.symbol_address
                  (Genv.globalenv prog)
                  (AST.prog_main prog) Ptrofs.zero)
               (get_main_fun_ptr (globalenv tprog) tprog).
Proof.
  intros.
  unfold match_prog in TRANSF. unfold transf_program in TRANSF.
  repeat destr_in TRANSF.  inv MAKEMAPS. inv w. auto.
  red in wf_prog_main_exists. rewrite Exists_exists in wf_prog_main_exists.
  destruct wf_prog_main_exists as (def & IN & P). 
  destruct def. destruct o; destruct P as [IDEQ P]; inv P.
  exploit transl_prog_get_seg_block; eauto.
  intros (sb & GETSEGB & GMAP).
  inv MATCH_SMINJ. exploit agree_sminj_glob0; eauto.
  intros (ofs' & b0 & b' & FINDSYM & SYMADDR & INJ).
  unfold Globalenvs.Genv.symbol_address. destr_match; auto.
  fold ge in EQ. rewrite EQ in FINDSYM. inv FINDSYM.
  unfold get_main_fun_ptr. 
  erewrite <- transl_prog_pres_main_id; eauto.
  rewrite GETSEGB. fold tge. rewrite SYMADDR. 
  eapply Val.inject_ptr; eauto.
  rewrite Ptrofs.add_zero_l. rewrite Ptrofs.repr_unsigned. auto.
Qed.


Lemma transf_initial_states : forall rs (SELF: forall j, forall r : PregEq.t, Val.inject j (rs r) (rs r)) st1,
    RawAsm.initial_state prog rs st1  ->
    exists st2, FlatAsm.initial_state tprog rs st2 /\ match_states st1 st2.
Proof.
  intros rs SELFINJECT st1 INIT.
  generalize TRANSF. intros TRANSF'.
  unfold match_prog in TRANSF'. unfold transf_program in TRANSF'.
  destruct (check_wellformedness prog) eqn:WF. 2: congruence. repeat destr_in TRANSF'.
  rename g into gmap.
  rename l into lmap.
  rename z1 into dsize. rename z0 into csize. rename z into efsize.
  inv INIT.
  exploit init_meminj_match_sminj; eauto.
  intros MATCH_SMINJ.
  exploit (init_mem_pres_inject m gmap); eauto.
  intros (m' & INITM' & MINJ).
  inversion H1.
  (* push_new stage *)
  exploit Mem.push_new_stage_inject; eauto. intros NSTGINJ.
  exploit (Mem.alloc_parallel_inject (globs_meminj gmap) (1%nat :: def_frame_inj m)
          (Mem.push_new_stage m) (Mem.push_new_stage m')
          0 (Mem.stack_limit + align (size_chunk Mptr) 8) m1 bstack
          0 (Mem.stack_limit + align (size_chunk Mptr) 8)); eauto. omega. omega.
  intros (j' & m1' & bstack' & MALLOC' & AINJ & INCR & FBSTACK & NOTBSTK).
  rewrite <- push_new_stage_def_frame_inj in AINJ.
  erewrite alloc_pres_def_frame_inj in AINJ; eauto.
  assert (bstack = Globalenvs.Genv.genv_next ge). 
  { 
    exploit (Genv.init_mem_genv_next prog m); eauto. intros BEQ. unfold ge. rewrite BEQ.
    apply Mem.alloc_result in MALLOC; eauto.
    subst bstack. apply Mem.push_new_stage_nextblock.
  }
  assert (bstack' = Genv.genv_next tge). 
  {
    exploit init_mem_genv_next; eauto. intros BEQ.
    unfold tge. rewrite BEQ.
    exploit Mem.alloc_result; eauto.
    intros. subst. apply Mem.push_new_stage_nextblock.
  }
  assert (forall x, j' x = init_meminj gmap x).
  {
    intros. destruct (eq_block x bstack).
    subst x. rewrite FBSTACK. unfold init_meminj. subst.
    rewrite dec_eq_true; auto.
    erewrite NOTBSTK; eauto.
    unfold init_meminj. subst. 
    rewrite dec_eq_false; auto.
  }
  exploit Mem.inject_ext; eauto. intros MINJ'.
  exploit Mem.drop_parallel_inject; eauto. red. simpl. auto.
  unfold init_meminj. fold ge. rewrite <- H4. rewrite pred_dec_true. eauto. auto.
  intros (m2' & MDROP' & DMINJ). simpl in MDROP'. rewrite Z.add_0_r in MDROP'.
  erewrite (drop_perm_pres_def_frame_inj m1) in DMINJ; eauto.
  
  assert (exists m3', Mem.record_stack_blocks m2' (make_singleton_frame_adt' bstack' frame_info_mono 0) = Some m3'
                 /\ Mem.inject (init_meminj gmap) (def_frame_inj m3) m3 m3') as RCD.
  {
    unfold def_frame_inj. unfold def_frame_inj in DMINJ.
    eapply (Mem.record_stack_block_inject_flat m2 m3 m2' (init_meminj gmap)
           (make_singleton_frame_adt' bstack frame_info_mono 0)); eauto.
    (* frame inject *)
    red. unfold make_singleton_frame_adt'. simpl. constructor. 
    simpl. intros b2 delta FINJ.
    unfold init_meminj in FINJ. fold ge in FINJ. rewrite <- H4 in FINJ. 
    rewrite pred_dec_true in FINJ; auto. inv FINJ.
    exists frame_info_mono. split. auto. apply inject_frame_info_id.
    constructor.
    (* in frame *)
    unfold make_singleton_frame_adt'. simpl. unfold in_frame. simpl.
    repeat rewrite_stack_blocks. 
    erewrite init_mem_stack; eauto.
    (* valid frame *)
    unfold make_singleton_frame_adt'. simpl. red. unfold in_frame.
    simpl. intuition. subst. 
    eapply Mem.drop_perm_valid_block_1; eauto.
    eapply Mem.valid_new_block; eauto.
    (* frame_agree_perms *)
    red. unfold make_singleton_frame_adt'. simpl. 
    intros b fi o k p BEQ PERM. inv BEQ; try contradiction.
    inv H7. unfold frame_info_mono. simpl.
    erewrite drop_perm_perm in PERM; eauto. destruct PERM.
    eapply Mem.perm_alloc_3; eauto.
    (* in frame iff *)
    unfold make_singleton_frame_adt'. unfold in_frame. simpl.
    intros b1 b2 delta INJB. split.
    intros BEQ. destruct BEQ; try contradiction. subst b1. 
    unfold init_meminj in INJB. fold ge in INJB. rewrite <- H4 in INJB.
    rewrite pred_dec_true in INJB; auto. inv INJB. left; auto.
    intros BEQ. destruct BEQ; try contradiction. subst b2. 
    assert (bstack' = Mem.nextblock (Mem.push_new_stage m')) as BEQ. 
    eapply Mem.alloc_result; eauto using MALLOC'.
    rewrite Mem.push_new_stage_nextblock in BEQ.
    erewrite <- init_mem_genv_next in BEQ; eauto using INITM'.
    subst bstack'.     
    destruct (eq_block bstack b1); auto.
    assert (b1 <> bstack) by congruence.
    apply NOTBSTK in H5. rewrite H6 in H5. rewrite INJB in H5.
    left. symmetry. subst bstack. eapply init_meminj_genv_next_inv; eauto.

    (* top frame *)
    red. repeat rewrite_stack_blocks. constructor. auto.
    (* size stack *)
    repeat rewrite_stack_blocks. 
    erewrite init_mem_stack; eauto. simpl. omega.
  }

  destruct RCD as (m3' & RCDSB & RMINJ).
  set (rs0' := rs # PC <- (get_main_fun_ptr tge tprog)
                  # RA <- Vnullptr
                  # RSP <- (Vptr bstack' (Ptrofs.repr (Mem.stack_limit + align (size_chunk Mptr) 8)))) in *.
  exists (State rs0' m3'). split.
  - eapply initial_state_intro; eauto.
    eapply initial_state_gen_intro; eauto. subst. fold tge in MDROP'. auto.
  - eapply match_states_intro; eauto.
    + eapply valid_instr_offset_is_internal_init; eauto. inv w; auto.
    + eapply extfun_entry_is_external_init; eauto. inv w; auto.
    + red.
      intros. eapply extfun_transf; eauto. inv w; auto.
      rewrite H6. eauto.
    + red. unfold rs0, rs0'.
      apply val_inject_set.
      apply val_inject_set.
      apply val_inject_set.
      auto.
      exploit (main_ptr_inject); eauto. unfold Globalenvs.Genv.symbol_address.
      unfold ge, ge0 in *. rewrite H2. fold tge. auto.
      unfold Vnullptr. destr; auto.
      econstructor. unfold init_meminj. subst bstack. fold ge. rewrite peq_true. subst bstack'.  fold tge. eauto.
      rewrite Ptrofs.add_zero. auto.
    + red. intros b g FD.
      unfold Genv.find_def in FD. eapply Genv.genv_defs_range in FD.
      revert FD. red. rewnb.
      fold ge. intros. xomega.
    + red.
      intros.
      erewrite update_gmap_not_in. 2: apply Heqp. reflexivity.
      intro IN. destruct (Genv.find_symbol_exists_1 prog id). apply IN. unfold ge, ge0 in *. congruence.  
Qed.

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

Axiom external_call_inject : forall ge j vargs1 vargs2 m1 m2 m1' vres1 t ef,
    Val.inject_list j vargs1 vargs2 ->
    Mem.inject j (def_frame_inj m1) m1 m2 ->
    external_call ef ge vargs1 m1 t vres1 m1' ->
    exists j' vres2 m2',
      external_call ef ge vargs2 m2 t vres2 m2' /\ 
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

Lemma goto_label_inject : forall rs1 rs2 gm lm id b f l l' j m1 m2 rs1' m1' ofs
                            (MATCHSMINJ: match_sminj gm lm j)
                            (RINJ: regset_inject j rs1 rs2)
                            (MINJ:Mem.inject j (def_frame_inj m1) m1 m2),
    rs1 PC = Vptr b ofs ->
    Genv.find_symbol ge id = Some b ->
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    Asm.goto_label ge f l rs1 m1 = Next rs1' m1' ->
    lm id l = Some l' ->
    exists rs2', goto_label tge l' rs2 m2 = Next rs2' m2 /\
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

Lemma add_globals_pres_senv : 
  forall (defs : list (ident * option gdef * segblock)) (ge : genv),
  Genv.genv_senv (add_globals ge defs) = Genv.genv_senv ge.
Proof.
  induction defs; intros.
  - simpl. auto.
  - simpl. erewrite IHdefs; eauto.
    unfold add_global. destruct a. destruct p. destruct o; auto.
    destruct g; auto.
Qed.

Lemma transl_prog_pres_senv : forall gmap lmap dsize csize efsize tprog prog,
    transl_prog_with_map gmap lmap prog dsize csize efsize = OK tprog ->
    (Genv.genv_senv (globalenv tprog)) = (Globalenvs.Genv.globalenv prog).
Proof.
  intros gmap lmap dsize csize efsize tprog0 prog0 H.
  monadInv H. unfold globalenv. simpl.
  rewrite add_globals_pres_senv; eauto.
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
  intros.
  destruct i; inv H3; simpl in *; monadInvX H4;
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
    repeat destr_in H6.
    destruct ros; simpl in *; monadInvX EQ.
    do 2 eexists; split; eauto.
    econstructor; eauto.
    apply regset_inject_expand; auto.
    do 2 eexists; split; eauto.
    econstructor; eauto.
    apply regset_inject_expand; auto.
    inversion MATCHSMINJ. 
    exploit (agree_sminj_glob0 i s); eauto.
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
    repeat destr_in H6.
    generalize (RSINJ PC).
    destruct ros; simpl in *; monadInvX EQ; do 2 eexists; split; eauto; econstructor; eauto.
    repeat apply regset_inject_expand; auto.
    + apply Val.offset_ptr_inject. eauto.
    + repeat apply regset_inject_expand; auto.
      apply Val.offset_ptr_inject. eauto.
      exploit (inject_symbol_sectlabel gm lm j i s Ptrofs.zero); eauto.
      
  (* - (* Pallocframe *) *)
  (*   generalize (RSINJ RSP). intros RSPINJ. *)
  (*   destruct (Mem.storev Mptr m1 *)
  (*                        (Val.offset_ptr *)
  (*                           (Val.offset_ptr (rs1 RSP) *)
  (*                                           (Ptrofs.neg (Ptrofs.repr (align (frame_size frame) 8)))) *)
  (*                           ofs_ra) (rs1 RA)) eqn:STORERA; try inv H6. *)
  (*   exploit (fun a1 a2 => *)
  (*              storev_mapped_inject' j Mptr m1 a1 (rs1 RA) m1' m2 a2 (rs2 RA)); eauto with inject_db. *)
  (*   intros (m2' & STORERA' & MINJ2). *)
  (*   destruct (rs1 RSP) eqn:RSP1; simpl in *; try congruence. *)
  (*   inv RSPINJ. *)
  (*   eexists; eexists. *)
  (*   (* Find the resulting state *) *)
  (*   rewrite <- H5 in STORERA'. rewrite STORERA'. split. eauto. *)
  (*   (* Solve match states *) *)
  (*   eapply match_states_intro; eauto. *)
  (*   eapply nextinstr_pres_inject; eauto. *)
  (*   repeat eapply regset_inject_expand; eauto. *)
  (*   eapply Val.inject_ptr; eauto. *)
  (*   repeat rewrite (Ptrofs.add_assoc i). *)
  (*   rewrite (Ptrofs.add_commut (Ptrofs.repr delta)). auto. *)
  (*   eapply store_pres_glob_block_valid; eauto. *)

  (* - (* Pfreeframe *) *)
  (*   generalize (RSINJ RSP). intros. *)
  (*   destruct (Mem.loadv Mptr m1 (Val.offset_ptr (rs1 RSP) ofs_ra)) eqn:EQRA; try inv H6. *)
  (*   exploit (fun g a2 => Mem.loadv_inject j g m1' m2 Mptr (Val.offset_ptr (rs1 Asm.RSP) ofs_ra) a2 v); eauto. *)
  (*   apply Val.offset_ptr_inject. auto. *)
  (*   intros (v2 & MLOAD2 & VINJ2). *)
  (*   eexists; eexists. split. simpl. *)
  (*   setoid_rewrite MLOAD2. auto. *)
  (*   eapply match_states_intro; eauto with inject_db. *)

  - repeat destr_in H6. simpl. 
    eexists _, _; split; eauto. econstructor; eauto.
    repeat apply regset_inject_expand; auto.
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
    exploit (agree_sminj_instr gm lm j MATCHSMINJ b b2 f ofs delta (Asm.Pbuiltin ef args res)); auto.
    intros (id & i' & sid & ofs1 & FITARG & FSYMB & TRANSL).
    (* exploit (globs_to_funs_inj_into_flatmem j); eauto. inversion 1; subst. *)
    monadInv TRANSL. monadInv EQ.
    set (pbseg := {| segblock_id := sid; segblock_start := Ptrofs.repr ofs1; segblock_size := Ptrofs.repr (instr_size (Asm.Pbuiltin ef args res)) |}) in *.
    exploit (eval_builtin_args_inject gm lm j m m'0 rs rs'0 (rs Asm.RSP) (rs'0 Asm.RSP) args vargs x0); auto.
    intros (vargs' & EBARGS & ARGSINJ).
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { 
      unfold match_prog in TRANSF. unfold transf_program in TRANSF.
      repeat destr_in TRANSF. 
      symmetry. eapply transl_prog_pres_senv; eauto.
    }
    generalize (external_call_inject ge j vargs vargs' m m'0 m' vres t ef ARGSINJ MINJ H3).
    rewrite SENVEQ.
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
    edestruct storev_mapped_inject' as (m2' & SV & INJ2); eauto.
    apply Val.offset_ptr_inject. eauto.
    edestruct (extcall_arguments_inject) as (args2 & ARGSINJ & EXTCALLARGS); eauto.
    assert (Globalenvs.Genv.to_senv ge = (Genv.genv_senv tge)) as SENVEQ. 
    { 
      unfold match_prog in TRANSF. unfold transf_program in TRANSF.
      repeat destr_in TRANSF. 
      symmetry. eapply transl_prog_pres_senv; eauto.
    }
    exploit (external_call_inject ge j args args2 ); eauto.
    rewrite SENVEQ.
    intros (j' & res' & m2'' & EXTCALL & RESINJ & MINJ' & INJINCR & INJSEP).
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
        intros b1 b0 delta0 J1 J2.
        generalize (INJSEP _ _ _ J1 J2).
        unfold Mem.valid_block. rewnb. eauto.
      (* * eapply (inject_pres_globs_inj_into_flatmem j); eauto. *)
      * eapply (inject_pres_valid_instr_offset_is_internal j); eauto.
        intros b1 b0 delta0 J1 J2.
        generalize (INJSEP _ _ _ J1 J2).
        unfold Mem.valid_block. rewnb. eauto.
      * eapply (inject_pres_extfun_entry_is_external j); eauto.
        intros b1 b0 delta0 J1 J2.
        generalize (INJSEP _ _ _ J1 J2).
        unfold Mem.valid_block. rewnb. eauto.
      * eapply (inject_pres_match_find_funct j); eauto.
        intros b1 b0 delta0 J1 J2.
        generalize (INJSEP _ _ _ J1 J2).
        unfold Mem.valid_block. rewnb. eauto.
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
        red. red. rewnb. eauto.
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
  forward_simulation (RawAsm.semantics prog (Pregmap.init Vundef)) (FlatAsm.semantics tprog (Pregmap.init Vundef)).
Proof.
  eapply forward_simulation_step with match_states.
  - simpl. intros. 
    unfold match_prog in TRANSF. unfold transf_program in TRANSF.
    repeat destr_in TRANSF.    
    erewrite transl_prog_pres_senv; eauto. auto.
  - simpl. intros s1 IS. 
    exploit transf_initial_states; eauto.
    intros.
    rewrite Pregmap.gi. auto.
  - simpl. intros s1 s2 r MS FS. eapply transf_final_states; eauto.
  - simpl. intros s1 t s1' STEP s2 MS. 
    edestruct step_simulation as (STEP' & MS'); eauto.
Qed.

End PRESERVATION.


End WITHMEMORYMODEL.