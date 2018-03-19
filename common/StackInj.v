Require Import Coqlib Tactics StackADT.

(* Specifying the shape of stack injection functions *)

(* [compat_frameinj_rec l g ns nt]
   [ns] is the stage position in the source stack, [nt] in the target stack.
   [l] is the target call stack.
   [g] is compatible with [l] if the corresponding frames are injected correctly by [g].
   Tailcalled stack frames are injected into the current target stage and we do
   not increment the target stage.
 *)

Fixpoint compat_frameinj_rec (l: list nat) (g: frameinj) (ns nt: nat) :=
  match l with
    nil => forall i j (LE: (ns <= i)%nat) (Gi: g i = Some j), (nt <= j)%nat
  | n :: l =>
    (forall i, ns <= i < ns + n -> g i = Some nt)%nat /\ compat_frameinj_rec l g (ns + n) (S nt)
  end.

Definition compat_frameinj l g := compat_frameinj_rec l g O O.

Lemma compat_frameinj_rec_above:
  forall l g ns nt (CFG: compat_frameinj_rec l g ns nt)
    i j (Gi: g i = Some j) (LE: (ns <= i)%nat),
    (nt <= j)%nat.
Proof.
  induction l; simpl; intros; eauto.
  destruct CFG as (GNS & GABOVE).
  destruct (lt_dec i (ns + a)); auto.
  rewrite GNS in Gi; auto. inv Gi; omega.
  eapply IHl in GABOVE. 2: apply Gi. omega. omega.
Qed.

Open Scope Z_scope.

Definition sizes g s1 s2 :=
  forall i2 f2
    (FAP2: f2 @ s2 : i2),
    exists i1 f1,
      g i1 = Some i2 /\
      (f1 @ s1 : i1) /\
      size_frames f2 <= size_frames f1.

Lemma compat_sizes_tl:
  forall l g m1 m2,
    compat_frameinj (1%nat::l) g ->
    sizes g m1 m2 ->
    sizes (down g) (tl m1) (tl m2).
Proof.
  unfold sizes; simpl; intros.
  destruct m2. simpl in *. inv FAP2. rewrite nth_error_nil in H1; inv H1. simpl in *.
  specialize (H0 (S i2) f2).
  trim H0. apply frame_at_pos_cons; auto.
  destruct H0 as (i1 & f1 & Gi & FAP1 & LE).
  destruct i1. rewrite (proj1 H) in Gi by omega. inv Gi.
  exists i1, f1; split; [|split].
  unfold down, downstar. rewrite Gi. reflexivity. destruct m1. inv FAP1. rewrite nth_error_nil in H0. inv H0. simpl.
  apply frame_at_pos_cons_inv in FAP1. simpl in *; auto. omega. auto.
Qed.

Lemma compat_frameinj_rec_pop_left:
  forall g l ns nt
    (CF: compat_frameinj_rec l g (S ns) nt),
    compat_frameinj_rec l (fun n : nat => g (S n)) ns nt.
Proof.
  induction l; simpl; intros; eauto.
  - eapply CF in Gi; eauto. omega.
  - destruct CF as [Gn CF]. split; intros.
    + apply Gn. omega.
    + eauto.
Qed.

Lemma compat_frameinj_rec_push_parallel:
  forall g l ns nt
    (CFR: compat_frameinj_rec l g ns nt)
    g'
    (G'spec: forall i, (S ns <= i)%nat -> g' i = option_map S (g (pred i))),
    compat_frameinj_rec l g' (S ns) (S nt).
Proof.
  induction l; simpl; intros; eauto.
  - rewrite G'spec in Gi; auto.
    unfold option_map in Gi; repeat destr_in Gi.
    eapply CFR in Heqo. omega. omega. 
  - destruct CFR as (Gn & CFR).
    split.
    + intros; rewrite G'spec; auto. rewrite Gn. reflexivity. omega. omega.
    + eapply IHl; eauto.
      intros; apply G'spec. omega.
Qed.

Lemma compat_frameinj_pop_right_rec:
  forall g l ns nt
    (CFR: compat_frameinj_rec l g ns (S nt))
    g' (G'spec: forall i, (ns <= i)%nat -> g' i = option_map pred (g i)),
    compat_frameinj_rec l g' ns nt.
Proof.
  induction l; simpl; intros; eauto.
  - rewrite G'spec in Gi; auto.
    unfold option_map in Gi; repeat destr_in Gi.
    eapply CFR in Heqo. omega. auto.
  - destruct CFR as (Gn & CFR).
    split.
    + intros; rewrite G'spec; auto.
      unfold option_map. rewrite Gn. reflexivity. omega. omega.
    + eapply IHl; eauto.
      intros; apply G'spec. omega.
Qed.


Lemma compat_frameinj_rec_upstar:
  forall l g g' ns nt,
    compat_frameinj_rec l g ns nt ->
    (forall i, ns < i -> g' i = g (pred i))%nat ->
    compat_frameinj_rec l g' (S ns) nt.
Proof.
  induction l; simpl; intros g g' ns nt CFG HYP.
  - intros i j LE G'. rewrite HYP in G' by omega. apply CFG in G'. auto. omega.
  - destruct CFG as (HYP' & CFG). split.
    + intros; rewrite HYP by omega. apply HYP'. omega.
    + eapply IHl. eauto. intros; apply HYP. omega.
Qed.

Lemma compat_frameinj_pop_right:
  forall g n l,
    compat_frameinj (n :: l) g ->
    compat_frameinj (S n :: l) (upstar g).
Proof.
  intros g n l (A & B); split; simpl; auto.
  unfold upstar. intros. destr. apply A. omega.
  simpl in B.
  eapply compat_frameinj_rec_upstar; eauto.
  unfold upstar.
  intros. destr. omega.
Qed.

Lemma compat_frameinj_rec_pop_parallel:
  forall g l ns nt
    (CFR: compat_frameinj_rec l g (S ns) (S nt)),
    compat_frameinj_rec l (down g) ns nt.
Proof.
  unfold down, downstar.
  induction l; simpl; intros; eauto.
  - unfold option_map in Gi; repeat destr_in Gi.
    eapply CFR in Heqo. omega. omega.
  - destruct CFR as (Gn & CFR).
    split.
    intros; rewrite Gn. reflexivity. omega.
    eapply IHl; eauto.
Qed.


Fixpoint sum (l: list Z) :=
  match l with
    nil => 0
  | a::r => a + sum r
  end.

Require Import Permutation.

Lemma size_stack_permut:
  forall s s',
    Permutation s s' ->
    size_stack s = size_stack s'.
Proof.
  induction 1; simpl; intros; eauto; omega.
Qed.

Lemma size_stack_app:
  forall s1 s2,
    size_stack (s1 ++ s2) = size_stack s1 + size_stack s2.
Proof.
  induction s1; simpl; intros; eauto. rewrite IHs1. omega.
Qed.

Lemma size_stack_concat:
  forall ss,
    size_stack (concat ss) = sum (map size_stack ss).
Proof.
  induction ss; simpl; intros; eauto.
  rewrite size_stack_app.
  omega.
Qed.

Definition inject_into (g: frameinj) (thr: nat) (target: nat) : list nat :=
  filter (fun i => option_eq Nat.eq_dec (g i) (Some target)) (list_nats thr).

Fixpoint frames_at {A} (l: list nat) (s: list A) : option (list A) :=
  match l with
  | nil => Some nil
  | a::r => match nth_error s a with
             Some f => option_map (fun r => f :: r) (frames_at r s)
           | None => None
           end
  end.

Opaque minus.

Lemma frames_at_cons:
  forall {A} l (s: list A) a,
    frames_at l s = frames_at (map S l) (a::s).
Proof.
  induction l; simpl; intros; eauto.
  destr.
Qed.

Lemma frames_at_eq:
  forall {A} (s: list A),
    frames_at (map (fun n => length s - S n)%nat (list_nats (length s))) s = Some (s).
Proof.
  induction s; simpl; intros. auto.
  replace (S (length s) - S (length s))%nat with O by omega. simpl.
  unfold option_map.
  erewrite map_ext_in with (g := fun n => (S (length s - S n))%nat).
  rewrite <- map_map. rewrite <- frames_at_cons. rewrite IHs. auto.
  intros. rewrite in_list_nats in H.
  omega.
Qed.

Lemma list_nats_S:
  forall n,
    list_nats (S n) = map S (list_nats n) ++ O :: nil.
Proof.
  induction n; simpl; intros; eauto.
  rewrite <- IHn. simpl. auto.
Qed.

Lemma map_list_nats_rev:
  forall n,
    map (fun m => n - S m)%nat (list_nats n) = rev (list_nats n).
Proof.
  induction n; simpl; intros. reflexivity.
  erewrite map_ext_in with (g := fun m => (S (n - S m))%nat).
  rewrite <- map_map. 
  2: intros; rewrite in_list_nats in H; omega.
  rewrite minus_diag.
  rewrite IHn. rewrite map_rev. rewrite <- rev_unit.
  rewrite <- list_nats_S. simpl. reflexivity.
Qed.

Lemma frames_at_permut:
  forall {A} (s: list A) (l1 l2: list nat) (P: Permutation l1 l2) f1,
    frames_at l1 s = Some f1 ->
    exists f2,
      frames_at l2 s = Some f2 /\ Permutation f1 f2.
Proof.
  induction 1; simpl; unfold option_map; intros; eauto.
  - repeat destr_in H. edestruct IHP as (f2 & FAT & PERM); eauto. rewrite FAT. eexists; split; eauto.
  - repeat destr_in H. repeat destr_in Heqo0.
    eexists; split; eauto. apply perm_swap.
  - edestruct IHP1 as (f2 & FAT1 & PERM); eauto.
    edestruct IHP2 as (f3 & FAT2 & PERM2); eauto.
    eexists; split; eauto.
    eapply perm_trans; eauto.
Qed.

Lemma frames_at_permut':
  forall {A} (s: list A) f,
    frames_at (list_nats (length s)) s = Some f ->
    Permutation f s.
Proof.
  intros A s f FAT.
  edestruct (frames_at_permut s) as (f2 & FAT2 & PERM12).
  apply Permutation_rev. apply FAT. rewrite <- map_list_nats_rev in FAT2.
  rewrite frames_at_eq in FAT2. inv FAT2. auto.
Qed.

Lemma frames_at_permut_ex:
  forall {A} (s: list A),
  exists f, frames_at (list_nats (length s)) s = Some f /\
       Permutation f s.
Proof.
  intros A s.
  edestruct (frames_at_permut s) as (f2 & FAT2 & PERM12).
  2: apply frames_at_eq.
  rewrite map_list_nats_rev. symmetry; apply Permutation_rev. eexists; split; eauto. symmetry; eauto.
Qed.

Fixpoint opt_concat {A} (l: list (option (list A))) : option (list A) :=
  match l with
    nil => Some nil
  | None :: l => None
  | Some a::l =>
    match opt_concat l with
    | None => None
    | Some r => Some (a ++ r)
    end
  end.

Lemma frames_at_app:
  forall {A} (s: list A) l1 l2,
    frames_at (l1 ++ l2) s =
    match frames_at l1 s with
      Some r1 =>
      match frames_at l2 s with
        Some r2 => Some (r1++r2)
      | _ => None
      end
    | _ => None
    end.
Proof.
  induction l1; simpl; intros; eauto. destr.
  destr.
  rewrite IHl1. destr. destr.
Qed.

Lemma opt_concat_concat:
  forall {A} (s: list A) l,
    opt_concat (map (fun f => frames_at f s) l) = frames_at (concat l) s.
Proof.
  induction l; simpl; intros; eauto.
  rewrite frames_at_app. rewrite IHl. reflexivity.
Qed.

Lemma frames_at_permut_concat:
  forall {A} (s: list A) ff,
    Permutation (list_nats (length s)) (concat ff) ->
    exists t, opt_concat (map (fun f => frames_at f s) ff) = Some t /\
    Permutation t s.
Proof.
  intros.
  rewrite opt_concat_concat.
  edestruct (frames_at_permut_ex s) as (f & EQ & PERM).
  edestruct (frames_at_permut s) as (t & EQ' & PERM'); eauto.
  eexists; split; eauto.
  symmetry in PERM'. etransitivity; eauto.
Qed.

Inductive sublist {A: Type}  : list A -> list A -> Prop :=
| sublist_intro s: sublist nil s
| sublist_skip a s1 s2: sublist s1 s2 -> sublist s1 (a::s2)
| sublist_same a s1 s2: sublist s1 s2 -> sublist (a::s1) (a::s2).

Lemma frames_at_filter:
  forall {A} g (s: list A) l f,
    frames_at l s = Some f ->
    exists f', frames_at (filter g l) s = Some f' /\ sublist f' f.
Proof.
  induction l; simpl; intros. inv H.
  - eexists; split; eauto. constructor.
  - unfold option_map in H. repeat destr_in H.
    edestruct IHl as (f' & FAT & SUB); eauto.
    repeat (destr; simpl; unfold option_map).
    inv FAT. inv Heqo.
    eexists; split; eauto. apply sublist_same; eauto.
    eexists; split; eauto. apply sublist_skip; eauto.
Qed.

Lemma size_stack_sublist:
  forall s1 s2,
    sublist s1 s2 ->
    size_stack s1 <= size_stack s2.
Proof.
  induction 1; simpl; intros; eauto. apply size_stack_pos.
  generalize (size_frames_pos a); omega.
  omega.
Qed.

Definition smallest (g: frameinj) i1 s1 :=
  match g i1 with
    Some i2 =>
    forallb (fun i => negb (option_eq Nat.eq_dec (g i) (Some i2)) || le_dec i1 i) (list_nats s1)
  | None => false
  end.

Fixpoint minl (l: list nat) : option nat :=
  match l with
  | nil => None
  | a::r => match minl r with
             Some b => Some (Nat.min a b)
           | None => Some a
           end
  end.

Lemma smallest_spec:
  forall g i n1,
    smallest g i n1 = true ->
    (forall i j, g i = Some j -> i < n1)%nat ->
    exists i2,
      g i = Some i2 /\ forall i', g i' = Some i2 -> (i <= i')%nat.
Proof.
  unfold smallest. intros. destr_in H.
  eexists; split; eauto.
  rewrite forallb_forall in H. intros.
  specialize (H i'). trim H. apply in_list_nats. eauto.
  apply orb_true_iff in H.
  rewrite H1 in H.
  destruct (le_dec i i'); simpl in *; auto.
  destruct H; try congruence.
  rewrite negb_true_iff in H.
  destruct option_eq; simpl in H; try congruence.
Qed.

Lemma map_concat:
  forall {A} (l: list A),
    concat (map (fun x => x::nil) l) = l.
Proof.
  induction l; simpl; intros; eauto. congruence.
Qed.

Lemma partition:
  forall {A} f 
    (l2: list A)
    (l1: list A)
    (INCL: forall i, In i l2 -> forall x, In x (f i) -> In x l1)
    x
    (IN: In x (concat (map f l2))),
    In x l1.
Proof.
  induction l2; simpl; intros; eauto.
  - easy.
  - rewrite in_app in IN.
    destruct IN; eauto.
Qed.

Lemma lnr_concat:
  forall {A B} (f: A -> list B)
    (LNRf: forall i, list_norepet (f i))
    (DISJ: forall i j, i <> j -> list_disjoint (f i) (f j))
    (l2: list A)
    (LNR2: list_norepet l2),
    list_norepet (concat (map f l2)).
Proof.
  intros A B f LNRf DISJ l2.
  induction 1; simpl. constructor.
  apply list_norepet_app. split; [|split]; auto.
  red; intros.
  rewrite concat_In in H1.
  destruct H1 as (xx & INx & INMAP).
  rewrite in_map_iff in INMAP. destruct INMAP as (a & Fa & INFa).
  subst.
  eapply DISJ. 2: apply H0. 2: apply INx. congruence.
Qed.

Lemma norepet_incl_perm_sublist:
  forall {A} (l1: list A)
    (lnr1: list_norepet l1)
    l2
    (incl: forall x, In x l1 -> In x l2),
  exists l2', sublist l1 l2' /\ Permutation l2 l2'.
Proof.
  induction 1; simpl; intros.
  - exists l2; split. constructor. reflexivity.
  - edestruct (in_split hd l2) as (l1' & l2' & EQ). apply incl; auto. subst.
    edestruct (IHlnr1 (l1' ++ l2')) as (l3' & SUB & PERM).
    intros. specialize (incl _ (or_intror H0)).
    rewrite in_app in incl. rewrite in_app. destruct incl as [IN|[EQ|IN]]; auto. subst. congruence.
    exists (hd::l3'); split. apply sublist_same; auto.
    etransitivity. symmetry. apply Permutation_middle. apply perm_skip. auto.
Qed.

Lemma filter_norepet:
  forall {A} f (l: list A),
    list_norepet l ->
    list_norepet (filter f l).
Proof.
  induction 1; simpl; intros; try destr; econstructor; eauto.
  rewrite filter_In. intros (B & C). congruence.
Qed.

Lemma sublist_inj:
  forall g (l1 l2: list nat),
    list_norepet l1 ->
    list_norepet l2 ->
  exists l1',
    sublist
      (concat (map
                 (fun j => filter (fun i => option_eq Nat.eq_dec (g i) (Some j)) l1)
                 l2)) l1'
      /\ Permutation l1 l1'.
Proof.
  intros. apply norepet_incl_perm_sublist; auto.
  - apply lnr_concat; auto.
    + intros; apply filter_norepet; auto.
    + intros i j DIFF x y INx INy.
      rewrite filter_In in INx, INy.
      destruct INx as (INx & EQx), INy as (INy & EQy).
      destruct option_eq; simpl in *; try congruence.
      destruct option_eq; simpl in *; try congruence.
  - intros x INC.
    rewrite concat_In in INC.
    setoid_rewrite in_map_iff in INC.
    destruct INC as (x0 & INx0 & (xx & EQx0 & INl2)).
    subst.
    rewrite filter_In in INx0.
    destruct INx0; auto.
Qed.


Lemma lnr_list_nats:
  forall n,
    list_norepet (list_nats n).
Proof.
  induction n; simpl; intros; constructor; eauto.
  rewrite in_list_nats. omega.
Qed.

Lemma sublist_frames_at:
  forall {A} (s: list A) (l1 l2: list nat) (S: sublist l1 l2)
    t2 (EQ: frames_at l2 s = Some t2),
  exists t1, frames_at l1 s = Some t1 /\ sublist t1 t2.
Proof.
  induction 1; simpl; intros; eauto.
  - exists nil; split; eauto. constructor.
  - unfold option_map in EQ. repeat destr_in EQ.
    edestruct IHS as (t1 & EQ & SS); eauto.
    exists t1; split; auto. apply sublist_skip. auto.
  - unfold option_map in EQ. repeat destr_in EQ.
    edestruct IHS as (t1 & EQ & SS); eauto.
    rewrite EQ. simpl.
    eexists; split; eauto. apply sublist_same. auto.
Qed.


Lemma frames_at_succeeds:
  forall {A} (s: list A) l,
    Forall (fun p => p < length s)%nat l ->
    exists f, frames_at l s = Some f.
Proof.
  induction 1; simpl; intros; eauto.
  destruct IHForall as (f & EQ); rewrite EQ.
  rewrite <- nth_error_Some in H. destr.
  simpl. eauto.
Qed.

Lemma min_exists:
  forall l i, In i l -> exists mi, minl l = Some mi.
Proof.
  destruct l; simpl. easy. intros. destr; eauto.
Qed.

Lemma min_in:
  forall l m,
    minl l = Some m ->
    In m l /\ forall x, In x l -> (m <= x)%nat.
Proof.
  induction l; simpl; intros; eauto. easy.
  repeat destr_in H.
  - specialize (IHl _ eq_refl). destruct IHl as (IN & MIN).
    split. destruct (le_dec a n). rewrite Nat.min_l; auto.
    rewrite Nat.min_r by omega. auto.
    intros. destruct H. subst. apply Nat.le_min_l.
    apply Nat.min_le_iff. apply MIN in H. auto.
  - destruct l. simpl. split; auto. intros x [|[]]; subst; omega.
    simpl in Heqo. destr_in Heqo.
Qed.
Lemma frames_at_in:
  forall s l i t f,
    frames_at l s = Some t ->
    In i l ->
    frame_at_pos s i f -> In f t.
Proof.
  induction l; simpl; intros; eauto. easy. unfold option_map in H; repeat destr_in H.
  destruct H0; subst. inv H1. rewrite Heqo in H; inv H. left; auto.
  eapply IHl in H. 2: reflexivity. 2: eauto. right; auto.
Qed.

Lemma opt_concat_sizes:
  forall l1 l2,
    list_forall2 (fun ol1 ol2 => match ol1, ol2 with
                                Some l1, Some l2 => size_stack l1 <= size_stack l2
                              | _, _ => False
                              end) l1 l2 ->
    forall s1 s2,
      opt_concat l1 = Some s1 ->
      opt_concat l2 = Some s2 ->
      size_stack s1 <= size_stack s2.
Proof.
  induction 1; simpl; intros. inv H; inv H0. omega.
  repeat destr_in H. subst.
  repeat destr_in H1. repeat destr_in H2.
  rewrite ! size_stack_app.
  specialize (IHlist_forall2 _ _ eq_refl eq_refl); omega.
Qed.

Lemma lf2_list_ints_map:
  forall {A B C} (f1: A -> B) (f2: A -> C) (P: B -> C -> Prop)
    (l: list A)
    (PROP: forall x, In x l -> P (f1 x) (f2 x)),
    list_forall2 P (map f1 l) (map f2 l).
Proof.
  induction l; simpl; intros; constructor; eauto.
Qed.

Lemma sizes_size_stack:
  forall g s1 s2
    (SZ: sizes g s1 s2)
    (SURJ: frameinj_surjective g (length s2))
    (RNG: forall i j, (g i = Some j -> i < length s1 /\ j < length s2)%nat),
    size_stack s2 <= size_stack s1.
Proof.
  intros.
  edestruct (frames_at_permut_concat s2) as (f2 & FAT2 & PERM2). rewrite map_concat. reflexivity.
  rewrite <- (size_stack_permut _ _ PERM2).
  edestruct (sublist_inj g (list_nats (length s1)) (list_nats (length s2))) as (l1' & SUB & PERM).
  apply lnr_list_nats.
  apply lnr_list_nats.
  destruct (frames_at_permut_ex s1) as (f & FAT1 & PERM1).
  destruct (frames_at_permut _ _ _ PERM _ FAT1) as (f3 & FAT3 & PERM3).
  destruct (sublist_frames_at s1 _ _ SUB _ FAT3) as (f4 & FAT4 & SUB2).
  rewrite <- (size_stack_permut _ _ PERM1).
  rewrite (size_stack_permut _ _ PERM3).
  etransitivity.
  2: apply (size_stack_sublist _ _ SUB2).
  rewrite <- opt_concat_concat in FAT4.
  eapply opt_concat_sizes. 2-3: eauto.
  rewrite ! map_map.
  apply lf2_list_ints_map.
  clear - SZ SURJ RNG.
  simpl.
  setoid_rewrite in_list_nats.
  intros j LT.
  rewrite <- nth_error_Some in LT.
  destruct nth_error eqn:?; try congruence.
  edestruct (frames_at_succeeds s1) as (f & EQ).
  2: rewrite EQ.
  rewrite Forall_forall; intros x IN. rewrite filter_In in IN.
  rewrite in_list_nats in IN. apply IN.
  red in SZ.
  simpl.

  destruct (SZ _ _ (frame_at_pos_intro _ _ _ Heqo)) as (i1 & f1 & Gi & FAP1 & LE).
  etransitivity. apply LE.
  eapply frames_at_in in FAP1; eauto.
  destruct (in_split _ _ FAP1) as (l1 & l2 & EQl12).
  subst.
  rewrite size_stack_app. simpl.
  generalize (size_stack_pos l1) (size_stack_pos l2). omega.
  rewrite filter_In. rewrite in_list_nats.
  split. eapply frame_at_pos_lt; eauto.
  rewrite Gi. destruct option_eq; auto.
Qed.

Lemma sizes_tl_left:
  forall g s1 s2
    (SZ: sizes g s1 s2)
    (G0: g O = None)
    (NO0: forall n, g n <> Some O),
    sizes (downstar g) (tl s1) s2.
Proof.
  unfold downstar. red; intros.
  destruct (SZ i2 f2) as (i1 & f1 & Gi1 & FAP1 & LE). auto.
  destruct i1. congruence.
  destruct s1. inv FAP1. rewrite nth_error_nil in H. inv H.
  exists i1, f1; split; eauto.
  split. simpl. apply frame_at_pos_cons_inv in FAP1. simpl in *; auto. omega. auto.
Qed.

Lemma sizes_ext:
  forall g g' m1 m2,
    sizes g m1 m2 ->
    (forall i, g i = g' i) ->
    sizes g' m1 m2.
Proof.
  red; intros; eauto.
  setoid_rewrite <- H0. eauto.
Qed.

Lemma down_upstar_is_pred:
  forall g i,
    down (upstar g) i = option_map pred (g i).
Proof.
  unfold down, downstar, upstar, option_map. auto.
Qed.

(* Lemma sizes_no_0: *)
(*   forall g s1 s2, *)
(*     sizes g s1 s2 -> *)
(*     sizes (fun n => if option_eq Nat.eq_dec (g n) (Some O) then None else g n) s1 s2. *)
(* Proof. *)
(*   red; intros. *)
(*   edestruct H as (i1 & f1 & Gi1 & FAP1 & LE). eauto. *)
(*   destr_in G. *)
(*   eapply H; eauto. *)
(*   intros. *)
(*   eapply SMALLEST. destr. *)
(* Qed. *)

Lemma compat_frameinj_rec_ext:
  forall l g g' ns nt (EXT: forall i, g i = g' i)
    (CFR: compat_frameinj_rec l g ns nt),
    compat_frameinj_rec l g' ns nt.
Proof.
  induction l; simpl; intros; eauto. rewrite <- EXT in Gi; eauto.
  destruct CFR as (LE & CFR); split; eauto.
  intros; rewrite <- EXT; eauto.
Qed.

Lemma frame_at_pos_tl:
  forall f s i,
    f @ s : S i <-> f @ tl s : i.
Proof.
  split. destruct s. inversion 1. rewrite nth_error_nil in H0; inv H0.
  intros.
  apply frame_at_pos_cons_inv in H; auto. omega.
  destruct s; simpl in *; intros. 
  inv H; rewrite nth_error_nil in H0. inv H0.
  apply frame_at_pos_cons. auto.
Qed.

Lemma compat_sizes_tl':
  forall l g m1 m2
    (CFG: compat_frameinj (1%nat::l) g)
    g'
    (EXT: forall i, g' i = match g i with
                      | Some j => if Nat.eq_dec j O then None else Some j
                      | None => None
                      end)
    (SZ: sizes g' m1 m2),
    sizes (down g') (tl m1) (tl m2).
Proof.
  unfold sizes; simpl; intros.
  destruct m2. simpl in *. inv FAP2. rewrite nth_error_nil in H; inv H. simpl in *.
  destruct (SZ (S i2) f2) as (i1 & f1 & Gi1 & FAP1 & LE). apply frame_at_pos_cons; auto.
  rewrite EXT in Gi1. destr_in Gi1. destr_in Gi1. inv Gi1.
  unfold down, downstar.
  destruct i1. rewrite (proj1 CFG) in Heqo by omega. inv Heqo.
  exists i1, f1; split. rewrite EXT, Heqo. destr.
  split; auto.
  apply frame_at_pos_tl. auto.
Qed.

Lemma compat_sizes_tl'':
  forall l g m1 m2
    (CFG: compat_frameinj (1%nat::l) g)
    g'
    (EXT: forall i, g' i = match g i with
                      | Some j => if Nat.eq_dec j O then None else Some j
                      | None => None
                      end)
    (SZ: sizes g' m1 m2),
    sizes (down g) (tl m1) (tl m2).
Proof.
  unfold sizes; simpl; intros.
  destruct m2. simpl in *. inv FAP2. rewrite nth_error_nil in H; inv H. simpl in *.
  destruct (SZ (S i2) f2) as (i1 & f1 & Gi & FAP1 & LE). apply frame_at_pos_cons; auto.
  destruct m1. simpl in *. inv FAP1. rewrite nth_error_nil in H; inv H. simpl in *.
  unfold down, downstar.
  rewrite EXT in Gi. repeat destr_in Gi.
  destruct i1. rewrite (proj1 CFG) in Heqo. inv Heqo. omega.
  exists i1. rewrite Heqo. eexists; split; eauto.
  split; eauto. apply frame_at_pos_cons_inv in FAP1. auto. omega.
Qed.

Lemma compat_sizes_tl''_other:
  forall l g m1 m2
    (CFG: compat_frameinj (1%nat::l) g)
    (SZ: sizes g m1 m2),
    sizes (down g) (tl m1) (tl m2).
Proof.
  unfold sizes; simpl; intros.
  destruct m2. simpl in *. inv FAP2. rewrite nth_error_nil in H; inv H. simpl in *.
  destruct (SZ (S i2) f2) as (i1 & f1 & Gi & FAP1 & LE). apply frame_at_pos_cons; auto.
  destruct m1. simpl in *. inv FAP1. rewrite nth_error_nil in H; inv H. simpl in *.
  unfold down, downstar.
  destruct i1. rewrite (proj1 CFG) in Gi. inv Gi. omega.
  exists i1. rewrite Gi. eexists; split; eauto.
  split; eauto. apply frame_at_pos_cons_inv in FAP1. auto. omega.
Qed.


Lemma frame_at_pos_tl_iter:
  forall f n s i,
    f @ (Nat.iter n (@tl _) s) : i <-> f @ s : (n + i)%nat.
Proof.
  induction n; simpl; intros. tauto.
  split. intro H.
  apply frame_at_pos_tl in H.
  apply IHn in H. rewrite plus_n_Sm. auto.
  intros.
  apply frame_at_pos_tl. apply IHn.
  replace (n + S i)%nat with (S (n + i))%nat. auto. omega.
Qed.

Lemma compat_sizes_tl''':
  forall l n g m1 m2
    (CFG: compat_frameinj (S n::l) g)
    (SZ: sizes g m1 m2),
    sizes (fun m => option_map pred (g (S n + m)%nat)) (Nat.iter (S n) (@tl _) m1) (tl m2).
Proof.
  unfold sizes; intros.
  apply frame_at_pos_tl in FAP2.
  specialize (SZ _ _ FAP2).
  destruct SZ as (i1 & f1 & Gi & FAP1 & LE).
  setoid_rewrite frame_at_pos_tl_iter.
  destruct (lt_dec i1 (S n)).
  rewrite (proj1 CFG) in Gi by omega. inv Gi.
  exists (i1 - S n)%nat, f1.
  replace (S n + (i1 - S n))%nat with i1 by omega.
  rewrite Gi. simpl. auto.
Qed.

Lemma size_stack_iter_tl:
  forall n l,
    size_stack (Nat.iter n (@tl _) l) <= size_stack l.
Proof.
  induction n; simpl; intros. reflexivity.
  etransitivity. apply size_stack_tl. auto.
Qed.

Lemma nat_iter_plus:
  forall {A} (f: A -> A) n m x,
    Nat.iter (n + m) f x = Nat.iter n f (Nat.iter m f x).
Proof.
  induction n; simpl; intros. auto. rewrite IHn. auto.
Qed.

Lemma size_stack_iter_tl_mono:
  forall n m l,
    (m <= n)%nat -> 
    size_stack (Nat.iter n (@tl _) l) <= size_stack (Nat.iter m (@tl _) l).
Proof.
  intros.
  replace n with ((n - m) + m)%nat by omega.
  rewrite nat_iter_plus.
  apply size_stack_iter_tl.
Qed.
Lemma length_tl:
  forall {A} (l: list A),
    length (tl l) = (length l - 1)%nat.
Proof.
  destruct l; simpl; auto. omega.
Qed.

Lemma length_iter_tl:
  forall {A} n (l: list A),
    (length (Nat.iter n (@tl _) l) = length l - n)%nat.
Proof.
  induction n; simpl; intros; eauto. omega.
  replace (length l - S n)%nat with ((length l - n) - 1)%nat by omega. rewrite <- IHn.
  apply length_tl.
Qed.
