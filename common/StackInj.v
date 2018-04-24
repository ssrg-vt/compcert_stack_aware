Require Import Coqlib Tactics StackADT.

(* Specifying the shape of stack injection functions *)

(* [compat_frameinj_rec l g ns nt]
   [ns] is the stage position in the source stack, [nt] in the target stack.
   [l] is the target call stack.
   [g] is compatible with [l] if the corresponding frames are injected correctly by [g].
   Tailcalled stack frames are injected into the current target stage and we do
   not increment the target stage.
 *)

(* Fixpoint compat_frameinj_rec (l: list nat) (g: frameinj) (ns nt: nat) := *)
(*   match l with *)
(*     nil => forall i j (LE: (ns <= i)%nat) (Gi: g i = Some j), (nt <= j)%nat *)
(*   | n :: l => *)
(*     (forall i, ns <= i < ns + n -> g i = Some nt)%nat /\ compat_frameinj_rec l g (ns + n) (S nt) *)
(*   end. *)

(* Definition compat_frameinj l g := compat_frameinj_rec l g O O. *)

(* Lemma compat_frameinj_rec_above: *)
(*   forall l g ns nt (CFG: compat_frameinj_rec l g ns nt) *)
(*     i j (Gi: g i = Some j) (LE: (ns <= i)%nat), *)
(*     (nt <= j)%nat. *)
(* Proof. *)
(*   induction l; simpl; intros; eauto. *)
(*   destruct CFG as (GNS & GABOVE). *)
(*   destruct (lt_dec i (ns + a)); auto. *)
(*   rewrite GNS in Gi; auto. inv Gi; omega. *)
(*   eapply IHl in GABOVE. 2: apply Gi. omega. omega. *)
(* Qed. *)

Open Scope Z_scope.

Inductive sizes : frameinj -> stack -> stack -> Prop :=
| sizes_nil: sizes nil nil nil
| sizes_cons g s1 s2 t1 n t2:
    sizes g (drop (S n) s1) s2 ->
    take (S n) s1 = Some t1 ->
    Exists (fun f1 => size_frames t2 <= size_frames f1) t1 ->
    sizes (S n::g) s1 (t2 :: s2).

Lemma compat_sizes_tl:
  forall g m1 m2,
    sizes (1%nat::g) m1 m2 ->
    sizes g (tl m1) (tl m2).
Proof.
  intros g m1 m2 SZ. inv SZ. simpl. simpl in *. auto.
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

Opaque minus.

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

Inductive sublist {A: Type}  : list A -> list A -> Prop :=
| sublist_intro s: sublist nil s
| sublist_skip a s1 s2: sublist s1 s2 -> sublist s1 (a::s2)
| sublist_same a s1 s2: sublist s1 s2 -> sublist (a::s1) (a::s2).

Lemma size_stack_sublist:
  forall s1 s2,
    sublist s1 s2 ->
    size_stack s1 <= size_stack s2.
Proof.
  induction 1; simpl; intros; eauto. apply size_stack_pos.
  generalize (size_frames_pos a); omega.
  omega.
Qed.

Fixpoint minl (l: list nat) : option nat :=
  match l with
  | nil => None
  | a::r => match minl r with
             Some b => Some (Nat.min a b)
           | None => Some a
           end
  end.

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

Lemma size_frames_le_size_stack:
  forall f s,
    In f s ->
    size_frames f <= size_stack s.
Proof.
  induction s; simpl; intros; eauto. easy.
  destruct H; subst. generalize (size_stack_pos s); omega.
  generalize (size_frames_pos a). trim IHs; auto. omega.
Qed.

Lemma sizes_size_stack:
  forall g s1 s2
    (SZ: sizes g s1 s2),
    size_stack s2 <= size_stack s1.
Proof.
  induction 1; simpl; intros; eauto.
  omega.
  rewrite (take_drop _ _ _ H).
  rewrite size_stack_app.
  cut (size_frames t2 <= size_stack t1). intros; omega.
  rewrite Exists_exists in H0. destruct H0 as (f1 & INf1 & LE).
  etransitivity. apply LE.
  eapply size_frames_le_size_stack; eauto.
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

Lemma tl_drop:
  forall {A} n (l: list A),
    drop n (tl l) = drop (S n) l.
Proof.
  reflexivity.
Qed.

Lemma drop_app:
  forall {A} n (s1 s2: list A),
    length s1 = n ->
    drop n (s1 ++ s2) = s2.
Proof.
  intros; subst.
  revert s1 s2; induction s1; simpl; intros; eauto.
Qed.

Lemma compat_sizes_drop:
  forall n g m1 m2
    (SZ: sizes (S n :: g) m1 m2),
    sizes g (drop (S n) m1) (tl m2).
Proof.
  intros. inv SZ. simpl.
  rewrite tl_drop. auto.
Qed.

Lemma size_stack_drop:
  forall n l,
    size_stack (drop n l) <= size_stack l.
Proof.
  induction n; simpl; intros. reflexivity.
  etransitivity. apply IHn. apply size_stack_tl.
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
    size_stack (drop n l) <= size_stack (drop m l).
Proof.
  intros.
  replace n with ((n - m) + m)%nat by omega.
  rewrite <- drop_drop. apply size_stack_drop.
Qed.

Lemma length_tl:
  forall {A} (l: list A),
    length (tl l) = (length l - 1)%nat.
Proof.
  destruct l; simpl; auto. omega.
Qed.

Lemma length_drop:
  forall {A} n (l: list A),
    (length (drop n l) = length l - n)%nat.
Proof.
  induction n; simpl; intros; eauto. omega.
  rewrite IHn. rewrite length_tl. omega.
Qed.
