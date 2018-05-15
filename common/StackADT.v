Require Import Coqlib.
Require Import MemPerm.
Require Import Memdata.
Require Import AST.
Require Import Values.
Require Export Assoc.
Require Intv.

Open Scope nat_scope.

(* To be moved to Coqlib *)
Definition option_prop {A} (P: A -> Prop) (oa: option A): Prop :=
  match oa with
    Some a => P a
  | None => True
  end.

Definition option_prop2 {A} (P: A -> A -> Prop) (oa ob: option A): Prop :=
  match oa, ob with
    Some a, Some b => P a b
  | Some a, None => False
  | _, _ => True
  end.


(** This file holds definitions related to our stack abstract data type (ADT).   *)

(** * Stack permissions *)

Inductive stack_permission: Type :=
  Public
| Private.

Definition stack_perm_eq: forall (p1 p2: stack_permission), {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
Qed.

(** Order on permissions: [Public] is greater than [Private]. Moreover,
    [stack_perm_le] is reflexive. *)

Definition stack_perm_le (sp1 sp2: stack_permission) :=
  match sp1, sp2 with
  | Private, _ => True
  | Public, Public => True
  | Public, _ => False
  end.

Lemma stack_perm_le_refl:
  forall p,
    stack_perm_le p p.
Proof.
  destruct p; red; auto.
Qed.

Lemma stack_perm_le_trans:
  forall p1 p2 p3,
    stack_perm_le p1 p2 ->
    stack_perm_le p2 p3 ->
    stack_perm_le p1 p3.
Proof.
  destruct p1,p2,p3; unfold stack_perm_le; intros; congruence.
Qed.


(** * Block information  *)

(** A block information records its size ([frame_size]) and the stack
    permissions for each offset of that block in [frame_perm]. *)

Record frame_info :=
  {
    frame_size: Z;
    frame_perm: Z -> stack_permission;
    frame_size_pos: (0 <= frame_size)%Z;
  }.

Definition public_frame_info sz : frame_info :=
  {|
    frame_size := Z.max 0 sz;
    frame_perm := fun _ => Public;
    frame_size_pos := Z.le_max_l _ _;
  |}.

Program Definition frame_info_of_size_and_pubrange (size: Z) (pubrange: Z * Z) : option frame_info :=
  if zlt 0 size
  then
    let '(lo,hi) := pubrange in
    Some {| frame_size := size; frame_perm := fun o => if zle lo o && zlt o hi then Public else Private; |}
  else None.
Next Obligation.
  omega.
Qed.

Definition frame_public f o := frame_perm f o = Public.

Definition frame_private f o := frame_perm f o = Private.

Definition frame_public_dec: forall f o, {frame_public f o} + {~ frame_public f o}.
Proof.
  unfold frame_public; intros; apply stack_perm_eq.
Qed.

Definition frame_private_dec: forall f o, {frame_private f o} + {~ frame_private f o}.
Proof.
  unfold frame_private; intros; apply stack_perm_eq.
Qed.

Definition public_stack_range (lo hi: Z) (fi: frame_info) : Prop :=
  forall ofs, (lo <= ofs < hi)%Z -> frame_public fi ofs.

Lemma public_stack_range_lo_ge_hi:
  forall lo hi fi, (hi <= lo)%Z -> public_stack_range lo hi fi.
Proof.
  red; intros; omega.
Qed.

Program Definition empty_frame: frame_info :=
  {|
    frame_size := 0;
    frame_perm o := Public;
  |}.

(** * Frame ADT  *)

(** A frame ADT records a list of blocks [frame_adt_blocks] and the size of the
    frame [frame_adt_size]. This size is _not_ the cumulated size of the blocks,
    but rather the stack space that will be necessary for the corresponding
    concrete frame down at the Mach and assembly languages. This size will match
    the size of the stack blocks in those low-level languages and will be used
    to construct the injection from the separate assembly blocks for every
    function to the continuous single stack in [RawAsm]. *)

Record frame_adt : Type :=
  {
    frame_adt_blocks: list (block * frame_info);
    frame_adt_size : Z;
    frame_adt_blocks_norepet:
      list_norepet (map fst frame_adt_blocks);
    frame_adt_size_pos:
      (0 <= frame_adt_size)%Z;
  }.

Lemma stack_perm_le_public:
  forall fi p o,
    (forall x, frame_perm fi x = Public) ->
    stack_perm_le p (frame_perm fi o).
Proof.
  intros fi p o PUB; rewrite PUB.
  destruct p; red; auto.
Qed.

(** * Tailcall frames *)

(** Tailcall frames are non-empty lists of [frame_adt]s. In most cases this list will be a
    singleton. When a tailcall is performed though, instead of popping the frame
    of the tail-caller and pushing the frame of the tailcalled function, we will
    append the frame of the tailcalled function to the current list. In this
    way, we record some form of history of the frames, enabling us to reason
    finely about tailcalls. *)

Definition tframe_adt := (option frame_adt * list frame_adt)%type.

(** * Stack ADT  *)

(** Finally, the stack itself is a list of tailcall frames.  *)

Definition stack := list tframe_adt.

(** Blocks belonging to frames, tframes, stacks.  *)

Definition get_frame_blocks (f: frame_adt) : list block :=
  map fst (frame_adt_blocks f).

Definition get_opt_frame_blocks (of: option frame_adt) : list block :=
  match of with
  | None => nil
  | Some f => get_frame_blocks f
  end.

Definition get_frames_blocks (tf: tframe_adt) : list block :=
  get_opt_frame_blocks (fst tf).  (* ++ concat (map get_frame_blocks (snd tf)). *)

Definition get_stack_blocks (s: stack) : list block :=
  concat (map get_frames_blocks s).

Definition in_frame (f: frame_adt) (b: block) : Prop :=
  In b (get_frame_blocks f).

Definition in_frames (l: tframe_adt) (b: block) :=
  In b (get_opt_frame_blocks (fst l)).

Definition in_stack (s: stack) (b: block) :=
  In b (get_stack_blocks s).

Definition in_frame' (f: frame_adt) bfi :=
  In bfi (frame_adt_blocks f).

Definition in_frames' (tf: tframe_adt) b :=
  match fst tf with
  | Some f => in_frame' f b
  | None => False
  end.

Fixpoint in_stack' (s: stack) b :=
  match s with
  | nil => False
  | tf::s => in_frames' tf b \/ in_stack' s b
  end.

Lemma in_frames'_rew:
  forall tf b,
    in_frames' tf b <->
    exists fr, in_frame' fr b /\ fst tf = Some fr.
Proof.
  unfold in_frames'. intros.
  destr; split; intros A; try decompose [ex and] A; try (intuition congruence);
    eexists; eauto.
Qed.

Lemma in_stack'_rew:
  forall s b,
    in_stack' s b <->
    exists (tf: tframe_adt),
      in_frames' tf b /\ In tf s.
Proof.
  induction s; simpl; split; intros; eauto.
  - easy.
  - decompose [ex and] H; easy.
  - destruct H; eauto. rewrite IHs in H.
    decompose [ex and] H; eauto.
  - rewrite IHs.
    decompose [ex and] H; eauto. destruct H2; subst; eauto.
Qed.

Lemma in_frame_dec:
  forall f b, {in_frame f b} + {~ in_frame f b}.
Proof.
  intros; apply in_dec, eq_block.
Defined.

Hint Resolve in_frame_dec.

Lemma in_frames_dec:
  forall l b, {in_frames l b} + {~ in_frames l b}.
Proof.
  intros; apply in_dec, eq_block.
Defined.

Hint Resolve in_frames_dec.

Lemma in_stack_dec:
  forall l b, {in_stack l b} + {~ in_stack l b}.
Proof.
  intros; apply in_dec, eq_block.
Defined.

Hint Resolve in_stack_dec.

Lemma in_stack_cons:
  forall a r b,
    in_stack (a::r) b <-> in_frames a b \/ in_stack r b.
Proof.
  unfold in_stack,in_frames.
  unfold get_stack_blocks.
  simpl.
  intros a r b. rewrite in_app. tauto.
Qed.

Lemma in_frames_cons:
  forall a r b,
    in_frames (a,r) b <-> (exists fa, a = Some fa /\ in_frame fa b).
Proof.
  unfold in_frames,in_frame.
  simpl. intuition.
  destruct a; simpl in *. eauto. easy.
  destruct H as (fa & EQ & IN); subst; eauto.
Qed.

Lemma in_stack_app:
  forall l1 l2 b,
    in_stack l1 b \/ in_stack l2 b <->
    in_stack (l1 ++ l2) b.
Proof.
  intros.
  unfold in_stack, get_stack_blocks in *.
  rewrite map_app, concat_app, in_app; tauto.
Qed.

(* Lemma in_frames_app: *)
(*   forall l1 l2 b, *)
(*     in_frames l1 b \/ in_frames l2 b <-> *)
(*     in_frames (l1 ++ l2) b. *)
(* Proof. *)
(*   intros. *)
(*   unfold in_frames, get_frames_blocks in *. *)
(*   rewrite map_app, concat_app, in_app; tauto. *)
(* Qed. *)

Lemma in_frame_info:
  forall b (f: frame_adt),
    in_frame f b ->
    exists fi,
      In (b,fi) (frame_adt_blocks f).
Proof.
  unfold in_frame, get_frame_blocks. intros b f.
  rewrite in_map_iff. intros ((bb & fi) & EQ & IN). simpl in *. subst.
  eauto.
Qed.

(** Fetching the frame information associated with a specific block. *)

Definition get_assoc_tframes (l: tframe_adt) (b: block) : option frame_info :=
  match fst l with
    Some fr =>
    if in_frame_dec fr b then
      get_assoc _ _ peq (frame_adt_blocks fr) b
    else None
  | _ => None
  end.

Fixpoint get_assoc_stack (l: stack) (b: block) : option frame_info :=
  match l with
    nil => None
  | lfr::r => if in_frames_dec lfr b then
              get_assoc_tframes lfr b
            else get_assoc_stack r b
  end.

Lemma not_in_stack_get_assoc:
  forall l b,
    ~ in_stack l b ->
    get_assoc_stack l b = None.
Proof.
  induction l; simpl; intros; eauto.
  rewrite in_stack_cons in H.
  repeat destr. eauto.
Qed.

Definition get_frame_info s : block -> option frame_info :=
  get_assoc_stack s.

(** * Injection of frame information  *)

Record inject_frame_info delta fi fi' :=
  {
    inject_perm: forall o, (0 <= o < frame_size fi)%Z -> stack_perm_le (frame_perm fi o) (frame_perm fi' (o + delta));
    inject_size:
      forall o, (0 <= o < frame_size fi -> 0 <= o + delta < frame_size fi')%Z;
  }.

Lemma inject_frame_info_id:
  forall f,
    inject_frame_info 0 f f.
Proof.
  constructor; auto.
  intros; rewrite Z.add_0_r. eapply stack_perm_le_refl; auto.
  intros; omega.
Qed.

Hint Resolve inject_frame_info_id.

Lemma inject_frame_info_trans:
  forall f1 f2 f3 delta1 delta2,
    inject_frame_info delta1 f1 f2 ->
    inject_frame_info delta2 f2 f3 ->
    inject_frame_info (delta1 + delta2) f1 f3.
Proof.
  intros f1 f2 f3 delta1 delta2 A B; inv A; inv B; constructor; eauto.
  - intros.
    eapply stack_perm_le_trans; eauto.
    rewrite Z.add_assoc. eauto.
  - intros.
    apply inject_size0 in H. apply inject_size1 in H. omega.
Qed.

Hint Resolve inject_frame_info_trans.

Lemma public_stack_shift:
  forall f1 f2 delta,
    inject_frame_info delta f1 f2 ->
    forall o,
      (0 <= o < frame_size f1)%Z ->
      frame_public f1 o ->
      frame_public f2 (o+delta).
Proof.
  unfold frame_public. intros.
  generalize (inject_perm _ _ _ H _ H0); eauto.
  rewrite H1.
  destruct (frame_perm f2); simpl; intuition.
Qed.

Lemma public_stack_range_shift:
  forall f1 f2 delta,
    inject_frame_info delta f1 f2 ->
    forall lo hi,
      (0 <= lo)%Z -> (hi <= frame_size f1)%Z ->
      public_stack_range lo hi f1 ->
      public_stack_range (lo+delta) (hi+delta) f2.
Proof.
  unfold public_stack_range; intros.
  replace ofs with (ofs-delta+delta)%Z by omega.
  eapply public_stack_shift; eauto. omega.
  apply H2; omega.
Qed.

(** * Injection of frame_adt  *)

Definition frame_inject (f: meminj) (f1 f2: frame_adt) :=
  Forall
    (fun bfi =>
       forall b2 delta,
         f (fst bfi) = Some (b2, delta) ->
         exists fi',
           In (b2, fi') (frame_adt_blocks f2) /\
           inject_frame_info delta (snd bfi) fi'
    )
    (frame_adt_blocks f1).

Lemma self_frame_inject f a:
  (forall b, f b = None \/ f b = Some (b,0)%Z) ->
  frame_inject f a a.
Proof.
  intros SELF.
  destruct a.
  apply Forall_forall; intros. destruct x. simpl in *.
  intros.
  destruct (SELF b); try congruence.
  rewrite H1 in H0; inv H0. eauto.
Qed.

Lemma frame_inject_id a:
  frame_inject inject_id a a.
Proof.
  apply self_frame_inject. right; reflexivity.
Qed.

Ltac injincrtac:=
  match goal with
    INCR: inject_incr ?f ?f',
          H: ?f' ?b = Some _,
             NEW: forall _ _ _, ?f _ = None -> ?f' _ = Some _ -> _ |- _ =>
    let b' := fresh "b'" in
    let delta := fresh "delta" in
    let FB := fresh "FB" in
    destruct (f b) as [[b' delta]|] eqn:FB;
    [ generalize (INCR _ _ _ FB); rewrite H;
      let A := fresh in intro A; inv A
    | generalize (NEW _ _ _ FB H)
    ]
  end.

Lemma frame_inject_incr:
  forall f f' f1 f2,
    inject_incr f f' ->
    (forall b b' delta,
        f b = None ->
        f' b = Some (b', delta) ->
        ~ in_frame f1 b) ->
    frame_inject f f1 f2 ->
    frame_inject f' f1 f2.
Proof.
  intros.
  unfold frame_inject in *.
  eapply Forall_impl; eauto.
  simpl. destruct f1. simpl.
  destruct a. simpl.
  intros IN ASSOC b2 delta F'B.
  injincrtac; autospe; eauto.
  intro NIN; contradict NIN.
  unfold in_frame, get_frame_blocks. simpl.
  rewrite in_map_iff. exists (b,f0); split; auto.
Qed.

Lemma frame_inject_in_frame:
  forall f v1 v2 b b' delta,
    frame_inject f v1 v2 ->
    in_frame v1 b ->
    f b = Some (b', delta) ->
    in_frame v2 b'.
Proof.
  unfold frame_inject. intros f v1 v2 b b' delta FI INF FB.
  rewrite Forall_forall in FI.
  red in INF. 
  setoid_rewrite in_map_iff in INF. destruct INF as ((b0 & f0) & EQ & IN). simpl in *; subst.
  specialize (FI _ IN). simpl in FI.
  specialize (FI _ _ FB).
  destruct FI as (fi' & ASSOC & SF).
  red. auto. apply in_map_iff. eexists; split; eauto. reflexivity.
Qed.

Lemma frame_inject_compose:
  forall (f f' : meminj) l1 l2
    (FI12: frame_inject f l1 l2)
    l3
    (FI23: frame_inject f' l2 l3),
    frame_inject (compose_meminj f f') l1 l3.
Proof.
  intros.
  unfold frame_inject in *.
  unfold compose_meminj.
  rewrite Forall_forall in *. intros (b1&fi1) IN b2 delta F.
  repeat destr_in F.
  specialize (FI12 _ IN _ _ Heqo).
  destruct FI12 as (fi2 & INL2 & IFI12).
  simpl in *. 
  specialize (FI23 _ INL2 _ _ Heqo0).
  destruct FI23 as (fi3 & INL3 & IFI23).
  eexists; split; eauto.
Qed.

Lemma in_frame_in_frames:
  forall f tf b,
    in_frame f b ->
    fst tf = Some f ->
    in_frames tf b.
Proof.
  unfold in_frames, get_frames_blocks.
  simpl. intros. rewrite H0. simpl. auto.
Qed.

Definition perm_type :=
  block -> Z -> perm_kind -> permission -> Prop.

(** * Consistency between permissions and frame size  *)

Definition frame_agree_perms (P: perm_type) (f: frame_adt) : Prop :=
  forall b fi o k p,
    In (b,fi) (frame_adt_blocks f) -> 
    P b o k p ->
    (0 <= o < frame_size fi)%Z.

Definition stack_agree_perms m (s: stack) :=
  forall tf,
    In tf s ->
    forall f,
      fst tf = Some f ->
      frame_agree_perms m f.

(** * Finding a frame at a given position  *)

Inductive frame_at_pos (s: stack) n f :=
| frame_at_pos_intro:
    nth_error s n = Some f -> frame_at_pos s n f.

Notation "f '@' s ':' i" := (frame_at_pos s i f) (at level 30, s at next level, i at next level, no associativity).

Lemma frame_at_pos_lt:
  forall s n f,
    f @ s : n ->
    n < length s.
Proof.
  intros s n f FAP; inv FAP.
  apply nth_error_Some. congruence.
Qed.

Lemma in_frame_at_pos:
  forall s f,
    In f s ->
    exists n, f @ s : n.
Proof.
  intros s f IN; apply In_nth_error in IN; destruct IN as (n & NTH).
  exists n; econstructor; eauto.
Qed.

Lemma frame_at_pos_In:
  forall s f n,
    f @ s : n ->
    In f s.
Proof.
  intros s f n FAP; inv FAP. eapply nth_error_In; eauto. 
Qed.

Lemma frame_at_same_pos:
  forall s n f1 f2,
    f1 @ s : n ->
    f2 @ s : n ->
    f1 = f2.
Proof.
  intros s n f1 f2 FAP1 FAP2; inv FAP1; inv FAP2; congruence.
Qed.

(** * Stack injection  *)

Definition frameinj := list nat.

Section TAKEDROP.
  Context {A: Type}.

  Fixpoint take (n: nat) (l: list A) : option (list A) :=
    match n with
    | O => Some nil
    | S m => match l with
            | h::t =>
               match take m t with
                 Some r => Some (h::r)
               | None => None
               end
            | _ => None
            end
    end.

  Fixpoint drop (n: nat) (l: list A) : list A :=
    match n with
    | O => l
    | S m => drop m (tl l)
    end.

  Lemma take_drop:
    forall n l t,
      take n l = Some t ->
      l = t ++ drop n l.
  Proof.
    induction n; simpl; intros; eauto. inv H. reflexivity.
    repeat destr_in H. simpl. f_equal. eauto.
  Qed.

  Lemma take_succeeds:
    forall n l,
      n <= length l ->
      exists t, take n l = Some t.
  Proof.
    induction n; simpl; intros; eauto.
    destr; simpl in *. omega.
    edestruct (IHn l0) as (t & EQ). omega.
    rewrite EQ. eauto.
  Qed.

  Lemma take_succeeds_inv:
    forall n l t,
      take n l = Some t ->
      n <= length l.
  Proof.
    induction n; simpl; intros; eauto. omega.
    repeat destr_in H.
    apply IHn in Heqo. simpl. omega.
  Qed.

  Lemma drop_length:
    forall n l,
      n <= length l ->
      length (drop n l) = length l - n.
  Proof.
    induction n; simpl; intros; eauto. omega.
    destruct l; simpl in *; try omega.
    rewrite IHn; omega.
  Qed.

  Lemma take_length:
    forall n l t,
      take n l = Some t ->
      length t = n.
  Proof.
    induction n; simpl; intros; eauto. inv H; auto.
    repeat destr_in H. simpl. erewrite IHn; eauto.
  Qed.

  Variable P: A -> Prop.

  Lemma take_forall:
    forall n l t,
      Forall P l ->
      take n l = Some t ->
      Forall P t.
  Proof.
    intros.
    rewrite (take_drop _ _ _ H0) in H.
    rewrite Forall_forall in H.
    rewrite Forall_forall. intros; apply H. rewrite in_app. auto.
  Qed.

  Lemma drop_forall:
    forall n l,
      Forall P l ->
      Forall P (drop n l).
  Proof.
    induction n; simpl; intros; eauto.
    apply IHn. inv H; simpl; auto.
  Qed.

End TAKEDROP.

Definition sum_list (l: list nat) : nat :=
  fold_right Peano.plus O l.

Fixpoint compose_frameinj (g g': frameinj): option frameinj :=
  match g' with
  | nil => Some nil
  | n::g' => match take n g with
            | Some t =>
              match compose_frameinj (drop n g) g' with
                Some r => Some (sum_list t :: r)
              | None => None
              end
            | None => None
            end
  end.

Lemma compose_frameinj_succeeds:
  forall g2 g1,
    sum_list g2 = length g1 ->
    exists g3, compose_frameinj g1 g2 = Some g3.
Proof.
  induction g2; simpl; intros; eauto.
  edestruct (take_succeeds a g1) as (t & EQ). omega. rewrite EQ.
  edestruct IHg2 as (g3 & EQ'). 2: rewrite EQ'.
  rewrite drop_length; omega. eauto.
Qed.

(** * Monotonicity of frame injections  *)

Definition flat_frameinj thr : frameinj := list_repeat thr 1.

Definition get_stack_top_blocks (s: stack) : list block :=
  match s with
    nil => nil
  | tf::r => get_frames_blocks tf
  end.

Definition is_stack_top s (b: block) :=
  In b (get_stack_top_blocks s).

Lemma stack_top_frame_at_position:
  forall s b,
    is_stack_top s b ->
    exists f, f @ s : 0 /\ in_frames f b.
Proof.
  destruct s; simpl; intros. easy.
  red in H. simpl in H.
  exists t; split.
  econstructor. simpl. auto.
  auto.
Qed.

Lemma frame_at_position_stack_top:
  forall s f b,
    f @ s : O ->
    in_frames f b ->
    is_stack_top s b.
Proof.
  destruct s; simpl; intros. inv H. simpl in H1. congruence.
  inv H. simpl in H1.
  inv H1. simpl; auto.
Qed.

Lemma is_stack_top_in_stack:
  forall s b,
    is_stack_top s b -> in_stack s b.
Proof.
  intros s b IS.
  destruct s; simpl in *. easy. red in IS; simpl in IS.
  rewrite in_stack_cons; left. eauto.
Qed.

(** * Surjectivity of stack injections  *)

(* Definition frameinj_surjective (g: frameinj) n2 := *)
(*   sum_list g = n2. *)

Class InjectPerm :=
  {
    inject_perm_condition: permission -> Prop;
    inject_perm_condition_writable: forall p, perm_order Writable p -> inject_perm_condition p;
  }.

(** * Specifying tailcalled frames.  *)
(** A tframe is a non-empty list of frames (a::l). It must be the case that all
    blocks in l have no permission.
 *)

Definition wf_tframe (m: perm_type) (* (j: meminj) *) (tf: tframe_adt) : Prop :=
  forall b,
    forall f,
      In f (snd tf) ->
      in_frame f b ->
      forall o k p,
        ~ m b o k p.

Definition wf_stack (m: perm_type) (s: stack) : Prop :=
  Forall (wf_tframe m) s.

Section INJ.
  Context {injperm: InjectPerm}.

   Definition has_perm (m: perm_type) (j: meminj) (f: tframe_adt) : Prop :=
     exists b o k p, j b <> None /\ in_frames f b /\ m b o k p /\ inject_perm_condition p.

   Definition has_perm_frame (m: perm_type) (j: meminj) (f: frame_adt) : Prop :=
     exists b o k p, j b <> None /\ in_frame f b /\ m b o k p /\ inject_perm_condition p.

   Definition tframe_inject (f: meminj) (P: perm_type) (tf1 tf2: tframe_adt): Prop :=
     forall f1,
       fst tf1 = Some f1 ->
       has_perm_frame P f f1 ->
       exists f2, fst tf2 = Some f2 /\ frame_inject f f1 f2.

   Lemma self_tframe_inject f P a:
     (forall b, f b = None \/ f b = Some (b,0)%Z) ->
     tframe_inject f P a a.
   Proof.
     intros SELF.
     red; intros. exists f1; split; auto.
     apply self_frame_inject; auto.
   Qed.

   Lemma tframe_inject_id P a:
     tframe_inject inject_id P a a.
   Proof.
     apply self_tframe_inject. right; reflexivity.
   Qed.

   Lemma tframe_inject_incr:
     forall P f f' f1 f2,
       inject_incr f f' ->
       (forall b b' delta,
           f b = None ->
           f' b = Some (b', delta) ->
           ~ in_frames f1 b) ->
       tframe_inject f P f1 f2 ->
       tframe_inject f' P f1 f2.
   Proof.
     intros P f f' f1 f2 INCR NEW TF ff1 IN1 (b & o & k & p & Fnone & IFR & PERM & IPC).
     edestruct TF as (f0 & IN & FI); eauto.
     - red.
       repeat eexists; eauto.
       destruct (f' b) eqn:?; try congruence. destruct p0.
       intro. eapply NEW in Heqo0; eauto. exfalso; apply Heqo0.
       eapply in_frame_in_frames; eauto.
     - eexists; split; eauto.
       eapply frame_inject_incr; eauto.
       intros b0 b' delta NONE SOME IFR0; eapply NEW; eauto.
       eapply in_frame_in_frames; eauto.
   Qed.

   Lemma tframe_inject_compose:
     forall (f f' : meminj) P P' l1 l2
       (FI12: tframe_inject f P l1 l2)
       l3
       (FI23: tframe_inject f' P' l2 l3)
       (PERMS: forall b1 b2 delta o k p,
           f b1 = Some (b2, delta) ->
           P b1 o k p ->
           inject_perm_condition p ->
           P' b2 (o + delta)%Z k p),
       tframe_inject (compose_meminj f f') P l1 l3.
   Proof.
     intros f f' P P' l1 l2 FI12 l3 FI23 PERMS
            f1 INf1 (b & o & k & p & JB & IFR & PERM & IPC).
     unfold compose_meminj in JB; repeat destr_in JB. subst.
     edestruct FI12 as (f2 & INl2 & FI12'); eauto.
     repeat eexists; eauto. congruence.
     edestruct FI23 as (f3 & INl3 & FI23'); eauto.
     repeat eexists; eauto. congruence.
     eapply frame_inject_in_frame; eauto.
     eexists; split; eauto.
     eapply frame_inject_compose; eauto.
   Qed.

   Inductive stack_inject_aux (f: meminj) (m: perm_type) : frameinj -> stack -> stack -> Prop :=
   | stack_inject_aux_intro:
       stack_inject_aux f m nil nil nil
   | stack_inject_aux_cons
       n g s1 hs1 ts1 tf ts2
       (TAKE: take (S n) s1 = Some hs1)
       (DROP: drop (S n) s1 = ts1)
       (SIA_REC: stack_inject_aux f m g ts1 ts2)
       (FI: Forall (fun f1 => tframe_inject f m f1 tf) hs1):
     stack_inject_aux f m (S n::g) s1 (tf::ts2).

   Lemma stack_inject_aux_length_l:
     forall f m g s1 s2,
       stack_inject_aux f m g s1 s2 ->
       sum_list g = length s1.
   Proof.
     induction 1; simpl; intros; eauto.
     rewrite (take_drop _ _ _ TAKE). subst.
     rewrite IHstack_inject_aux. rewrite app_length.
     f_equal. symmetry.
     erewrite take_length by eauto. omega.
   Qed.

   Lemma stack_inject_aux_length_r:
     forall f m g s1 s2,
       stack_inject_aux f m g s1 s2 ->
       length g = length s2.
   Proof.
     induction 1; simpl; intros; eauto.
   Qed.

   Record stack_inject (f: meminj) (g: frameinj) (m: perm_type) (s1 s2: stack) :=
    {
      (* stack_src_wf: wf_stack m s1; *)
      stack_inject_frame_inject: stack_inject_aux f m g s1 s2;
      stack_inject_not_in_source:
        forall b1 b2 delta bi2
          (FB: f b1 = Some (b2, delta))
          (NIS: ~ in_stack s1 b1)
          (FI: in_stack' s2 (b2,bi2))
          o k p
          (PERM: m b1 o k p)
          (IPC: inject_perm_condition p),
          frame_public bi2 (o + delta);
    }.

  Lemma concat_In:
    forall {A} (l: list (list A)) b,
      In b (concat l) <->
      exists x, In b x /\ In x l.
  Proof.
    induction l; simpl; intros; eauto.
    split. easy. intros (x & AA & B); auto.
    rewrite in_app, IHl.
    split.
    intros [B|(x & B & C)]; eauto.
    intros (x & B & [C|C]); subst; eauto.
  Qed.

  Lemma in_stack'_app:
    forall s1 s2 b,
      in_stack' (s1 ++ s2) b <-> in_stack' s1 b \/ in_stack' s2 b.
  Proof.
    induction s1; simpl; intros; eauto.
    tauto.
    rewrite IHs1. tauto.
  Qed.

  Lemma in_frame'_in_frame:
    forall b1 bi1 fr1,
      in_frame' fr1 (b1, bi1) -> in_frame fr1 b1.
  Proof.
    intros. red in H. eapply in_map with (f:= fst) in H. auto.
  Qed.

  Lemma wf_stack_drop:
    forall P n s,
      wf_stack P s ->
      wf_stack P (drop n s).
  Proof.
    induction n; simpl; intros; eauto.
    apply IHn.
    inv H; simpl. constructor. auto.
  Qed.

  Lemma stack_inject_compat:
    forall f g P s1 s2,
      stack_inject f g P s1 s2 ->
    forall b1 b2 delta bi1,
      f b1 = Some (b2, delta) ->
      in_stack' s1 (b1, bi1) ->
      (exists o k p, P b1 o k p /\ inject_perm_condition p) ->
      exists bi2,
        in_stack' s2 (b2, bi2) /\ inject_frame_info delta bi1 bi2.
  Proof.
    intros f g P s1 s2 SI.
    inv SI.
    revert stack_inject_frame_inject0 .
    clear stack_inject_not_in_source0.
    induction 1; simpl; intros b1 b2 delta bi1 FB INS PERM.
    - easy.
    - subst.
      destruct PERM as (o & k & p & PERM & IPC).
      rewrite (take_drop _ _ _ TAKE) in INS.
      rewrite in_stack'_app in INS.
      destruct INS as [INS|INS].
      + rewrite in_stack'_rew in INS.
        destruct INS as (tf1 & INFRS & INS).
        rewrite Forall_forall in FI. specialize (FI _ INS).
        red in FI.
        rewrite in_frames'_rew in INFRS. destruct INFRS as (fr & INFR & INFRS).
        specialize (FI _ INFRS).
        trim FI. red. exists b1, o, k, p; repeat apply conj; auto. congruence.
        eapply in_frame'_in_frame; eauto.
        destruct FI as (f2 & INTF & FI).
        red in FI. rewrite Forall_forall in FI.
        specialize (FI _ INFR). simpl in FI.
        specialize (FI _ _ FB).
        destruct FI as (bi2 & INfr2 & IFI).
        exists bi2; split; auto. left; rewrite in_frames'_rew.
        eexists; split; eauto.
      + edestruct IHstack_inject_frame_inject0 as (bi2 & INS2 & IFI); eauto.
  Qed.

  Lemma stack_top_in_frames:
    forall s b,
      is_stack_top s b ->
      exists f,
        in_frames f b /\ In f s.
  Proof.
    unfold is_stack_top; destruct s; simpl; intros. easy.
    exists t; split; auto.
  Qed.

  Lemma in_frames_in_stack:
    forall s f b,
      In f s ->
      in_frames f b ->
      in_stack s b.
  Proof.
    induction s; simpl; intros; eauto.
    rewrite in_stack_cons.
    destruct H. subst. auto.
    eapply IHs in H; eauto.
  Qed.

  Lemma tframe_inject_in_frames:
    forall f m v1 v2 b b' delta o k p,
      tframe_inject f m v1 v2 -> m b o k p -> inject_perm_condition p -> in_frames v1 b -> f b = Some (b', delta) -> in_frames v2 b'.
  Proof.
    intros f m v1 v2 b b' delta o k p TFI PERM IPC IFR FB.
    red in IFR. unfold get_opt_frame_blocks in IFR.
    destr_in IFR; try easy. unfold get_frame_blocks in IFR.
    rewrite in_map_iff in IFR. destruct IFR as (fa & blocks & IN). subst.
    specialize (TFI _ Heqo0).
    trim TFI.
    repeat eexists; eauto. congruence. red. unfold get_frame_blocks.
    apply in_map. auto.
    destruct TFI as (f2 & IN2 & FI12).
    eapply in_frame_in_frames; eauto.
    eapply frame_inject_in_frame; eauto.
    red. apply in_map. auto.
  Qed.

  Lemma stack_inject_is_stack_top:
    forall f g m s1 s2,
      stack_inject f g m s1 s2 ->
      forall b1 b2 delta,
        f b1 = Some (b2, delta) ->
        (exists o k p, m b1 o k p /\ inject_perm_condition p) ->
        is_stack_top s1 b1 ->
        is_stack_top s2 b2.
  Proof.
    intros f g m s1 s2 SI b1 b2 delta FB PERM IST.
    destruct (stack_top_frame_at_position _ _ IST) as (ff & FAP1 & IFR1).
    destruct s1. inv FAP1. simpl in *. congruence.
    inv SI. inv stack_inject_frame_inject0.
    eapply frame_at_position_stack_top; eauto.
    constructor. reflexivity.
    inv FAP1. inv H.
    simpl in TAKE. destr_in TAKE. inv TAKE. inv FI.
    destruct PERM as (o & k & p & PERM & IPC).
    eapply tframe_inject_in_frames; eauto.
  Qed.

  Lemma in_stack_in_frames_ex:
    forall s b,
      in_stack s b ->
      exists f, In f s /\ in_frames f b.
  Proof.
    induction s; simpl; intros; eauto. easy.
    rewrite in_stack_cons in H. destruct H.
    exists a; eauto.
    edestruct IHs as (x & A & B); eauto.
  Qed.

  Lemma frame_at_pos_ex:
    forall i s,
      i < length s ->
      exists f,
        f @ s : i.
  Proof.
    intros.
    rewrite <- nth_error_Some in H.
    destruct (nth_error s i) eqn:?; try congruence.
    repeat econstructor; eauto.
  Qed.

  Inductive nodup: stack -> Prop :=
  | nodup_nil:
      nodup nil
  | nodup_cons:
      forall f s,
        nodup s ->
        (forall b, in_frames f b -> ~ in_stack s b) ->
        nodup (f::s).

  Definition nodup' (s: stack) :=
    forall b f1 f2,
      In f1 s ->
      In f2 s ->
      in_frames f1 b ->
      in_frames f2 b ->
      f1 = f2.

  Lemma nodup_nodup': forall l, nodup l -> nodup' l.
  Proof.
    induction l; simpl; intros; eauto.
    red; intros; easy.
    red; intros.
    simpl in *.
    destruct H0.
    - destruct H1. congruence.
      subst.
      inv H.
      exfalso; eapply H6. eauto. eapply in_frames_in_stack. eauto. eauto.
    - destruct H1. 
      subst.
      inv H.
      exfalso; eapply H6. eauto. eapply in_frames_in_stack; eauto.
      inv H. eapply IHl; eauto.
  Qed.

  (* Inductive nodupt: tframe_adt -> Prop := *)
  (* | nodupt_nil: nodupt nil *)
  (* | nodupt_cons: forall f s, nodupt s -> (forall b, in_frame f b -> ~ in_frames s b) -> nodupt (f::s). *)

  (* Definition nodupt (s: tframe_adt) := *)
  (*   forall b f1 f2, *)
  (*     In f1 s -> *)
  (*     In f2 s -> *)
  (*     in_frame f1 b -> *)
  (*     in_frame f2 b -> *)
  (*     f1 = f2. *)


  (* Lemma nodupt_nodupt': forall l, nodupt l -> nodupt' l. *)
  (* Proof. *)
  (*   induction 1; simpl; intros; eauto. *)
  (*   - unfold nodupt'. easy. *)
  (*   - intros b f1 f2 [EQ1|AIN1] [EQ2|AIN2] IFR1 IFR2; subst; simpl in *; auto. *)
  (*     + eapply H0 in IFR1. elim IFR1. *)
  (*       unfold in_frames, get_frames_blocks. *)
  (*       apply concat_In. *)
  (*       eexists; split. apply IFR2. *)
  (*       apply in_map. simpl. auto. *)
  (*     + eapply H0 in IFR2. elim IFR2. *)
  (*       unfold in_frames, get_frames_blocks. *)
  (*       apply concat_In. *)
  (*       eexists; split. apply IFR1. *)
  (*       apply in_map. simpl. auto. *)
  (*     + eapply IHnodupt; eauto. *)
  (* Qed. *)

  Lemma in_frames_in_frame_ex:
    forall tf b,
      in_frames tf b ->
      exists f,
        fst tf = Some f /\ in_frame f b.
  Proof.
    intros; rewrite <- in_frames_cons. erewrite <- surjective_pairing; eauto.
  Qed.

  Lemma get_assoc_tframes_in :
    forall l b r,
      get_assoc_tframes l b = Some r ->
      exists f,
        fst l = Some f /\ In (b,r) (frame_adt_blocks f).
  Proof.
    destruct l; simpl. destruct o; simpl; try easy.
    cbn. intros b r. destr. intro H; eapply get_assoc_in in H.
    eauto.
  Qed.

  Lemma get_assoc_stack_In:
    forall s b fi,
      get_assoc_stack s b = Some fi ->
      exists f tf, fst tf = Some f /\ In (b,fi) (frame_adt_blocks f) /\ In tf s.
  Proof.
    induction s; simpl; intros; eauto.
    congruence.
    destr_in H.
    - apply get_assoc_tframes_in in H.
      destruct H as (f & IN1 & IN2). exists f, a; split; eauto.
    - edestruct IHs as (f & tf & AIN & IN1 & IN2); eauto.
      exists f, tf; split; eauto.
  Qed.

  Lemma in_frame_blocks_in_frame:
    forall b fi fr
      (IN : In (b, fi) (frame_adt_blocks fr)),
      in_frame fr b.
  Proof.
    intros; setoid_rewrite in_map_iff; eexists; split; eauto. reflexivity.
  Qed.

  Lemma in_get_assoc_tframes:
    forall tf f b fi
      (NTH : fst tf = Some f)
      (IN : In (b, fi) (frame_adt_blocks f)),
      get_assoc_tframes tf b = Some fi.
  Proof.
    intros. unfold get_assoc_tframes.
    rewrite NTH.
    rewrite pred_dec_true.
    apply in_lnr_get_assoc. destruct f; auto. auto.
    eapply in_frame_blocks_in_frame; eauto.
  Qed.

  Lemma get_assoc_stack_lnr:
    forall s b tf fi f
      (NTH: fst tf = Some f)
      (IN: In (b,fi) (frame_adt_blocks f))
      (ND: nodup s)
      (INS: In tf s),
      get_assoc_stack s b = Some fi.
  Proof.
    induction s; simpl; intros; eauto.
    easy.
    destruct INS; subst.
    - rewrite pred_dec_true.
      eapply in_get_assoc_tframes; eauto.
      eapply in_frame_in_frames; eauto.
      eapply in_frame_blocks_in_frame; eauto.
    - rewrite pred_dec_false.
      eapply IHs; eauto.
      inv ND; auto.
      intro IFR; inv ND.
      apply H3 in IFR.
      apply IFR.
      eapply in_frames_in_stack; eauto.
      eapply in_frame_in_frames; eauto.
      eapply in_frame_blocks_in_frame; eauto.
  Qed.

  Lemma wf_stack_in_frames_in_frame:
    forall s,
      forall f1 b,
        In f1 s ->
        in_frames f1 b ->
        exists vf1,
          fst f1 = Some vf1 /\
          in_frame vf1 b.
  Proof.
    intros s f1 b INS INF.
    destruct f1. destruct o; try easy. cbn in INF.
    eexists; split. reflexivity.
    auto.
  Qed.

  Lemma nodup_block_info:
    forall b bi1 bi2 f,
      In (b,bi1) (frame_adt_blocks f) ->
      In (b,bi2) (frame_adt_blocks f) ->
      bi1 = bi2.
  Proof.
    intros.
    destruct f. simpl in *.
    revert frame_adt_blocks_norepet0 H H0.
    generalize frame_adt_blocks0 as l.
    clear.
    induction l; simpl; intros LNR IN1 IN2; eauto.
    easy.
    inv LNR; trim IHl; eauto.
    destruct IN1,IN2; subst; auto.
    congruence.
    simpl in *.
    elim H1. apply in_map_iff; eexists; split; eauto. reflexivity.
    simpl in *.
    elim H1. apply in_map_iff; eexists; split; eauto. reflexivity.
  Qed.

  Lemma in_stack'_stack_agree_perms:
    forall m2 l2 b2 bi2,
      in_stack' l2 (b2, bi2) ->
      stack_agree_perms m2 l2 ->
      forall o k p, m2 b2 o k p -> (0 <= o < frame_size bi2)%Z.
  Proof.
    intros.
    rewrite in_stack'_rew in H.
    destruct H as (tf & IFR & IN).
    rewrite in_frames'_rew in IFR.
    destruct IFR as (fr & IFR & INTF).
    eapply H0; eauto.
  Qed.

  Lemma in_frame'_norepet:
    forall b bi1 bi2 f,
      in_frame' f (b, bi1) ->
      in_frame' f (b, bi2) ->
      bi1 = bi2.
  Proof.
    unfold in_frame'.
    intros b bi1 bi2 f.
    destruct f. simpl in *.
    revert frame_adt_blocks_norepet0.
    generalize frame_adt_blocks0 as l. clear.
    induction l; simpl; intros; eauto. easy.
    inv frame_adt_blocks_norepet0.
    trim IHl; auto.
    intuition subst; simpl in *.
    congruence.
    exfalso; apply H3. eapply in_map in H. exact H.
    exfalso; apply H3. eapply in_map in H1. exact H1.
  Qed.

  Lemma in_frames'_in_frames:
    forall fr b bi,
      in_frames' fr (b, bi) ->
      in_frames fr b.
  Proof.
    unfold in_frames', in_frames. intros fr b bi EQ. destr_in EQ.
    simpl.
    eapply in_frame'_in_frame; eauto.
  Qed.


  Lemma in_stack'_in_stack:
    forall fr b bi,
      in_stack' fr (b, bi) ->
      in_stack fr b.
  Proof.
    induction fr; simpl; intros; eauto.
    rewrite in_stack_cons. destruct H; eauto using in_frames'_in_frames.
  Qed.

  Lemma in_stack'_norepet:
    forall s
      (ND: nodup s)
      b bi1 bi2,
      in_stack' s (b, bi1) ->
      in_stack' s (b, bi2) ->
      bi1 = bi2.
  Proof.
    induction 1; simpl; intros b bi1 bi2 INS1 INS2; eauto. easy.
    destruct INS1 as [INS1 | INS1], INS2 as [INS2 | INS2]; eauto.
    + rewrite in_frames'_rew in INS1, INS2.
      destruct INS1 as (fr1 & INfr1 & INS1).
      destruct INS2 as (fr2 & INfr2 & INS2).
      assert (fr1 = fr2) by congruence; subst.
      eapply in_frame'_norepet; eauto.
    + edestruct H; eauto using in_frames'_in_frames, in_stack'_in_stack.
    + edestruct H; eauto using in_frames'_in_frames, in_stack'_in_stack.
  Qed.

  Lemma stack_inject_inject_frame_info:
    forall f g m l1 l2,
      stack_inject f g m l1 l2 ->
      nodup l1 ->
      nodup l2 ->
      forall b1 bi1 b2 bi2,
        in_stack' l1 (b1, bi1) ->
        in_stack' l2 (b2, bi2) ->
        forall delta, 
          f b1 = Some (b2, delta) ->
          forall o k p,
            m b1 o k p ->
            inject_perm_condition p ->
        inject_frame_info delta bi1 bi2.
  Proof.
    intros f g m l1 l2 SI ND1 ND2 b1 bi1 b2 bi2 INS1 INS2 delta FB o k p PERM IPC.
    edestruct (stack_inject_compat _ _ _ _ _ SI _ _ _ _ FB INS1) as (bi2' & INS2' & IFI).
    do 3 eexists; split; eauto.
    cut (bi2 = bi2'). intro; subst; auto.
    eapply in_stack'_norepet; eauto.
  Qed.

  Lemma take_sumlist:
    forall n l1 l2,
      take n l1 = Some l2 ->
      sum_list l2 <= sum_list l1.
  Proof.
    induction n; simpl; intros; eauto. inv H. simpl. omega.
    repeat destr_in H. 
    apply IHn in Heqo.
    simpl in *. omega.
  Qed.

  Lemma drop_tl:
    forall {A} n (l: list A),
      tl (drop n l) = drop n (tl l).
  Proof.
    induction n; simpl; intros; eauto.
  Qed.

  Lemma drop_drop:
    forall {A} n1 n2 (l: list A),
      drop n1 (drop n2 l) = drop (n1 + n2) l.
  Proof.
    induction n1; simpl; intros; eauto.
    rewrite <- IHn1. rewrite drop_tl. auto.
  Qed.

  Lemma stack_inject_drop:
    forall f m1 g1 l1 l2
      (SI : stack_inject_aux f m1 g1 l1 l2)
      n (POS: O < n) l (TAKE : take n g1 = Some l),
      stack_inject_aux f m1 (drop n g1) (drop (sum_list l) l1) (drop n l2).
  Proof.
    induction 1; simpl; intros; eauto.
    - destruct n; simpl in *; inv TAKE. simpl. constructor.
    - subst.
      destruct n0; simpl in *. omega. repeat destr_in TAKE0. simpl.
      destruct (lt_dec O n0).
      rewrite plus_comm. rewrite <- drop_drop. eapply IHSI; eauto.
      assert (n0 = O) by omega. subst.
      simpl in *. inv Heqo. simpl. rewrite Nat.add_0_r. auto.
  Qed.

  Lemma take_smaller:
    forall {A} a b (l: list A) l1 l2,
      take (a + b) l = Some l1 ->
      take a l = Some l2 ->
      take a l1 = Some l2.
  Proof.
    induction a; simpl; intros; eauto.
    repeat destr_in H. repeat destr_in H0.
    erewrite IHa; eauto.
  Qed.

  Lemma take_drop_rest:
    forall {A} a b (l: list A) l1,
      take (a + b) l = Some l1 ->
      take b (drop a l) = Some (drop a l1).
  Proof.
    induction a; simpl; intros; eauto.
    repeat destr_in H. simpl. eauto.
  Qed.

  Lemma stack_inject_aux_take:
    forall n
      f m g s1 s2
      (SIA: stack_inject_aux f m g s1 s2)
      g' s1' s2'
      (TG: take n g = Some g')
      (TS1: take (sum_list g') s1 = Some s1')
      (TS2: take n s2 = Some s2'),
      stack_inject_aux f m g' s1' s2'.
  Proof.
    induction n; simpl; intros.
    - inv TG; inv TS2. simpl in *. inv TS1. constructor.
    - repeat destr_in TG. repeat destr_in TS2. inv SIA.
      econstructor; eauto.
      eapply take_smaller; eauto.
      eapply IHn; eauto.
      eapply take_drop_rest; eauto.
  Qed.

  Lemma stack_inject_aux_tframe_inject:
    forall f m g s1 s2 x,
      stack_inject_aux f m g s1 s2 ->
      In x s1 ->
      exists y, In y s2 /\ tframe_inject f m x y.
  Proof.
    induction 1; simpl; intros; eauto. easy.
    subst.
    rewrite (take_drop _ _ _ TAKE) in H0. rewrite in_app in H0.
    destruct H0.
    rewrite Forall_forall in FI. apply FI in H0. eauto.
    destruct IHstack_inject_aux as (y & INs2 & TFI). auto.
    eauto.
  Qed.

  Opaque take drop.

  Lemma stack_inject_aux_compose:
    forall f f' m1 m2 g1 g2 s1 s2 s3 g3
      (COMP : compose_frameinj g1 g2 = Some g3)
      (SI12 : stack_inject_aux f m1 g1 s1 s2)
      (SI23 : stack_inject_aux f' m2 g2 s2 s3)
      (PERMS: forall b1 b2 delta o k p,
          f b1 = Some (b2, delta) ->
          m1 b1 o k p ->
          inject_perm_condition p ->
          m2 b2 (o + delta)%Z k p),
      stack_inject_aux (compose_meminj f f') m1 g3 s1 s3.
  Proof.
    intros.
    revert f' m2 g2 s2 s3 SI23 f m1 g1 s1 SI12 g3 COMP PERMS.
    induction 1; intros; eauto.
    - inv COMP. inv SI12. constructor.
    - repeat destr_in COMP.
      repeat destr_in H0. repeat destr_in Heqo. simpl in *.
      destruct (take_succeeds (sum_list l) s0) as (t & EQ).
      erewrite <- stack_inject_aux_length_l by eauto.
      eapply take_sumlist; eauto.
      cut (exists sl, sum_list l = S sl). intros (sl & SL). rewrite SL in *.
      econstructor; eauto.
      eapply IHSI23; eauto. 
      rewrite <- SL.
      eapply stack_inject_drop; eauto. omega.
      rewrite Forall_forall in FI |- *. intros.
      exploit stack_inject_aux_take. apply SI12. eauto. rewrite SL; eauto. eauto. 
      intro SIA.
      edestruct (stack_inject_aux_tframe_inject _ _ _ _ _ x SIA) as (y & INhs1 & TFI). auto.
      eapply tframe_inject_compose; eauto.
      Transparent take drop.
      inv SI12; simpl in *. congruence.
      repeat destr_in H0. simpl. eauto.
  Qed.

  Lemma stack_inject_compose:
    forall (f f' : meminj) g g' m1 l1 l2,
      stack_inject f g m1 l1 l2 ->
      forall m2 l3,
        stack_inject f' g' m2 l2 l3 ->
        nodup l2 ->
        nodup l3 ->
        (forall b1 b2 delta o k p,
            f b1 = Some (b2, delta) ->
            m1 b1 o k p ->
            inject_perm_condition p ->
            m2 b2 (o + delta)%Z k p) ->
        stack_agree_perms m2 l2 ->
        forall g3,
        (compose_frameinj g g') = Some g3 ->
        stack_inject (compose_meminj f f') g3 m1 l1 l3.
  Proof.
    intros f f' g g' m1 l1 l2 SI1 m2 l3 SI2 ND2 ND3 PERM FAP g3 COMP.
    inversion SI1; inversion SI2.
    split; auto.
    - eapply stack_inject_aux_compose; eauto.
    - intros b1 b3 delta bi3 CINJ NIS1 INS3 o k p PERMS IPC.
      unfold compose_meminj in CINJ.
      destruct (f b1) as [[b2 delta1]|] eqn:FB1; try congruence.
      destruct (f' b2) as [[b33 delta2]|] eqn:FB2; try congruence.
      inv CINJ.
      destruct (in_stack_dec l2 b2).
      +
        assert (INS2: exists bi2, in_stack' l2 (b2,bi2)).
        {
          destruct (in_stack_in_frames_ex _ _ i) as (f2 & INS2 & INF2).
          setoid_rewrite in_stack'_rew.
          edestruct in_frames_in_frame_ex as (f2' & INS2' & INF2'). apply INF2.
          edestruct in_frame_info as (bi2 & IFR2). apply INF2'.
          setoid_rewrite in_frames'_rew.
          exists bi2, f2. split; auto.
          exists f2'; split; auto.
        }
        destruct INS2 as (bi2 & INS2).
        exploit stack_inject_not_in_source0. eauto. eauto. eauto. eauto. auto.
        intro PUB2.
        exploit PERM; eauto. intro PERMS2.
        rewrite Z.add_assoc. eapply public_stack_shift; eauto.
        2: eapply in_stack'_stack_agree_perms; eauto.
        eapply stack_inject_inject_frame_info; eauto.
      + rewrite Z.add_assoc. eapply stack_inject_not_in_source1; eauto.
  Qed.

  Definition public_stack_access l (b: block) (lo hi: Z) : Prop :=
    match get_frame_info l b with
      Some fi => public_stack_range lo hi fi
    | None => True
    end.

  Lemma lo_ge_hi_public_stack_access:
    forall m b lo hi,
      (lo >= hi)%Z ->
      public_stack_access m b lo hi.
  Proof.
    red. intros.
    destruct (get_frame_info m b); try tauto.
    red; intros. omega.
  Qed.

  Definition stack_access (m: stack) (b: block) (lo hi: Z) : Prop :=
    is_stack_top m b \/ public_stack_access m b lo hi.

  Lemma is_stack_top_dec : forall m b,
      {is_stack_top m b} + {~is_stack_top m b}.
  Proof.
    intros. unfold is_stack_top. apply in_dec. 
    apply eq_block.
  Qed.

  Lemma lo_ge_hi_stack_access:
    forall m b lo hi,
      (lo >= hi)%Z ->
      stack_access m b lo hi.
  Proof.
    unfold stack_access.
    intros.
    destruct (is_stack_top_dec m b);[left|right]. auto.
    eapply lo_ge_hi_public_stack_access. auto.
  Qed.


  Lemma is_stack_top_stack_blocks:
    forall m b,
      is_stack_top m b <-> (exists f r, in_frames f b /\ m = f::r).
  Proof.
    unfold is_stack_top, get_stack_top_blocks.
    intros.
    destruct m eqn:?; intuition.
    - decompose [ex and] H; intuition congruence.
    - repeat eexists. eauto.
    - subst.    
      decompose [ex and] H; intuition. inv H2.
      eauto. 
  Qed.

  Lemma in_stack_data_inside:
    forall fi lo hi lo' hi',
      public_stack_range lo hi fi ->
      (lo <= lo')%Z ->
      (hi' <= hi)%Z ->
      public_stack_range lo' hi' fi.
  Proof.
    intros fi lo hi lo' hi' NPSA LO HI.
    do 2 red in NPSA |- *.
    intros; apply NPSA. omega.
  Qed.

  Lemma public_stack_access_inside:
    forall m b lo hi lo' hi',
      public_stack_access m b lo hi ->
      (lo <= lo')%Z ->
      (hi' <= hi)%Z ->
      public_stack_access m b lo' hi'.
  Proof.
    intros m b lo hi lo' hi' NPSA LO HI.
    unfold public_stack_access in *.
    destruct (get_frame_info m b); auto.
    eapply in_stack_data_inside in NPSA; eauto.
  Qed.

  Lemma stack_access_inside:
    forall m b lo hi lo' hi',
      stack_access m b lo hi ->
      (lo <= lo')%Z ->
      (hi' <= hi)%Z ->
      stack_access m b lo' hi'.
  Proof.
    intros m b lo hi lo' hi' NPSA LO HI.
    unfold stack_access in *.
    destruct NPSA; auto. right.
    eapply public_stack_access_inside; eauto.
  Qed.

  Lemma public_stack_range_dec : forall lo hi f,
      {public_stack_range lo hi f} + {~public_stack_range lo hi f}.
  Proof.
    unfold public_stack_range. intros. 
    edestruct (Intv.forall_rec (frame_public f) (fun ofs => ~ frame_public f ofs)) with (lo:=lo) (hi:=hi).
    - apply frame_public_dec. 
    - auto.
    - right. intro A.
      destruct e as (x & IN & NIN).
      apply NIN. apply A. auto.
  Qed.

  Lemma public_stack_access_dec : forall m b lo hi,
      {public_stack_access m b lo hi} + 
      {~public_stack_access m b lo hi}.
  Proof.
    unfold public_stack_access.
    intros.
    destruct (get_frame_info m b); auto.
    apply public_stack_range_dec.
  Qed.

  Lemma stack_access_dec : forall m b lo hi,
      {stack_access m b lo hi} + 
      {~stack_access m b lo hi}.
  Proof.
    intros. unfold stack_access.
    destruct (is_stack_top_dec m b); auto.
    destruct (public_stack_access_dec m b lo hi); auto.
    right; intuition.
  Qed.


  Lemma not_in_frames_no_frame_info:
    forall (m : tframe_adt) (b : block), ~ in_frames m b -> get_assoc_tframes m b = None.
  Proof.
    intros.
    destruct (get_assoc_tframes m b) eqn:GAT; auto.
    apply get_assoc_tframes_in in GAT.
    destruct GAT as (f0 & IN1 & IN2).
    exfalso; apply H.
    eapply in_frame_in_frames; eauto.
    eapply in_frame_blocks_in_frame; eauto.
  Qed.

  Lemma get_frame_info_in_frames:
    forall m b f, get_assoc_tframes m b = Some f -> in_frames m b.
  Proof.
    intros.
    destruct (in_frames_dec m b); auto.
    rewrite not_in_frames_no_frame_info in H; auto. congruence.
  Qed.

  Lemma get_frame_info_in_stack:
    forall m b f, get_frame_info m b = Some f -> in_stack m b.
  Proof.
    intros.
    destruct (in_stack_dec m b); auto.
    rewrite not_in_stack_get_assoc in H; auto. congruence.
  Qed.

  Inductive option_le_stack {A: Type} (Pns: A -> Prop) (Pss: A -> A -> Prop) (delta: Z): option A -> option A -> Prop :=
  | option_le_none_none : option_le_stack Pns Pss delta None None
  | option_le_some_some a b : Pss a b -> option_le_stack Pns Pss delta (Some a) (Some b)
  | option_le_none_some a: Pns a -> option_le_stack Pns Pss delta None (Some a).

  Lemma get_assoc_spec:
    forall s b fi,
      get_assoc_stack s b = Some fi ->
      exists fr tf, In (b,fi) (frame_adt_blocks fr) /\ fst tf = Some fr /\ In tf s.
  Proof.
    intros; edestruct get_assoc_stack_In as (f & tf & AIN & IN1 & IN2); eauto.
  Qed.

  Lemma In_tl:
    forall {A} (l: list A) x,
      In x (tl l) ->
      In x l.
  Proof.
    induction l; simpl; intros; eauto.
  Qed.

  Lemma nodup_tl:
    forall l,
      nodup l ->
      nodup (tl l).
  Proof.
    intros l ND; inv ND; simpl; auto. constructor.
  Qed.

  Lemma in_frame_get_assoc:
    forall a b,
      in_frame a b ->
      exists f : frame_info, get_assoc positive frame_info peq (frame_adt_blocks a) b = Some f.
  Proof.
    unfold in_frame, get_frame_blocks.
    intros a.
    generalize (frame_adt_blocks a).
    induction l; simpl; intros; eauto. easy.
    destr. destr. eauto. simpl in *. destruct H. congruence. subst.
    eauto.
  Qed.

  Lemma in_frames_get_assoc_tframes:
    forall s b,
      in_frames s b ->
      exists f, get_assoc_tframes s b = Some f.
  Proof.
    unfold in_frames, get_assoc_tframes. intros. destr; try easy.
    rewrite pred_dec_true.
    eapply in_frame_get_assoc; eauto. auto.
  Qed.

  Lemma in_stack_get_assoc_stack:
    forall s b,
      in_stack s b ->
      exists f, get_assoc_stack s b = Some f.
  Proof.
    induction s; simpl; intros; eauto. easy.
    rewrite in_stack_cons in H.
    destr.
    eapply in_frames_get_assoc_tframes; eauto.
    eapply IHs; eauto. intuition.
  Qed.

  Lemma get_frame_info_inj_gen:
    forall f g m1 s1 s2 b1 b2 delta
      (SI: stack_inject f g m1 s1 s2)
      (ND1: nodup s1)
      (ND2: nodup s2)
      (FB : f b1 = Some (b2, delta))
      (PERM: exists o k p, m1 b1 o k p /\ inject_perm_condition p),
      option_le_stack (fun fi => 
                   forall ofs k p,
                     m1 b1 ofs k p ->
                     inject_perm_condition p ->
                     frame_public fi (ofs + delta))
                (inject_frame_info delta)
                delta
                (get_frame_info s1 b1)
                (get_frame_info s2 b2).
  Proof.
    intros.
    unfold get_frame_info.
    destruct (in_stack_dec s1 b1).
    edestruct in_stack_in_frames_ex as (ff & INS & INF); eauto.
    destruct (get_assoc_stack s1 b1) eqn:STK1.
    - destruct PERM as (o & k & p & PERM & IPC).
      eapply (wf_stack_in_frames_in_frame) in INF; eauto.
      destruct INF as (vf1 & VF1 & INF).
      edestruct in_frame_info as (fi2 & INF2); eauto.
      erewrite get_assoc_stack_lnr in STK1; eauto. inv STK1.
      edestruct (stack_inject_compat _ _ _ _ _ SI) as (bi2 & INS2 & IFI); eauto.
      setoid_rewrite in_stack'_rew.
      setoid_rewrite in_frames'_rew.
      exists ff; split; auto. exists vf1; split; eauto.
      revert INS2. setoid_rewrite in_stack'_rew.
      setoid_rewrite in_frames'_rew.
      intros (tf & (fr & INFR & INFRS) & INS2).
      erewrite get_assoc_stack_lnr; eauto.
      constructor. auto.
    - edestruct (in_stack_get_assoc_stack s1 b1); congruence.
    - rewrite not_in_stack_get_assoc; auto.
      destruct (get_assoc_stack s2 b2) eqn:FI2.
      + apply option_le_none_some.
        edestruct get_assoc_spec as (fr & tfr & IN & AIN & INR); eauto.
        intros; eapply stack_inject_not_in_source; eauto.
        rewrite in_stack'_rew. setoid_rewrite in_frames'_rew.
        exists tfr. split. exists fr; split; auto. auto.
      + apply option_le_none_none.
  Qed.

  Lemma is_stack_top_inj_gen:
    forall P f g s1 s2 b1 b2 delta
      (MINJ: stack_inject f g P s1 s2)
      (FB: f b1 = Some (b2, delta))
      (PERM: exists o k p, P b1 o k p /\ inject_perm_condition p)
      (IST: is_stack_top s1 b1),
      is_stack_top s2 b2.
  Proof.
    intros.
    eapply stack_inject_is_stack_top; eauto.
  Qed.

  Lemma stack_access_inj_gen:
    forall f g m1 s1 s2 b1 b2 delta lo hi p
      (MINJ : stack_inject f g m1 s1 s2)
      (ND1: nodup s1)
      (ND2: nodup s2)
      (FAP: stack_agree_perms m1 s1)
      (FB : f b1 = Some (b2, delta))
      (RP: forall o, (lo <= o < hi)%Z -> m1 b1 o Cur p)
      (IPC: inject_perm_condition p)
      (NPSA: stack_access s1 b1 lo hi),
      stack_access s2 b2 (lo + delta) (hi + delta).
  Proof.
    unfold stack_access, public_stack_access.
    intros. revert NPSA.
    destruct (zlt lo hi).
    intros [A|A].
    - exploit is_stack_top_inj_gen; eauto.
      exists lo, Cur, p; split; eauto. apply RP. omega.
    - assert (forall fi, get_frame_info s2 b2 = Some fi -> public_stack_range (lo+delta) (hi+delta) fi).
      {
        intros.
        assert (in_stack s2 b2).
        exploit get_assoc_spec. eauto. intros (fr & tf & IN1 & AIN & IN2).
        eapply in_frames_in_stack; eauto.
        eapply in_frame_in_frames; eauto.
        eapply in_frame_blocks_in_frame; eauto.
        generalize (get_frame_info_inj_gen _ _ _ _ _ _ _ _ MINJ ND1 ND2 FB). rewrite H. intro GFIJ.
        trim GFIJ.
        {
          exists lo, Cur, p; split; eauto. apply RP; omega.
        }
        inv GFIJ.
        - rewrite <- H1 in A.
          symmetry in H1. apply get_assoc_spec in H1.
          destruct H1 as (fr & tf & IN1 & AIN & IN2).
          specialize (FAP _ IN2 _ AIN).
          red in FAP.
          assert (forall o, lo <= o < hi -> 0 <= o < frame_size a)%Z as INFR.
          intros.
          eapply FAP. eauto. apply RP. auto.
          destruct (zlt lo hi).
          + eapply public_stack_range_shift; eauto.
            apply INFR; auto. omega.
            cut (hi - 1 < frame_size a)%Z. omega.
            apply INFR; auto. omega.
          + eapply public_stack_range_lo_ge_hi. omega.
        - red.  intros.
          replace ofs with (ofs-delta+delta)%Z by omega. eapply H3.
          apply RP. omega. auto.
      }     
      right; destr.
      specialize (H _ eq_refl). auto.
    - intros; destr. right. eapply public_stack_range_lo_ge_hi. omega.
  Qed.

Lemma in_stack_tl:
  forall (l: stack)  b,
    in_stack ((tl l)) b ->
    in_stack (l) b.
Proof.
  destruct l; simpl; auto.
  intros; rewrite in_stack_cons; auto.
Qed.


(* Lemma in_frames_tl: *)
(*   forall l b, *)
(*     in_frames ((tl l)) b -> *)
(*     in_frames (l) b. *)
(* Proof. *)
(*   destruct l; simpl; auto. *)
(*   intros; rewrite in_frames_cons; auto. *)
(* Qed. *)

Lemma Forall_tl:
  forall {A} P (l: list A),
    Forall P l ->
    Forall P (tl l).
Proof.
  inversion 1; simpl; auto.
Qed.

Lemma stack_agree_perms_tl:
  forall P (l: stack),
    stack_agree_perms P l ->
    stack_agree_perms P (tl l).
Proof.
  red; intros.
  eapply H; eauto.
  eapply In_tl; eauto.
Qed.

Lemma wf_stack_tl p s:
  wf_stack p s ->
  wf_stack p (tl s).
Proof.
  eapply Forall_tl; eauto.
Qed.

Lemma tframe_inject_invariant:
  forall (m m': perm_type) f f1 f2 thr,
    (forall b ofs k p b' delta,
        f b = Some (b', delta) ->
        Plt b thr ->
        m' b ofs k p -> m b ofs k p) ->
    (forall b, in_frames f1 b -> Plt b thr) ->
    tframe_inject f m f1 f2 ->
    tframe_inject f m' f1 f2.
Proof.
  intros m m' f f1 f2 thr PERMS PLT TFI ff1 INf1 HP.
  specialize (TFI _ INf1).
  trim TFI. destruct HP as (b & o & k & p & FB & IFR & PERM & IPC).
  destruct (f b) eqn:?; try congruence. destruct p0.
  repeat eexists; eauto. congruence. eapply PERMS; eauto.
  eapply PLT; eauto. eapply in_frame_in_frames; eauto.
  destruct TFI as (f3 & EQ & FI).
  repeat eexists; eauto.
Qed.

Lemma tframe_inject_invariant_strong:
  forall (m m': perm_type) f f1 f2,
    (forall b ofs k p b' delta,
        f b = Some (b', delta) ->
        m' b ofs k p -> m b ofs k p) ->
    tframe_inject f m f1 f2 ->
    tframe_inject f m' f1 f2.
Proof.
  intros m m' f f1 f2 PERMS TFI ff1 INf1 HP.
  specialize (TFI _ INf1). trim TFI. destruct HP as (b & o & k & p & FB & IFR & PERM & IPC).
  destruct (f b) eqn:?; try congruence. destruct p0.
  repeat eexists; eauto. congruence.
  destruct TFI as (f3 & EQ & FI).
  subst. repeat eexists; eauto.
Qed.

Lemma in_take:
  forall {A} n (l: list A) t a,
    take n l = Some t ->
    In a t ->
    In a l.
Proof.
  intros A n l t a TAKE IN.
  rewrite (take_drop _ _ _ TAKE).
  rewrite in_app; auto.
Qed.


Definition in_frames_all (tf: tframe_adt) b : Prop :=
  In b (get_opt_frame_blocks (fst tf)) \/ exists f, In f (snd tf) /\ in_frame f b.

Fixpoint in_stack_all (s: stack) b : Prop :=
  match s with
    nil => False
  | tf::r => in_frames_all tf b \/ in_stack_all r b
  end.

Lemma in_frames_in_frames_all:
  forall s b,
    in_frames s b ->
    in_frames_all s b.
Proof.
  induction s; simpl; intros; eauto.
  rewrite in_frames_cons in H. destruct H as (fa & EQ & IFR). red. subst. simpl. left; auto.
Qed.

Lemma in_stack_in_stack_all:
  forall s b,
    in_stack s b ->
    in_stack_all s b.
Proof.
  induction s; simpl; intros; eauto.
  rewrite in_stack_cons in H.
  destruct H; eauto. left.
  eapply in_frames_in_frames_all; eauto.
Qed.

Lemma in_stack_all_drop:
  forall n l b,
    in_stack_all (drop n l) b ->
    in_stack_all l b.
Proof.
  induction n; simpl; intros; eauto.
  eapply IHn in H.
  destruct l; simpl in *; eauto.
Qed.

Lemma in_frames_all_in_stack_all:
  forall f l b,
    in_frames_all f b ->
    In f l ->
    in_stack_all l b.
Proof.
  induction l; simpl; intros; eauto.
  destruct H0; subst; eauto.
Qed.

Lemma tframe_inject_invariant':
  forall (m m': perm_type) f f1 f2 ,
    (forall b ofs k p,
        in_frames_all f1 b ->
        m' b ofs k p -> m b ofs k p) ->
    tframe_inject f m f1 f2 ->
    tframe_inject f m' f1 f2.
Proof.
  intros m m' f f1 f2 PERMS TFI ff1 INf1 HP.
  specialize (TFI _ INf1).
  trim TFI. destruct HP as (b & o & k & p & FB & IFR & PERM & IPC).
  destruct (f b) eqn:?; try congruence. destruct p0.
  repeat eexists; eauto. congruence. eapply PERMS; eauto.
  left. rewrite INf1. simpl. auto.
  destruct TFI as (f3 & EQ & FI).
  repeat eexists; eauto.
Qed.

Lemma stack_inject_aux_invariant:
  forall (m m': perm_type) f g s1 s2,
    stack_inject_aux f m g s1 s2 ->
    (forall b ofs k p,
        in_stack_all s1 b ->
        m' b ofs k p -> m b ofs k p) ->
    stack_inject_aux f m' g s1 s2.
Proof.
  induction 1; simpl; intros PERM; econstructor; eauto.
  - eapply IHstack_inject_aux; eauto. subst.
    intros; eapply PERM; eauto using in_stack_all_drop.
  - eapply Forall_impl. 2: apply FI.
    simpl.
    intros; eapply tframe_inject_invariant'. 2: eauto.
    intros; eapply PERM; eauto.
    eapply in_frames_all_in_stack_all; eauto.
    eapply in_take; eauto.
Qed.

Lemma stack_inject_invariant:
  forall (m m': perm_type) f g s1 s2,
    (forall b ofs k p,
        in_stack_all s1 b ->
        m' b ofs k p -> m b ofs k p) ->
    (forall b1 b2 delta, f b1 = Some (b2, delta) ->
                    ~ in_stack s1 b1 ->
                    forall fi,
                      in_stack' s2 (b2,fi) ->
                      forall o k pp,
                        m' b1 o k pp ->
                        inject_perm_condition pp ->
                        frame_public fi (o + delta)) ->
    stack_inject f g m s1 s2 ->
    stack_inject f g m' s1 s2.
Proof.
  intros m m' f g s1 s2 PERM PLT FI.
  destruct FI. constructor; auto.
  - intros.
    eapply stack_inject_aux_invariant; eauto.
  - intros. eauto.
Qed.

  (* Lemma stack_inject_invariant': *)
  (*   forall (m m': perm_type) f g f1 f2 thr, *)
  (*     (forall b ofs k p, *)
  (*         Plt b thr -> *)
  (*         m' b ofs k p -> m b ofs k p) -> *)
  (*     Forall (fun f1 => forall b, in_frames f1 b -> Plt b thr) f1 -> *)
  (*     Forall (fun t1 => forall f1 b, In f1 (snd t1) -> in_frame f1 b -> Plt b thr) f1 -> *)
  (*     (forall b1 b2 delta, f b1 = Some (b2, delta) -> *)
  (*                     in_stack f2 b2 -> *)
  (*                     Plt b1 thr) -> *)
  (*     stack_inject f g m f1 f2 -> *)
  (*     stack_inject f g m' f1 f2. *)
  (* Proof. *)
  (*   intros. *)
  (*   eapply stack_inject_invariant; eauto. *)
  (*   intros. *)
  (*   elim H5. eapply H2; eauto. *)
  (*   eapply in_stack'_in_stack; eauto. *)
  (* Qed. *)

  Lemma stack_inject_aux_invariant_strong:
    forall (m m': perm_type) f g s1 s2,
      stack_inject_aux f m g s1 s2 ->
      (forall b ofs k p b' delta,
          f b = Some (b', delta) ->
          m' b ofs k p -> m b ofs k p) ->
      stack_inject_aux f m' g s1 s2.
  Proof.
    induction 1; simpl; intros PERM; econstructor; eauto.
    eapply Forall_impl. 2: apply FI.
    simpl.
    intros; eapply tframe_inject_invariant_strong; eauto.
  Qed.

  Lemma stack_inject_invariant_strong:
    forall (m m': block -> _ -> _ -> _ -> Prop) f g f1 f2,
      (forall b ofs k p b' delta,
          f b = Some (b', delta) ->
          m' b ofs k p -> m b ofs k p) ->
      stack_inject f g m f1 f2 ->
      stack_inject f g m' f1 f2.
  Proof.
    intros m m' f g f1 f2 PERM FI.
    destruct FI. constructor; auto.
    - intros. eapply stack_inject_aux_invariant_strong; eauto.
    - intros; eapply stack_inject_not_in_source0; eauto.
  Qed.

  Lemma stack_inject_nil:
    forall f p,
      stack_inject f nil p nil nil.
  Proof.
    repeat constructor. easy.
  Qed.

  Lemma stack_inject_length_stack:
    forall j g P s1 s2,
      stack_inject j g P s1 s2 ->
      (length s2 <= length s1)%nat.
  Proof.
    intros j g P s1 s2 SI.
    inversion SI.
    revert stack_inject_frame_inject0. clear.
    revert g s1 s2.
    induction 1; simpl; intros; eauto.
    simpl in *. repeat destr_in TAKE. simpl.
    simpl in *. apply le_n_S. etransitivity. apply IHstack_inject_frame_inject0.
    rewrite drop_length. omega.
    eapply take_succeeds_inv; eauto.
  Qed.

  Fixpoint list_nats n :=
    match n with
      O => nil
    | S m => m :: list_nats m
    end.

  Lemma in_list_nats:
    forall n m,
      In m (list_nats n) <-> (m < n)%nat.
  Proof.
    induction n; simpl; split; intros.
    - easy.
    - omega.
    - destruct H; subst. omega. apply IHn in H; omega.
    - destruct (Nat.eq_dec m n); auto. right; rewrite IHn. omega.
  Qed.

  Lemma option_eq_true:
    forall {A} Aeq (o1 o2: option A),
      proj_sumbool (option_eq Aeq o1 o2) = true <-> o1 = o2.
  Proof.
    intros.
    destruct (option_eq Aeq o1 o2); try congruence.
    subst; tauto. split; inversion 1. congruence.
  Qed.

  Fixpoint filteri {A} (f: nat -> A -> bool) (l: list (nat * A)) : list (A) :=
    match l with
      nil => nil
    | (i,a)::r => let r' := filteri f r in
             if f i a then a :: r' else r'
    end.

  Lemma le_add_pos:
    (forall a b,
        0 <= b ->
        a <= a + b)%Z.
  Proof.
    intros; omega.
  Qed.

  Fixpoint pairi {A} (l: list A) i : list (nat * A) :=
    match l with
      nil => nil
    | a::r => (i,a)::(pairi r (S i))
    end.



Definition maxl (l: list Z) : option Z :=
  match l with nil => None | _ => Some (fold_right Z.max Z0 l) end.

Lemma maxl_is_max:
  forall l m,
    maxl l = Some m ->
    Forall (fun n => (n <= m)%Z) l.
Proof.
  destruct l. constructor.
  intros. unfold maxl in H.
  revert H. generalize (z :: l). inversion 1; subst.
  clear.
  induction l0; simpl; intros. constructor.
  constructor; auto.
  apply Z.le_max_l.
  eapply Forall_impl. 2: eauto. intros.
  simpl in H0.
  apply Zmax_bound_r. auto.
Qed.

Lemma maxl_in:
  forall l (F: Forall (fun n => 0 <= n)%Z l) m,
    maxl l = Some m ->
    In m l.
Proof.
  destruct l. inversion 2. unfold maxl. simpl. inversion 2; subst. clear H.
  revert z F.
  induction l; simpl; intros; eauto. inv F. rewrite Z.max_l; auto.
  rewrite Z.max_assoc.
  specialize (IHl (Z.max z a)). trim IHl.
  inv F. inv H2.
  constructor. apply Z.max_le_iff. auto.
  auto.
  destruct IHl. rewrite <- H.
  rewrite Zmax_spec. destr.
  auto.
Qed.

Definition size_frame (f: frame_adt) : Z := 
  align (frame_adt_size f) 8.

Definition opt_size_frame (of: option frame_adt) : Z :=
  match of with
  | Some f => size_frame f
  | None => Z0
  end.

Definition max_l (l: list Z) : Z :=
  fold_right Z.max Z0 l.

Definition size_frames (l: tframe_adt) : Z :=
  Z.max (opt_size_frame (fst l)) (max_l (map size_frame (snd l))).

Lemma size_frames_cons:
  forall a b,
    size_frames ( a , b ) = Z.max (opt_size_frame a) (max_l (map size_frame b)).
Proof.
  reflexivity.
Qed.

Fixpoint size_stack (l: stack) : Z :=
  match l with
    nil => 0
  | fr::r => size_stack r + size_frames fr
  end.

Lemma size_frame_pos:
  forall fr,
    (0 <= size_frame fr)%Z.
Proof.
  unfold size_frame.
  etransitivity.
  2: apply align_le. apply frame_adt_size_pos. omega.
Qed.

Lemma opt_size_frame_pos:
  forall fr,
    (0 <= opt_size_frame fr)%Z.
Proof.
  unfold opt_size_frame. intros. destr. apply size_frame_pos. omega.
Qed.

Lemma size_frames_pos:
  forall s,
    (0 <= size_frames s)%Z.
Proof.
  intros. unfold size_frames. 
  apply Z.max_le_iff.
  left.
  apply opt_size_frame_pos.
Qed.

Lemma size_stack_pos:
  forall s,
    (0 <= size_stack s)%Z.
Proof.
  induction s; simpl; intros; eauto. omega.
  generalize (size_frames_pos a); omega.
Qed.

Lemma size_stack_tl:
  forall l,
    (size_stack (tl l) <= size_stack l)%Z.
Proof.
  induction l; simpl; intros. omega.
  generalize (size_frames_pos a); omega.
Qed.
  


  Ltac elim_div :=
    unfold Zdiv, Zmod in *;
    repeat
      match goal with
      |  H : context[ Zdiv_eucl ?X ?Y ] |-  _ =>
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
      |  |-  context[ Zdiv_eucl ?X ?Y ] =>
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
      end; unfold Remainder.
  

  Open Scope Z_scope.
  Lemma align_ge1:
    forall sz al,
      al > 0 ->
      exists b, 0 <= b < al /\
           align sz al = sz + b /\ 
           b = (al - 1 - (sz - 1 - al * ((sz - 1) / al))).
  Proof.
    intros.
    generalize (align_le sz al H).
    destruct (align_divides sz al H).
    rewrite H0.
    intros. 
    unfold align in H0.
    rewrite <- H0.
    replace ((sz+al-1)/al) with (1+ ((sz-1)/al)).
    {
      replace ((1+ ((sz-1)/al))*al) with (al + (sz -1)/al *al).
      {
        rewrite Z.mul_comm.
        replace (al * ((sz - 1) / al)) with
        (al * ((sz - 1) / al) + (sz-1) mod al - (sz-1) mod al) by omega.
        rewrite <- Z.div_mod by omega.
        rewrite Z.mod_eq by omega.
        exists (al - 1 - (sz - 1 - al * ((sz - 1) / al))).
        split; try omega.
        {
          elim_div. assert (al <> 0) by omega. intuition.
        }
      }
      rewrite Z.mul_add_distr_r. omega.
    }
    {
      replace (sz + al - 1) with ((sz -1) + 1*al) by omega.
      rewrite Z_div_plus_full by omega.
      omega.
    }
  Qed.
  
  Lemma align_mono:
    forall al sz sz',
      al > 0 ->
      0 <= sz <= sz' ->
      align sz al <= align sz' al.
  Proof.
    intros.
    generalize (align_ge1 sz al H)
               (align_ge1 sz' al H).
    intros [b [A [B C]]] [c [D [E F]]].
    destruct (zlt (sz'-sz) al); try intuition omega.
    assert (exists d, 0 <= d < al /\ sz' = sz + d).
    {
      clear - H0 H l.
      exists (sz'-sz). intuition try omega.
    }
    destruct H1 as [d [ENC EQ]]. rewrite EQ in *.
    clear EQ.
    rewrite B; rewrite E.
    cut (      al * ((sz - 1) / al) <=
               (   al * ((sz + d - 1) / al))); intros; try omega.  
    apply Z.mul_le_mono_nonneg_l; try  omega.
    apply Z.div_le_mono; try omega.
  Qed.

  Lemma stack_inject_aux_id:
    forall p s,
      stack_inject_aux inject_id p (flat_frameinj (length s)) s s.
  Proof.
    induction s; simpl; intros; econstructor; simpl; eauto.
    repeat constructor.
    eapply tframe_inject_id; eauto.
  Qed.

  Lemma flat_frameinj_pos s:
    Forall (lt 0) (flat_frameinj s).
  Proof.
    induction s; simpl; intros; constructor; auto.
  Qed.

  Lemma stack_inject_id:
    forall p s,
      wf_stack p s ->
      stack_inject inject_id (flat_frameinj (length s)) p s s.
  Proof.
    intros p s WF; constructor; auto.
    eapply stack_inject_aux_id; eauto.
    intros b1 b2 delta bi2 FB NIS FI o k p0 PERM IPC.
    apply in_stack'_in_stack in FI. inv FB. congruence.
  Qed.

(** The following shows how to transport a stack injection when more blocks get
injected. We have an hypothesis about those new blocks. Namely, they are not
part of the source stack, and if the block they're injected to is part of the
stack, then the corresponding locations have the public stack permission. The
typical case when a new block is not in the stack but the target block they
inject to is already in is Inlining, where the parent function clearly already
exists and is already on the stack when the block for the callee is allocated.
Another scenario is generation of single-stack-block Asm, where the unique stack
block is also present and part of the stack when the 'source' blocks get
allocated. *)

  Lemma in_stack_drop:
    forall n s b,
      in_stack (drop n s) b ->
      in_stack s b.
  Proof.
    induction n; simpl; intros; eauto.
    apply IHn in H.
    apply in_stack_tl. auto.
  Qed.

Lemma stack_inject_aux_incr:
  forall f f' g (p: block -> Z -> perm_kind -> permission -> Prop)  s1 s2,
    stack_inject_aux f p g s1 s2 ->
    inject_incr f f' ->
    (forall b b' delta,
        f b = None ->
        f' b = Some (b', delta) ->
        ~ in_stack s1 b) ->
    stack_inject_aux f' p g s1 s2.
Proof.
  induction 1; simpl; intros INCR NEW; econstructor; eauto.
  subst.
  eapply IHstack_inject_aux; eauto.
  intros b b' delta H0 H1 INS. eapply NEW; eauto using in_stack_drop.
  eapply Forall_impl. 2: apply FI.
  simpl; intros.
  eapply tframe_inject_incr; eauto. subst.
  intros b b' delta H2 H3 IFR.
  eapply NEW; eauto.
  eapply in_frames_in_stack; eauto using in_take.
Qed.

Lemma stack_inject_incr:
  forall f f' g (p: block -> Z -> perm_kind -> permission -> Prop)  s1 s2,
    inject_incr f f' ->
    (forall b b' delta,
        f b = None ->
        f' b = Some (b', delta) ->
        ~ in_stack s1 b 
        /\ forall fi,
            in_stack' s2 (b', fi) ->
            forall o k pp,
              p b o k pp ->
              inject_perm_condition pp ->
              frame_public fi (o + delta)) ->
    stack_inject f g p s1 s2 ->
    stack_inject f' g p s1 s2.
Proof.
  intros f f' g p s1 s2 INCR NEW SI.
  inversion SI; constructor; eauto.
  - eapply stack_inject_aux_incr; eauto.
    intros; eapply NEW; eauto.
  - intros b1 b2 delta bi2 SOME NIS INS o k p0 P IPC.
    destruct (f b1) as [[b2' delta']|] eqn:FB.
    exploit INCR. eauto. rewrite SOME. inversion 1; subst.
    eauto.
    generalize (NEW _ _ _ FB SOME). intros (NIN1 & NIN2). eapply NIN2 in INS; eauto.
Qed.

Lemma norepet_1:
  forall {A:Type} (a:A),
    list_norepet (a::nil).
Proof.
  repeat constructor. easy.
Qed.

Definition make_singleton_frame_adt (b: block) (sz: Z) (machsz: Z) :=
  {|
    frame_adt_blocks := (b, public_frame_info sz)::nil;
    frame_adt_size := Z.max 0 machsz;
    frame_adt_blocks_norepet := norepet_1 _;
    frame_adt_size_pos := Z.le_max_l _ _
  |}.

Definition make_singleton_frame_adt' (b: block) fi (sz: Z) :=
  {|
    frame_adt_blocks := (b,fi)::nil;
    frame_adt_size := Z.max 0 sz;
    frame_adt_blocks_norepet := norepet_1 _;
    frame_adt_size_pos := Z.le_max_l _ _
  |}.

  Lemma val_inject_ext:
    forall j1 j2 m1 m2,
      Val.inject j1 m1 m2 ->
      (forall x, j1 x = j2 x) ->
      Val.inject j2 m1 m2.
  Proof.
    intros j1 j2 m1 m2 INJ EXT.
    inv INJ; econstructor; eauto.
    rewrite <- EXT; eauto.
  Qed.

  Lemma memval_inject_ext:
    forall j1 j2 m1 m2,
      memval_inject j1 m1 m2 ->
      (forall x, j1 x = j2 x) ->
      memval_inject j2 m1 m2.
  Proof.
    intros j1 j2 m1 m2 INJ EXT.
    inv INJ; constructor; auto.
    eapply val_inject_ext; eauto.
  Qed.




Lemma frame_inject_ext:
  forall j1 j2 f1 f2,
    frame_inject j1 f1 f2 ->
    (forall b, j1 b = j2 b) ->
    frame_inject j2 f1 f2.
Proof.
  intros j1 j2 f1 f2 FI EXT.
  red in FI |- *.
  rewrite Forall_forall in *.
  intros x IN b2 delta J2.
  rewrite <- EXT in J2. eauto.
Qed.

Lemma has_perm_frame_ext:
  forall j j' P f,
    (forall b, j b = j' b) ->
    has_perm_frame P j f ->
    has_perm_frame P j' f.
Proof.
  intros j j' P f EXT (b & o & k & p0 & FSOME & INFR1 & PERM & IPC).
  repeat eexists; eauto. rewrite EXT in FSOME; auto.
Qed.

Lemma tframe_inject_ext:
  forall j1 j2 p f1 f2,
    tframe_inject j1 p f1 f2 ->
    (forall b, j1 b = j2 b) ->
    tframe_inject j2 p f1 f2.
Proof.
  intros j1 j2 p f1 f2 FI EXT ff1 INf1 HP.
  eapply has_perm_frame_ext in HP. 2: symmetry; eauto.
  edestruct FI as (f3 & IN1 & FI12); eauto.
  repeat eexists; eauto. eapply frame_inject_ext; eauto.
Qed.

  Lemma stack_inject_aux_ext':
    forall j1 j2 g P m1 m2,
      stack_inject_aux j1 P g m1 m2 ->
      (forall x, j1 x = j2 x) ->
      stack_inject_aux j2 P g m1 m2.
  Proof.
    induction 1; simpl; intros; econstructor; eauto.
    eapply Forall_impl. 2: apply FI.
    simpl; intros.
    eapply tframe_inject_ext; eauto.
  Qed.

  Lemma stack_inject_ext':
    forall j1 j2 g P m1 m2,
      stack_inject j1 g P m1 m2 ->
      (forall x, j1 x = j2 x) ->
      stack_inject j2 g P m1 m2.
  Proof.
    intros j1 j2 g P m1 m2 INJ EXT.
    inv INJ; constructor; eauto.
    - eapply stack_inject_aux_ext'; eauto.
    - intros.
      eapply stack_inject_not_in_source0; eauto. rewrite EXT; eauto.
  Qed.


    Lemma frameinj_push_flat:
      forall m,
        flat_frameinj (Datatypes.S m) = 1%nat :: flat_frameinj m.
    Proof.
      reflexivity.
    Qed.
    
Lemma frame_at_pos_cons:
  forall l i f a,
    frame_at_pos l i f ->
    frame_at_pos (a::l) (S i) f.
Proof.
  intros l i f a H; inv H; econstructor.
  simpl.
  auto.
Qed.

Lemma frame_at_pos_last:
  forall l a f,
    frame_at_pos (a::l) 0 f ->
    f = a.
Proof.
  intros l a f H. inv H. simpl in H0. congruence.
Qed.

Lemma frame_at_pos_same_frame:
  forall s i1 i2 f b,
    frame_at_pos s i1 f ->
    frame_at_pos s i2 f ->
    in_frames f b ->
    nodup s ->
    i1 = i2.
Proof.
  induction s; simpl; intros; eauto.
  - inv H.  rewrite nth_error_nil in H3. easy.
  - inv H; inv H0.
    destruct (Nat.eq_dec i1 i2); auto.
    exfalso.
    destruct (Nat.eq_dec i1 O).
    + subst. simpl in H3. inv H3.
      destruct i2. congruence. simpl in H. apply nth_error_In in H.
      inv H2. specialize (H5 _ H1). apply H5.
      eapply in_frames_in_stack; eauto.
    + destruct (Nat.eq_dec i2 0).
      * subst.
        simpl in H. inv H.
        destruct i1. congruence. simpl in H3. apply nth_error_In in H3.
        inv H2. specialize (H5 _ H1). apply H5.
        eapply in_frames_in_stack; eauto.
      * destruct i1, i2; try congruence. simpl in *.
        apply n. f_equal. eapply IHs; eauto.
        constructor; auto. constructor; auto.
        apply nodup_tl in H2.
        simpl in *; auto.
Qed.

Open Scope nat_scope.



Opaque minus.

Inductive top_tframe_prop (P: tframe_adt -> Prop) : stack -> Prop :=
| top_tframe_prop_intro tf r:
    P tf ->
    top_tframe_prop P (tf::r).


(* Definition wf_tframe_strong (m: perm_type) (j: meminj) (f: tframe_adt) : Prop := *)
(*   forall b, *)
(*     j b <> None -> *)
(*     in_frames f b -> *)
(*     forall o k p, ~ m b o k p. *)


Definition top_tframe_tc (s: stack) : Prop :=
  top_tframe_prop (fun tf => fst tf = None) s.

Lemma stack_inject_push_new_stage_right:
  forall j n g P s1 s2,
    stack_inject j (n :: g) P s1 s2 ->
    top_tframe_tc s1 ->
    (2 <= n)%nat ->
    stack_inject j (1%nat :: pred n :: g) P s1 ((None,nil)::s2).
Proof.
  intros j n g P s1 s2 SI TTNP Gof1.
  inversion SI; constructor; auto.
  - inv stack_inject_frame_inject0.
    simpl in *. repeat destr_in TAKE.
    econstructor. reflexivity. simpl. eauto.
    destruct n0. omega. econstructor; eauto. inv FI; auto.
    repeat constructor.
    intros ff1 INf1 _. exfalso.
    inv TTNP. congruence.
  - simpl. intros; eapply stack_inject_not_in_source0; eauto. tauto.
Qed.

Lemma frame_at_pos_cons_inv:
  forall a s i f,
    frame_at_pos (a::s) i f ->
    O < i ->
    frame_at_pos s (pred i) f.
Proof.
  intros a s i f FAP LT ; inv FAP.
  destruct i. omega.
  simpl in H. simpl. constructor; auto.
Qed.

Lemma stack_inject_unrecord_parallel:
  forall j g m1 s1 s2
    (SI: stack_inject j (1%nat :: g) m1 s1 s2)
    (ND2: nodup s2)
    fr2 l2
    (STK2 : s2 = fr2 :: l2)
    fr1 l1
    (STK1 : s1 = fr1 :: l1),
    stack_inject j g m1 l1 l2.
Proof.
  intros. subst.
  inversion SI; constructor; auto.
  + inv stack_inject_frame_inject0. simpl in *; auto.
  + simpl. intros b1 b2 delta bi2 JB NIS INS o k p PERM IPC.
    inv stack_inject_frame_inject0. simpl in *; auto. inv TAKE.
    inv FI. clear H2.
    destruct (in_frames_dec fr1 b1).
    * destruct (in_frames_in_frame_ex _ _ i) as (fr & INfrs & INFR).
      inv ND2. edestruct H3.
      eapply tframe_inject_in_frames; eauto.
      eapply in_stack'_in_stack; eauto.
    * eapply stack_inject_not_in_source0 in JB; eauto.
      rewrite in_stack_cons. intuition.
Qed.

Lemma stack_inject_unrecord_parallel_frameinj_flat_on:
  forall j m1 s1 s2
    (SI: stack_inject j (flat_frameinj (length s2)) m1 s1 s2)
    (ND2: nodup s2)
    fr2 l2
    (STK2 : s2 = fr2 :: l2)
    fr1 l1
    (STK1 : s1 = fr1 :: l1),
    stack_inject j (flat_frameinj (length l2)) m1 l1 l2.
Proof.
  intros. subst.
  eapply stack_inject_unrecord_parallel; eauto.
Qed.

Definition same_sizes_frame f1 f2 := frame_adt_size f1 = frame_adt_size f2.

Lemma same_sizes_frame_size_eq:
  forall f1 f2,
    same_sizes_frame f1 f2 ->
    size_frame f1 = size_frame f2.
Proof.
  intros f1 f2 SS; unfold size_frame; rewrite SS. reflexivity.
Qed.

Definition same_sizes_list_frames tf1 tf2 :=
  list_forall2 same_sizes_frame tf1 tf2.

Definition same_sizes_list_frames_size_eq:
  forall tf1 tf2 (SS: same_sizes_list_frames tf1 tf2),
    map size_frame tf1 = map size_frame tf2.
Proof.
  induction 1; simpl; intros; eauto.
  apply same_sizes_frame_size_eq in H. congruence.
Qed.

Definition same_sizes_opt_frame of1 of2 :=
  match of1, of2 with
  | Some f1, Some f2 => same_sizes_frame f1 f2
  | None, None => True
  | _, _ => False
  end.

Lemma same_sizes_opt_frame_size_eq:
  forall f1 f2,
    same_sizes_opt_frame f1 f2 ->
    opt_size_frame f1 = opt_size_frame f2.
Proof.
  intros f1 f2 SS; red in SS.
  repeat destr_in SS. simpl.
  apply same_sizes_frame_size_eq; eauto.
Qed.

Definition same_sizes_tframes (tf1 tf2: tframe_adt) :=
  same_sizes_opt_frame (fst tf1) (fst tf2) /\
  same_sizes_list_frames (snd tf1) (snd tf2).

Lemma same_sizes_tframes_size_eq:
  forall tf1 tf2
    (SS: same_sizes_tframes tf1 tf2),
    size_frames tf2 = size_frames tf1.
Proof.
  intros tf1 tf2 (SS1 & SS2); unfold size_frames.
  apply same_sizes_opt_frame_size_eq in SS1.
  apply same_sizes_list_frames_size_eq in SS2. congruence.
Qed.

Inductive stack_equiv : stack -> stack -> Prop :=
| stack_equiv_nil: stack_equiv nil nil
| stack_equiv_cons s1 s2 tf1 tf2
                   (SE: stack_equiv s1 s2)
                   (LF2: same_sizes_tframes tf1 tf2):
  stack_equiv (tf1::s1) (tf2::s2).

Lemma stack_equiv_fsize:
  forall s1 s2,
    stack_equiv s1 s2 ->
    size_stack s2 = size_stack s1.
Proof.
  induction 1; simpl; intros. reflexivity.
  f_equal; auto. eapply same_sizes_tframes_size_eq; eauto.
Qed.

Lemma stack_equiv_length:
  forall s1 s2, stack_equiv s1 s2 -> length s1 = length s2.
Proof.
  induction 1; simpl; intros; eauto.
Qed.

Lemma stack_equiv_tail:
  forall s1 s2,
    stack_equiv s1 s2 ->
    stack_equiv (tl s1) (tl s2).
Proof.
  inversion 1; simpl; auto; constructor; auto.
Qed.

Hint Resolve stack_equiv_tail.

Inductive match_stack : list (option (block * Z)) -> stack -> Prop :=
| match_stack_nil s: match_stack nil s
| match_stack_cons lsp s f r sp bi z
                       (REC: match_stack lsp s)
                       (BLOCKS: frame_adt_blocks f = (sp,bi)::nil)
                       (SIZE: frame_size bi = Z.max 0 z):
    match_stack (Some (sp,z) :: lsp) ( (Some f , r) :: s).

Lemma list_forall2_refl:
  forall (R: frame_adt -> frame_adt -> Prop) (Rrefl: forall x, R x x) s,
  list_forall2 R s s.
Proof.
  induction s; constructor; auto.
Qed.

Lemma stack_equiv_refl:
  forall s,
    stack_equiv s s.
Proof.
  induction s; constructor. auto.
  split; red. repeat destr.
  apply list_forall2_refl. reflexivity.
Qed.
End INJ.

Program Definition inject_perm_upto_writable: InjectPerm :=
  {|
    inject_perm_condition := fun p => perm_order Writable p
  |}.

Program Definition inject_perm_all: InjectPerm :=
  {|
    inject_perm_condition := fun p => True
  |}.

(* Definition same_head (P: perm_type) (m m': stack) := *)
(*   list_forall2 *)
(*     (fun tf1 tf2 => *)
(*        (forall f1, In f1 tf1 -> has_perm_frame (injperm:=inject_perm_all) P inject_id f1 -> In f1 tf2) *)
(*        /\ (forall f1, In f1 tf2 -> In f1 tf1) *)
(*     ) *)
(*     m m'. *)

(* Lemma same_head_in_stack': *)
(*   forall P s1 s2, same_head P s1 s2 -> forall b fi, in_stack' s2 (b,fi) -> in_stack' s1 (b,fi). *)
(* Proof. *)
(*   induction 1; simpl; intros; eauto. *)
(*   destruct H. *)
(*   destruct H1; auto. *)
(*   left. *)
(*   rewrite in_frames'_rew in H1. destruct H1 as (fr & IFR & INb1). *)
(*   apply H2 in INb1. *)
(*   rewrite in_frames'_rew; eauto. *)
(* Qed. *)

(* Lemma same_head_get_frame_info: *)
(*   forall P s1 s2 (SH: same_head P s1 s2) *)
(*     (ND: nodup s1) (ND': Forall nodupt s1) *)
(*     b f (GFI: get_frame_info s2 b = Some f), *)
(*     get_frame_info s1 b = Some f. *)
(* Proof. *)
(*   intros. *)
(*   apply get_assoc_spec in GFI. *)
(*   destruct GFI as (fr & tf & INblocks & INtf & INS). *)
(*   exploit same_head_in_stack'; eauto. *)
(*   rewrite in_stack'_rew. eexists; split; eauto. *)
(*   rewrite in_frames'_rew. eexists; split; eauto. *)
(*   intro INS'. *)
(*   clear INblocks INtf INS. *)
(*   rewrite in_stack'_rew in INS'. setoid_rewrite in_frames'_rew in INS'. *)
(*   destruct INS' as (ttf & (tfr & IFR & ITF) & INS). *)
(*   eapply get_assoc_stack_lnr; eauto. *)
(* Qed. *)

(* Lemma same_head_in_impl: *)
(*   forall P s1 s2, same_head P s1 s2 -> forall b, in_stack s2 b -> in_stack s1 b. *)
(* Proof. *)
(*   intros. *)
(*   eapply in_stack_in_frames_ex in H0. destruct H0 as (tf & INS & IFRS). *)
(*   eapply in_frames_in_frame_ex in IFRS. destruct IFRS as (fr & IFRS & IFR). *)
(*   apply in_frame_info in IFR. destruct IFR as (fi & IFR). *)
(*   eapply in_stack'_in_stack. eapply same_head_in_stack'; eauto. *)
(*   rewrite in_stack'_rew. eexists; split; eauto. *)
(*   rewrite in_frames'_rew. eexists; split; eauto. *)
(* Qed. *)

(* Lemma same_head_fap: *)
(*   forall P s1 s2 (SH: same_head P s1 s2) *)
(*          f1 i (FAP1: f1 @ s1 : i), *)
(*   exists f2, f2 @ s2 : i /\ (forall ff1, In ff1 f1 -> has_perm_frame (injperm:= inject_perm_all) P inject_id ff1 -> In ff1 f2). *)
(* Proof. *)
(*   induction 1; simpl; intros; eauto. *)
(*   destruct H. *)
(*   destruct i. *)
(*   - apply frame_at_pos_last in FAP1. subst. *)
(*     exists b1; split. constructor; reflexivity. *)
(*     auto. *)
(*   - apply frame_at_pos_cons_inv in FAP1. *)
(*     eapply IHSH in FAP1. destruct FAP1 as (f2 & FAP2 & PROP). *)
(*     exists f2; split. apply frame_at_pos_cons. auto. eauto. omega. *)
(* Qed. *)

Lemma has_perm_frame_impl {injperm: InjectPerm}:
  forall (P1 P2: perm_type) j f tf,
    has_perm_frame P1 j f ->
    frame_inject j f tf ->
    (forall b1 b2 delta o k p, j b1 = Some (b2, delta) -> P1 b1 o k p -> inject_perm_condition p -> P2 b2 (o + delta)%Z k p) ->
    has_perm_frame P2 inject_id tf.
Proof.
  intros P1 P2 j f tf (b & o & k & p & NONE & IFR & PERM1 & IPC) FI PERMS.
  red in FI.
  apply in_frame_info in IFR. destruct IFR as (fi & IFR).
  rewrite Forall_forall in FI; specialize (FI _ IFR).
  simpl in FI.
  destruct (j b) eqn:?; try congruence. destruct p0.
  specialize (FI _ _ eq_refl).
  destruct FI as (fi' & IN' & IFI).
  exists b0, (o + z)%Z, k, p. split. unfold inject_id. congruence.
  split. eapply in_frame'_in_frame; eauto. split; eauto.
Qed.

(* Lemma same_head_more_perm {injperm: InjectPerm}: *)
(*   forall (P1 P2: perm_type) s1 s2 *)
(*          (SH: same_head P1 s1 s2) *)
(*          (SAMEPERM: forall b o k p, in_stack s1 b -> P2 b o k p -> P1 b o k p), *)
(*     same_head P2 s1 s2. *)
(* Proof. *)
(*   induction 1; simpl; intros; constructor; auto. *)
(*   - destruct H; split; auto. *)
(*     intros; eapply H; eauto. *)
(*     destruct H2 as (b & o & k & p & NONE & IFR & PERM & IPC). *)
(*     exists b, o, k, p; repeat split; eauto. eapply SAMEPERM; eauto. *)
(*     rewrite in_stack_cons; left. *)
(*     eapply in_frame_in_frames; eauto. *)
(*   - apply IHSH. intros. eapply SAMEPERM; eauto. *)
(*     apply in_stack_tl. simpl; auto. *)
(* Qed. *)

(* Lemma public_stack_access_same_head: *)
(*   forall s1 (ND: nodup s1) (ND': Forall nodupt s1) s2 P (SH: same_head P s1 s2) b lo hi *)
(*          (PSA: public_stack_access s1 b lo hi), *)
(*     public_stack_access s2 b lo hi. *)
(* Proof. *)
(*   intros. red. destr. red in PSA. *)
(*   erewrite same_head_get_frame_info in PSA; eauto. *)
(* Qed. *)

Definition stack_top_is_new s :=
  top_tframe_prop (fun tf => tf = (None,nil)) s.

(* Lemma is_stack_top_same_head: *)
(*   forall P s1 (WF: wf_stack P inject_id s1) (ND: nodup s1) s2 (SH: same_head P s1 s2) b *)
(*          o k p (PERM: P b o k p) *)
(*          (IST: is_stack_top s1 b), *)
(*     is_stack_top s2 b \/ ~ in_stack s2 b. *)
(* Proof. *)
(*   intros. *)
(*   inv SH. easy. *)
(*   destruct H. *)
(*   red in IST. simpl in IST. *)
(*   change (in_frames a1 b) in IST. *)
(*   left. red. simpl. *)
(*   change (in_frames b1 b). *)
(*   edestruct in_frames_in_frame_ex as (fr & IFRS & IFR). eauto. *)
(*   eapply in_frame_in_frames; eauto. apply H; auto. *)
(*   exists b, o, k, p; repeat split; auto. unfold inject_id; congruence. *)
(* Qed. *)

(* Lemma stack_access_same_head: *)
(*   forall s1 P (ND: nodup s1) (ND': Forall nodupt s1) (WF: wf_stack P inject_id s1) s2 (SH: same_head P s1 s2) b lo hi k p *)
(*          (R: forall o, (lo <= o < hi)%Z -> P b o k p) *)
(*          (SA: stack_access s1 b lo hi), *)
(*     stack_access s2 b lo hi. *)
(* Proof. *)
(*   intros. *)
(*   destruct (zlt lo hi). *)
(*   destruct SA as [IST|PSA]. *)
(*   edestruct is_stack_top_same_head; eauto. apply (R lo). omega. left; auto. *)
(*   right; red; destr. eapply get_frame_info_in_stack in Heqo; congruence. *)
(*   right; eapply public_stack_access_same_head; eauto. *)
(*   eapply lo_ge_hi_stack_access; eauto. *)
(* Qed. *)

(* Lemma stack_access_same_head_or_not_in_stack: *)
(*   forall s1 P (ND: nodup s1) (ND': Forall nodupt s1) (WF: wf_stack P inject_id s1) s2 b *)
(*          (SH: same_head P s1 s2 \/ ~ in_stack s2 b) lo hi k p *)
(*          (R: forall o, (lo <= o < hi)%Z -> P b o k p) *)
(*          (SA: stack_access s1 b lo hi), *)
(*     stack_access s2 b lo hi. *)
(* Proof. *)
(*   intros. *)
(*   destruct SH as [SH | NIS]. *)
(*   eapply stack_access_same_head; eauto. *)
(*   right. red. destr. apply get_frame_info_in_stack in Heqo. congruence.           *)
(* Qed. *)

Lemma max_in_le:
  forall l a i,
    In a l ->
    (a <= fold_right Z.max i l)%Z.
Proof.
  induction l; simpl; intros; eauto.
  easy. destruct H; eauto. subst. apply Z.le_max_l.
  apply Z.max_le_iff. right; eauto.
Qed.

Lemma max_sublist:
  forall l1 l2 i,
    (forall x, In x l1 -> In x l2) ->
    (fold_right Z.max i l1 <= fold_right Z.max i l2)%Z.
Proof.
  induction l1; simpl; intros; eauto.
  induction l2; simpl; intros; eauto. omega.
  apply Z.max_le_iff. right. apply IHl2. easy.
  apply Z.max_lub_iff. split.
  apply max_in_le; auto.
  apply IHl1. auto.
Qed.

(* Lemma same_head_size: *)
(*   forall P s1 s2, *)
(*     same_head P s1 s2 -> *)
(*     (size_stack s2 <= size_stack s1)%Z. *)
(* Proof. *)
(*   induction 1; simpl; intros; rewrite ? size_stack_cons. omega. *)
(*   cut (size_frames b1 <= size_frames a1)%Z. omega. *)
(*   apply max_sublist. setoid_rewrite in_map_iff. *)
(*   intros x (x0 & EQ & IN). exists x0; split; auto. apply H. auto. *)
(* Qed. *)

(* Lemma same_head_refl: *)
(*   forall P s, *)
(*     same_head P s s. *)
(* Proof. *)
(*   induction s; simpl; intros; constructor; eauto. *)
(* Qed. *)

(* For use in Mach and Asm, the parent_sp pointer is now computed on the stack
   adt rather than on the abstract semantic callstack in Mach or with an extra
   stored pointer in Asm. *)

Definition current_frame_sp (tf: tframe_adt) : val :=
  match fst tf with
  | Some fr =>
    match frame_adt_blocks fr with
    | (b,fi)::nil => Vptr b Integers.Ptrofs.zero
    | _ => Vundef
    end
  | _ => Vnullptr
  end.

Definition current_sp (stk: stack) : val :=
  match stk with
    fr :: _ => current_frame_sp fr
  | _ => Vnullptr
  end.

Definition parent_sp (stk: stack) : val :=
  match stk with
    nil => Vundef
  | _ :: tl => current_sp tl
  end.

Lemma type_parent_sp:
  forall stk,
  Val.has_type (parent_sp stk) Tptr.
Proof.
  unfold parent_sp, current_sp, current_frame_sp. intros.
  repeat destr; try now (simpl; auto).
Qed.
Definition opt_cons {A: Type} (o: option A) (l: list A) : list A :=
  match o with
    None => l
  | Some a => a::l
  end.

Lemma In_opt_cons:
  forall {A} o (l: list A) a,
    In a (opt_cons o l) ->
    o = Some a \/ In a l.
Proof.
  intros. destruct o; simpl in *; eauto. intuition congruence.
Qed.

Lemma size_frames_eq:
  forall f l, size_frames (f, l) = size_frames (None, opt_cons f l).
Proof.
  unfold size_frames; simpl.
  destruct f. simpl. intros.
  rewrite (Z.max_r 0). auto. apply Z.max_le_iff. left; apply size_frame_pos.
  simpl. reflexivity.
Qed.


Lemma map_opt_cons:
  forall {A B} (f: A -> B) o l,
    map f (opt_cons o l) = opt_cons (option_map f o) (map f l).
Proof.
  destruct o; simpl; reflexivity.
Qed.

Lemma max_opt_size_frame_tailcall:
  forall f l,
    Z.max (opt_size_frame f) (max_l l) = max_l (opt_cons (option_map size_frame f) l).
Proof.
  destruct f; simpl; auto.
  intros; apply Z.max_r.
  induction l; simpl; intros; eauto. omega.
  apply Z.max_le_iff. auto.
Qed.

Lemma size_frames_tc:
  forall f,
    size_frames (None, opt_cons (fst f) (snd f)) = size_frames f.
Proof.
  unfold size_frames.
  intros. simpl.
  rewrite map_opt_cons. rewrite <- max_opt_size_frame_tailcall.
  apply Z.max_r.
  rewrite Z.max_le_iff. left. destruct f; simpl. destruct o; simpl.
  apply size_frame_pos. omega.    
Qed.

