Require Import Coqlib.

Lemma of_nat_le_mono : forall m n,
  (m <= n)%nat -> Ple (Pos.of_nat m) (Pos.of_nat n).
Proof.
  induction 1; intros.
  - apply Ple_refl.
  - apply Ple_trans with (Pos.of_nat m0); auto.
    simpl. destruct m0. simpl. apply Ple_refl.
    apply Ple_succ.
Qed.

Lemma pos_incr_comm : forall p,
  Pos.of_nat (Datatypes.S (Pos.to_nat p))%nat = Psucc p.
Proof.
  clear. intros p. rewrite <- Pos2Nat.inj_succ.
  rewrite Pos2Nat.id. auto.
Qed.

Lemma Plt_le_absurd : forall a b,
  Plt a b -> Ple b a -> False.
Proof.
  intros a b H H0. apply Pos.lt_nle in H. unfold Ple in *.
  contradiction.
Qed.
