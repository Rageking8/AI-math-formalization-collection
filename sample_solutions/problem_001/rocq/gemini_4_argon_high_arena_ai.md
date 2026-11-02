# Gemini 4 Argon High (Arena AI)

Model: `gemini-4-argon-high` (via Arena AI)\
Date: `2 November 2026`\
Line count: `120`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals ZArith Lra Lia.
Open Scope R_scope.

Definition alpha : R := (5 + sqrt 17) / 2.
Definition beta : R := (5 - sqrt 17) / 2.

Fixpoint ab_seq (n : nat) : Z * Z :=
  match n with
  | O => (2%Z, 5%Z)
  | S n' =>
    let (x, y) := ab_seq n' in
    (y, (5 * y - 2 * x)%Z)
  end.

Definition a_seq (n : nat) : Z := fst (ab_seq n).

Lemma ab_seq_snd : forall n : nat, snd (ab_seq n) = a_seq (S n).
Proof.
  intro n. unfold a_seq. simpl. destruct (ab_seq n). reflexivity.
Qed.

Lemma a_seq_SS : forall n : nat,
  a_seq (S (S n)) = (5 * a_seq (S n) - 2 * a_seq n)%Z.
Proof.
  intro n. rewrite <- ab_seq_snd. unfold a_seq. simpl.
  destruct (ab_seq n) as [x y]. simpl. reflexivity.
Qed.

Lemma a_seq_odd : forall n : nat, Z.Odd (a_seq (S n)).
Proof.
  induction n as [| n IH].
  - change (a_seq 1) with 5%Z.
    exists 2%Z. lia.
  - rewrite a_seq_SS.
    destruct IH as [k Hk].
    exists (5 * k + 2 - a_seq n)%Z.
    lia.
Qed.

Lemma sqrt17_sq : sqrt 17 * sqrt 17 = 17.
Proof.
  apply sqrt_sqrt; lra.
Qed.

Lemma alpha_sq : alpha * alpha = 5 * alpha - 2.
Proof.
  unfold alpha. pose proof sqrt17_sq. nra.
Qed.

Lemma beta_sq : beta * beta = 5 * beta - 2.
Proof.
  unfold beta. pose proof sqrt17_sq. nra.
Qed.

Lemma a_seq_eq : forall n : nat,
  IZR (a_seq n) = alpha ^ n + beta ^ n /\
  IZR (a_seq (S n)) = alpha ^ (S n) + beta ^ (S n).
Proof.
  induction n as [| n [IH1 IH2]].
  - change (a_seq 0) with 2%Z.
    change (a_seq 1) with 5%Z.
    simpl. unfold alpha, beta. split; lra.
  - split.
    + exact IH2.
    + rewrite a_seq_SS, minus_IZR, !mult_IZR, IH1, IH2.
      simpl.
      replace (alpha * (alpha * alpha ^ n)) with ((alpha * alpha) * alpha ^ n) by ring.
      replace (beta * (beta * beta ^ n)) with ((beta * beta) * beta ^ n) by ring.
      rewrite alpha_sq, beta_sq.
      ring.
Qed.

Lemma beta_bounds : 0 < beta < 1.
Proof.
  unfold beta.
  pose proof (sqrt_pos 17).
  pose proof sqrt17_sq.
  nra.
Qed.

Lemma beta_pow_bounds : forall n : nat, 0 < beta ^ (S n) < 1.
Proof.
  induction n as [| n IH].
  - simpl. pose proof beta_bounds. lra.
  - remember (S n) as m. simpl.
    pose proof beta_bounds.
    nra.
Qed.

Lemma Zceil_eq : forall (r : R) (z : Z),
  IZR z - 1 < r <= IZR z -> Zceil r = z.
Proof.
  intros r z [H1 H2].
  unfold Zceil, Zfloor.
  destruct (archimed (- r)) as [Ha1 Ha2].
  assert (H3 : IZR (- z) < IZR (up (- r))).
  { rewrite opp_IZR. lra. }
  assert (H4 : IZR (up (- r)) < IZR (2 - z)).
  { rewrite minus_IZR. lra. }
  apply lt_IZR in H3.
  apply lt_IZR in H4.
  lia.
Qed.

Theorem ceil_pow_expr_odd : forall x : nat,
    Z.Odd (Zceil (((5 + sqrt 17) / 2) ^ x)).
Proof.
  destruct x as [| n].
  - simpl.
    replace (Zceil 1) with 1%Z.
    + exists 0%Z. lia.
    + symmetry. apply Zceil_eq. lra.
  - fold alpha.
    replace (Zceil (alpha ^ S n)) with (a_seq (S n)).
    + apply a_seq_odd.
    + symmetry. apply Zceil_eq.
      pose proof (proj2 (a_seq_eq n)) as Heq.
      pose proof (beta_pow_bounds n) as Hbeta.
      lra.
Qed.
```
