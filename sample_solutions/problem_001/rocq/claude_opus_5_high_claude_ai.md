# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `31 October 2026`\
Line count: `88`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals ZArith.
Open Scope R_scope.

From Stdlib Require Import Lra Lia.   (* Lra gives lra and nra; Lia gives lia *)

Fixpoint A (n : nat) : Z :=
  match n with
  | O => 2%Z
  | S m => match m with
           | O => 5%Z
           | S k => (5 * A m - 2 * A k)%Z
           end
  end.

Definition alpha : R := (5 + sqrt 17) / 2.
Definition beta  : R := (5 - sqrt 17) / 2.

Lemma sqrt17_sqr : sqrt 17 * sqrt 17 = 17.
Proof. apply sqrt_sqrt; lra. Qed.

Lemma sqrt17_bounds : 4 < sqrt 17 < 5.
Proof.
assert (H0 := sqrt_pos 17). assert (H1 := sqrt17_sqr). split; nra.
Qed.

Lemma beta_bounds : 0 < beta < 1.
Proof. unfold beta. generalize sqrt17_bounds; lra. Qed.

Lemma alpha_quad : alpha * alpha = 5 * alpha - 2.
Proof. unfold alpha. generalize sqrt17_sqr; intros; nra. Qed.

Lemma beta_quad : beta * beta = 5 * beta - 2.
Proof. unfold beta. generalize sqrt17_sqr; intros; nra. Qed.

Lemma A_spec_pair :
  forall n, alpha ^ n + beta ^ n = IZR (A n)
         /\ alpha ^ (S n) + beta ^ (S n) = IZR (A (S n)).
Proof.
induction n as [| n [IH1 IH2]].
- split.
  + simpl. ring.
  + simpl. unfold alpha, beta. lra.
- split; [exact IH2 | ].
  assert (Hrec : A (S (S n)) = (5 * A (S n) - 2 * A n)%Z) by reflexivity.
  assert (Ea : alpha ^ (S (S n)) = 5 * alpha ^ (S n) - 2 * alpha ^ n).
  { rewrite <- !tech_pow_Rmult.
    replace (alpha * (alpha * alpha ^ n)) with (alpha * alpha * alpha ^ n) by ring.
    rewrite alpha_quad; ring. }
  assert (Eb : beta ^ (S (S n)) = 5 * beta ^ (S n) - 2 * beta ^ n).
  { rewrite <- !tech_pow_Rmult.
    replace (beta * (beta * beta ^ n)) with (beta * beta * beta ^ n) by ring.
    rewrite beta_quad; ring. }
  rewrite Hrec, minus_IZR, !mult_IZR, <- IH1, <- IH2, Ea, Eb. ring.
Qed.

Lemma A_spec : forall n, alpha ^ n + beta ^ n = IZR (A n).
Proof. intro n; apply (A_spec_pair n). Qed.

Lemma A_odd : forall n, Z.Odd (A (S n)).
Proof.
induction n as [| n [k Hk]].
- exists 2%Z; reflexivity.
- assert (Hrec : A (S (S n)) = (5 * A (S n) - 2 * A n)%Z) by reflexivity.
  exists (5 * k + 2 - A n)%Z. rewrite Hrec, Hk; ring.
Qed.

Lemma beta_pow_bounds : forall n, 0 < beta ^ (S n) < 1.
Proof.
intro n; split.
- apply pow_lt, beta_bounds.
- apply pow_lt_1_compat; [ generalize beta_bounds; lra | lia ].
Qed.

Lemma Zceil_alpha_pow : forall n, Zceil (alpha ^ (S n)) = A (S n).
Proof.
intro n; apply Zceil_eq.
generalize (A_spec (S n)); generalize (beta_pow_bounds n); lra.
Qed.

Theorem ceil_pow_expr_odd : forall x : nat,
    Z.Odd (Zceil (((5 + sqrt 17) / 2) ^ x)).
Proof.
intro x.
replace ((5 + sqrt 17) / 2) with alpha by reflexivity.
destruct x as [| n].
- rewrite (Zceil_eq 1%Z); [ exists 0%Z; reflexivity | ]. simpl; lra.
- rewrite Zceil_alpha_pow. apply A_odd.
Qed.
```
