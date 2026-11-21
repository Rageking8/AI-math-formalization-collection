# Gemini 4 Hydrogen High (AI Studio)

Model: `Gemini 4 Hydrogen High` (via AI Studio)\
Date: `21 November 2026`\
Line count: `72`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals.
Open Scope R_scope.

Theorem log_abs_sum_lower_bound (x y : R) (hx : 0 < x) (hy : 0 < y) :
    Rabs (ln x) + Rabs (ln y) >= 2 * ln ((x + y) / (2 * sqrt (x * y))).
Proof.
  apply Rle_ge.
  assert (Hln_le : forall a b, 0 < a -> a <= b -> ln a <= ln b).
  { intros a b Ha Hab.
    destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | Heq].
    - apply Rlt_le, ln_increasing; assumption.
    - rewrite Heq; apply Rle_refl. }
  assert (Hmain : forall u v, 0 < u -> 0 < v -> v <= u ->
    2 * ln ((u + v) / (2 * sqrt (u * v))) <= ln u - ln v).
  { intros u v Hu Hv Hvu.
    assert (H2 : 0 < 2) by (apply (IZR_lt 0%Z 2%Z); reflexivity).
    assert (H3 : 0 < 3) by (apply (IZR_lt 0%Z 3%Z); reflexivity).
    assert (H4 : 0 < 4) by (apply (IZR_lt 0%Z 4%Z); reflexivity).
    assert (Huv : 0 < u * v) by (apply Rmult_lt_0_compat; assumption).
    assert (Hspos : 0 < sqrt (u * v)) by (apply sqrt_lt_R0; assumption).
    assert (Hs : sqrt (u * v) * sqrt (u * v) = u * v).
    { apply sqrt_sqrt, Rlt_le; assumption. }
    assert (HApos : 0 < (u + v) / (2 * sqrt (u * v))).
    { apply Rdiv_lt_0_compat.
      - apply Rplus_lt_0_compat; assumption.
      - apply Rmult_lt_0_compat; assumption. }
    replace (2 * ln ((u + v) / (2 * sqrt (u * v))))
      with (ln (((u + v) * (u + v)) / (4 * (u * v)))).
    2: {
      replace (((u + v) * (u + v)) / (4 * (u * v)))
        with (((u + v) / (2 * sqrt (u * v))) * ((u + v) / (2 * sqrt (u * v)))).
      - rewrite ln_mult; [ring | assumption | assumption].
      - transitivity (((u + v) * (u + v)) / (4 * (sqrt (u * v) * sqrt (u * v)))).
        + field; repeat split; apply Rgt_not_eq, Rlt_gt; repeat apply Rmult_lt_0_compat; assumption.
        + rewrite Hs; reflexivity.
    }
    replace (ln u - ln v) with (ln (u / v)).
    2: {
      unfold Rdiv.
      rewrite ln_mult; [| assumption | apply Rinv_0_lt_compat; assumption].
      rewrite ln_Rinv; [ring | assumption].
    }
    apply Hln_le.
    - apply Rdiv_lt_0_compat.
      + apply Rmult_lt_0_compat; apply Rplus_lt_0_compat; assumption.
      + apply Rmult_lt_0_compat; assumption.
    - apply Rminus_le.
      replace (((u + v) * (u + v)) / (4 * (u * v)) - u / v)
        with (- (((u - v) * (3 * u + v)) / (4 * (u * v)))).
      2: { field; repeat split; apply Rgt_not_eq, Rlt_gt; repeat apply Rmult_lt_0_compat; assumption. }
      rewrite <- Ropp_0; apply Ropp_le_contravar.
      unfold Rdiv.
      apply Rmult_le_pos.
      + apply Rmult_le_pos.
        * apply Rge_le, Rge_minus, Rle_ge; assumption.
        * apply Rlt_le, Rplus_lt_0_compat; [apply Rmult_lt_0_compat; assumption | assumption].
      + apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; assumption. }
  assert (Habs : forall u v, ln u - ln v <= Rabs (ln u) + Rabs (ln v)).
  { intros u v.
    unfold Rminus.
    rewrite <- (Rabs_Ropp (ln v)).
    apply Rplus_le_compat; apply Rle_abs. }
  destruct (Rle_lt_dec x y) as [Hxy | Hyx].
  - replace ((x + y) / (2 * sqrt (x * y))) with ((y + x) / (2 * sqrt (y * x))).
    + eapply Rle_trans.
      * apply Hmain; assumption.
      * rewrite Rplus_comm; apply Habs.
    + rewrite (Rplus_comm x y), (Rmult_comm x y); reflexivity.
  - eapply Rle_trans.
    + apply Hmain; [assumption | assumption | apply Rlt_le; assumption].
    + apply Habs.
Qed.
```
