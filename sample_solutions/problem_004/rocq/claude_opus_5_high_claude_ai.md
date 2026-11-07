# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `7 November 2026`\
Line count: `75`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals.
Open Scope R_scope.

Theorem log_abs_sum_lower_bound (x y : R) (hx : 0 < x) (hy : 0 < y) :
    Rabs (ln x) + Rabs (ln y) >= 2 * ln ((x + y) / (2 * sqrt (x * y))).
Proof.
  assert (H4 : (0:R) < 4).
  { replace 4 with (2 * 2) by ring. apply Rmult_lt_0_compat; apply Rlt_0_2. }
  (* non-strict monotonicity of ln *)
  assert (Hmono : forall u v : R, 0 < u -> u <= v -> ln u <= ln v).
  { intros u v Hu Huv. destruct Huv as [Hlt | Heq].
    - left. apply ln_increasing; assumption.
    - rewrite Heq. apply Rle_refl. }
  (* the ordered case  b <= a *)
  assert (key : forall a b : R, 0 < a -> 0 < b -> b <= a ->
      2 * ln ((a + b) / (2 * sqrt (a * b))) <= Rabs (ln a) + Rabs (ln b)).
  { intros a b Ha Hb Hba.
    assert (Hane : a <> 0) by (apply Rgt_not_eq; assumption).
    assert (Hbne : b <> 0) by (apply Rgt_not_eq; assumption).
    assert (Hab : 0 < a * b) by (apply Rmult_lt_0_compat; assumption).
    assert (Hs : 0 < sqrt (a * b)) by (apply sqrt_lt_R0; assumption).
    assert (Hss : sqrt (a * b) * sqrt (a * b) = a * b)
      by (apply sqrt_sqrt; left; assumption).
    assert (Hsne : sqrt (a * b) <> 0) by (apply Rgt_not_eq; assumption).
    assert (Hsum : 0 < a + b) by (apply Rplus_lt_0_compat; assumption).
    assert (Hden : 0 < 2 * sqrt (a * b))
      by (apply Rmult_lt_0_compat; [apply Rlt_0_2 | assumption]).
    set (A := (a + b) / (2 * sqrt (a * b))).
    assert (HA : 0 < A) by (unfold A; apply Rdiv_lt_0_compat; assumption).
    assert (HAA : 0 < A * A) by (apply Rmult_lt_0_compat; assumption).
    (* A^2 = (a+b)^2 / (4ab) *)
    assert (E : A * A
                = (a + b) * (a + b) / (4 * (sqrt (a * b) * sqrt (a * b)))).
    { unfold A. field. assumption. }
    rewrite Hss in E.
    (* A^2 <= a/b, because (a+b)^2 <= 4a^2 when b <= a *)
    assert (Hle : A * A <= a / b).
    { rewrite E.
      apply Rmult_le_reg_r with (r := 4 * (a * b)).
      - apply Rmult_lt_0_compat; assumption.
      - assert (E1 : (a + b) * (a + b) / (4 * (a * b)) * (4 * (a * b))
                     = (a + b) * (a + b)) by (field; split; assumption).
        assert (E2 : a / b * (4 * (a * b)) = (2 * a) * (2 * a))
          by (field; assumption).
        rewrite E1, E2.
        apply Rmult_le_compat.
        + left; assumption.
        + left; assumption.
        + replace (2 * a) with (a + a) by ring.
          apply Rplus_le_compat_l; assumption.
        + replace (2 * a) with (a + a) by ring.
          apply Rplus_le_compat_l; assumption. }
    (* ln (a/b) = ln a - ln b *)
    assert (Hdiv : ln (a / b) = ln a - ln b).
    { unfold Rdiv. rewrite ln_mult.
      - rewrite ln_Rinv by assumption. ring.
      - assumption.
      - apply Rinv_0_lt_compat; assumption. }
    (* chain everything *)
    apply Rle_trans with (r2 := ln (A * A)).
    - rewrite ln_mult by assumption. right; ring.
    - apply Rle_trans with (r2 := ln a - ln b).
      + rewrite <- Hdiv. apply Hmono; assumption.
      + unfold Rminus. apply Rplus_le_compat.
        * apply Rle_abs.
        * rewrite <- (Rabs_Ropp (ln b)). apply Rle_abs. }
  (* reduce the general case to the ordered one by symmetry *)
  destruct (Rle_or_lt y x) as [Hyx | Hxy].
  - apply Rle_ge. apply key; assumption.
  - apply Rle_ge.
    rewrite (Rplus_comm (Rabs (ln x)) (Rabs (ln y))).
    rewrite (Rplus_comm x y).
    rewrite (Rmult_comm x y).
    apply key; [assumption | assumption | left; assumption].
Qed.
```
