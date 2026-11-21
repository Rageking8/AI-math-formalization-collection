# Gemini 4 Hydrogen High (AI Studio)

Model: `Gemini 4 Hydrogen High` (via AI Studio)\
Date: `21 November 2026`\
Line count: `104`\
Turn count: `3`

## Solution

```rocq
From Stdlib Require Import Reals.
Open Scope R_scope.

Theorem sin_mul_upper_bound : forall x y z : R,
    x + y + z = PI ->
      sin x * sin y * sin z <= 3 * sqrt 3 / 8.
Proof.
  intros x y z Hxyz.
  assert (H01 : 0 < 1) by exact Rlt_0_1.
  assert (H02 : 0 < 2) by exact Rlt_R0_R2.
  assert (H03 : 0 < 3) by (replace 3 with (1 + 2) by ring; apply Rplus_lt_0_compat; assumption).
  assert (H04 : 0 < 4) by (replace 4 with (2 * 2) by ring; apply Rmult_lt_0_compat; assumption).
  assert (H08 : 0 < 8) by (replace 8 with (2 * 4) by ring; apply Rmult_lt_0_compat; assumption).
  assert (H016 : 0 < 16) by (replace 16 with (4 * 4) by ring; apply Rmult_lt_0_compat; assumption).
  assert (H064 : 0 < 64) by (replace 64 with (8 * 8) by ring; apply Rmult_lt_0_compat; assumption).
  apply Rsqr_incr_0_var.
  - assert (Hz : z = PI - (x + y)) by (rewrite <- Hxyz; ring).
    assert (Hsinz : sin z = sin (x + y)) by (rewrite Hz, sin_minus, sin_PI, cos_PI; ring).
    rewrite Hsinz.
    assert (Hsinxy : sin x * sin y = (cos (x - y) - cos (x + y)) / 2).
    { rewrite cos_minus, cos_plus.
      unfold Rdiv.
      transitivity ((sin x * sin y) * (2 * / 2)).
      + rewrite Rinv_r by (apply Rgt_not_eq; exact H02). ring.
      + ring. }
    rewrite Hsinxy.
    apply (Rmult_le_reg_l 64); [exact H064 | ].
    assert (Hlhs : 64 * Rsqr ((cos (x - y) - cos (x + y)) / 2 * sin (x + y)) =
                   16 * Rsqr (cos (x - y) - cos (x + y)) * Rsqr (sin (x + y))).
    { unfold Rsqr, Rdiv.
      transitivity (16 * ((cos (x - y) - cos (x + y)) * (cos (x - y) - cos (x + y))) *
                    (sin (x + y) * sin (x + y)) * ((2 * / 2) * (2 * / 2))).
      + ring.
      + rewrite Rinv_r by (apply Rgt_not_eq; exact H02). ring. }
    assert (Hrhs : 64 * Rsqr (3 * sqrt 3 / 8) = 27).
    { unfold Rsqr, Rdiv.
      transitivity (9 * (sqrt 3 * sqrt 3) * ((8 * / 8) * (8 * / 8))).
      + ring.
      + rewrite Rinv_r by (apply Rgt_not_eq; exact H08).
        rewrite sqrt_def by (apply Rlt_le; exact H03).
        ring. }
    rewrite Hlhs, Hrhs.
    assert (Hu2 : Rsqr (cos (x - y)) <= 1).
    { pose proof (sin2_cos2 (x - y)) as Hsc.
      rewrite <- Hsc.
      rewrite <- (Rplus_0_l (Rsqr (cos (x - y)))) at 1.
      apply Rplus_le_compat_r, Rle_0_sqr. }
    assert (Hu_ub : cos (x - y) <= 1)
      by (apply Rsqr_incr_0_var; [rewrite Rsqr_1; exact Hu2 | apply Rle_0_1]).
    assert (Hu_lb : -1 <= cos (x - y)).
    { apply (Rsqr_neg_pos_le_0 (cos (x - y)) 1).
      - unfold Rsqr in Hu2 |- *.
        apply Rle_trans with (r2 := 1); [exact Hu2 | right; ring].
      - apply Rle_0_1. }
    assert (Hs2 : Rsqr (sin (x + y)) = 1 - Rsqr (cos (x + y)))
      by (pose proof (sin2_cos2 (x + y)) as Hsc; rewrite <- Hsc; ring).
    destruct (Rle_or_lt 0 (cos (x + y))) as [Ht | Ht].
    + assert (Hnt : - cos (x + y) <= cos (x + y)).
      { apply (Rplus_le_reg_r (cos (x + y))).
        rewrite Rplus_opp_l, <- (Rplus_0_l 0).
        apply Rplus_le_compat; exact Ht. }
      assert (Hsqr_bound : Rsqr (cos (x - y) - cos (x + y)) <= Rsqr (1 + cos (x + y))).
      { apply neg_pos_Rsqr_le.
        * replace (- (1 + cos (x + y))) with (-1 + - cos (x + y)) by ring.
          unfold Rminus. apply Rplus_le_compat_r; exact Hu_lb.
        * unfold Rminus. apply Rplus_le_compat; [exact Hu_ub | exact Hnt]. }
      apply Rle_trans with (r2 := 16 * Rsqr (1 + cos (x + y)) * Rsqr (sin (x + y))).
      * apply Rmult_le_compat_r; [apply Rle_0_sqr | ].
        apply Rmult_le_compat_l; [apply Rlt_le; exact H016 | exact Hsqr_bound].
      * rewrite Hs2.
        apply Rminus_le.
        replace (16 * Rsqr (1 + cos (x + y)) * (1 - Rsqr (cos (x + y))) - 27)
          with (- (Rsqr (2 * cos (x + y) - 1) * (Rsqr (2 * cos (x + y) + 3) + 2)))
          by (unfold Rsqr; ring).
        apply (Rplus_le_reg_r (Rsqr (2 * cos (x + y) - 1) * (Rsqr (2 * cos (x + y) + 3) + 2))).
        rewrite Rplus_opp_l, Rplus_0_l.
        apply Rmult_le_pos; [apply Rle_0_sqr | ].
        rewrite <- (Rplus_0_l 0).
        apply Rplus_le_compat; [apply Rle_0_sqr | apply Rlt_le; exact H02].
    + assert (Htn : cos (x + y) <= - cos (x + y)).
      { apply (Rplus_le_reg_r (cos (x + y))).
        rewrite Rplus_opp_l, <- (Rplus_0_l 0).
        apply Rplus_le_compat; apply Rlt_le; exact Ht. }
      assert (Hsqr_bound : Rsqr (cos (x - y) - cos (x + y)) <= Rsqr (1 - cos (x + y))).
      { apply neg_pos_Rsqr_le.
        * replace (- (1 - cos (x + y))) with (-1 + cos (x + y)) by ring.
          unfold Rminus. apply Rplus_le_compat; [exact Hu_lb | exact Htn].
        * unfold Rminus. apply Rplus_le_compat_r; exact Hu_ub. }
      apply Rle_trans with (r2 := 16 * Rsqr (1 - cos (x + y)) * Rsqr (sin (x + y))).
      * apply Rmult_le_compat_r; [apply Rle_0_sqr | ].
        apply Rmult_le_compat_l; [apply Rlt_le; exact H016 | exact Hsqr_bound].
      * rewrite Hs2.
        apply Rminus_le.
        replace (16 * Rsqr (1 - cos (x + y)) * (1 - Rsqr (cos (x + y))) - 27)
          with (- (Rsqr (2 * cos (x + y) + 1) * (Rsqr (2 * cos (x + y) - 3) + 2)))
          by (unfold Rsqr; ring).
        apply (Rplus_le_reg_r (Rsqr (2 * cos (x + y) + 1) * (Rsqr (2 * cos (x + y) - 3) + 2))).
        rewrite Rplus_opp_l, Rplus_0_l.
        apply Rmult_le_pos; [apply Rle_0_sqr | ].
        rewrite <- (Rplus_0_l 0).
        apply Rplus_le_compat; [apply Rle_0_sqr | apply Rlt_le; exact H02].
  - unfold Rdiv.
    apply Rle_mult_inv_pos; [apply Rmult_le_pos; [apply Rlt_le; exact H03 | apply sqrt_pos] | exact H08].
Qed.
```
