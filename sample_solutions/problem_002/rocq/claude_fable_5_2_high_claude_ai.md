# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `10 November 2026`\
Line count: `75`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals.
Open Scope R_scope.

Theorem sin_mul_upper_bound : forall x y z : R,
    x + y + z = PI ->
      sin x * sin y * sin z <= 3 * sqrt 3 / 8.
Proof.
  intros x y z H.
  assert (H3 : 0 <= 3) by (apply Rlt_le; prove_sup0).
  assert (Ht : sqrt 3 * sqrt 3 = 3) by (apply sqrt_sqrt; exact H3).
  assert (Ht0 : 0 < sqrt 3) by (apply sqrt_lt_R0; prove_sup0).
  set (t := sqrt 3) in *.
  (* Key algebraic fact: on the unit circle, (1 - c) * s <= 3 sqrt 3 / 4. *)
  assert (aux : forall s c, s * s + c * c = 1 -> (1 - c) * s <= 3 * t / 4).
  { intros s c Hsc.
    destruct (Rle_or_lt ((1 - c) * s) (3 * t / 4)) as [Hle | Hgt]; [exact Hle |].
    exfalso.
    assert (Hpos : 0 < 3 * t / 4).
    { apply Rdiv_lt_0_compat; [apply Rmult_lt_0_compat; [prove_sup0 | exact Ht0] | prove_sup0]. }
    assert (Hsq : (3 * t / 4) * (3 * t / 4) < ((1 - c) * s) * ((1 - c) * s)).
    { apply Rmult_le_0_lt_compat; try (apply Rlt_le; exact Hpos); exact Hgt. }
    assert (Hid : ((1 - c) * s) * ((1 - c) * s)
                  = (3 * t / 4) * (3 * t / 4)
                    - ((1 - c) - 3 / 2) * ((1 - c) - 3 / 2)
                      * (((1 - c) + 1 / 2) * ((1 - c) + 1 / 2) + 1 / 2)).
    { replace ((3 * t / 4) * (3 * t / 4)) with (9 / 16 * (t * t)) by field.
      rewrite Ht.
      replace (((1 - c) * s) * ((1 - c) * s))
        with ((1 - c) * (1 - c) * (s * s)) by ring.
      replace (s * s) with (1 - c * c)
        by (rewrite <- Hsc; ring).
      field. }
    assert (Hnn : 0 <= ((1 - c) - 3 / 2) * ((1 - c) - 3 / 2)
                       * (((1 - c) + 1 / 2) * ((1 - c) + 1 / 2) + 1 / 2)).
    { apply Rmult_le_pos.
      - apply Rle_0_sqr.
      - apply Rplus_le_le_0_compat.
        + apply Rle_0_sqr.
        + apply Rlt_le. apply Rdiv_lt_0_compat; prove_sup0. }
    rewrite Hid in Hsq.
    apply (Rlt_irrefl (3 * t / 4 * (3 * t / 4))).
    eapply Rlt_le_trans; [exact Hsq |].
    rewrite <- (Rminus_0_r (3 * t / 4 * (3 * t / 4))) at 2.
    apply Rplus_le_compat_l.
    apply Ropp_le_contravar. exact Hnn. }
  (* Reduce to the two variables x, y. *)
  assert (Hz : z = PI - (x + y)) by (rewrite <- H; ring).
  rewrite Hz, sin_PI_x.
  assert (Hprod : sin x * sin y = (cos (x - y) - cos (x + y)) / 2).
  { rewrite cos_minus, cos_plus. field. }
  rewrite Hprod.
  destruct (COS_bound (x - y)) as [Hd1 Hd2].
  assert (Hsc : sin (x + y) * sin (x + y) + cos (x + y) * cos (x + y) = 1)
    by (apply (sin2_cos2 (x + y))).
  set (D := cos (x - y)) in *.
  set (S := sin (x + y)) in *.
  set (C := cos (x + y)) in *.
  replace ((D - C) / 2 * S) with ((D - C) * S * / 2) by field.
  replace (3 * t / 8) with (3 * t / 4 * / 2) by field.
  apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; prove_sup0 |].
  destruct (Rle_or_lt 0 S) as [HS | HS].
  - (* S >= 0: use D <= 1 *)
    apply Rle_trans with ((1 - C) * S).
    + apply Rmult_le_compat_r; [exact HS |].
      apply Rplus_le_compat_r. exact Hd2.
    + apply aux. exact Hsc.
  - (* S < 0: use -1 <= D *)
    apply Rle_trans with ((1 - (- C)) * (- S)).
    + replace ((D - C) * S) with ((C - D) * (- S)) by ring.
      apply Rmult_le_compat_r.
      * apply Rlt_le, Ropp_0_gt_lt_contravar. exact HS.
      * replace (1 - - C) with (C - (-1)) by ring.
        apply Rplus_le_compat_l. apply Ropp_le_contravar. exact Hd1.
    + apply aux. rewrite <- Hsc. ring.
Qed.
```
