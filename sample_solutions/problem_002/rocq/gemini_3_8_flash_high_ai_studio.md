# Gemini 3.8 Flash High (AI Studio)

Model: `Gemini 3.8 Flash High` (via AI Studio)\
Date: `4 November 2026`\
Line count: `95`\
Turn count: `2`

## Solution

```rocq
From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

Theorem sin_mul_upper_bound : forall x y z : R,
    x + y + z = PI ->
      sin x * sin y * sin z <= 3 * sqrt 3 / 8.
Proof.
  assert (sin_pos_bound : forall u v w : R,
            u + v + w = PI ->
            0 <= sin w ->
            sin u * sin v * sin w <= 3 * sqrt 3 / 8).
  {
    intros u v w Hsum Hw.
    destruct (COS_bound (u - v)) as [_ Hcos_uv].
    destruct (COS_bound w) as [Hcos_w _].
    assert (Huv : u + v = PI - w) by (rewrite <- Hsum; ring).
    assert (Hcos_uv_w : cos (u + v) = - cos w).
    { rewrite Huv, cos_minus, cos_PI, sin_PI; ring. }
    assert (Hdiff : 4 * sin w * (1 + cos w) - 8 * (sin u * sin v * sin w) =
                    4 * sin w * (1 - cos (u - v))).
    { assert (Hstep : 4 * sin w * (1 + cos w) - 8 * (sin u * sin v * sin w) =
                      4 * sin w * (1 - cos (u - v)) + 4 * sin w * (cos (u + v) + cos w)).
      { rewrite cos_minus, cos_plus; ring. }
      rewrite Hstep, Hcos_uv_w; ring. }
    assert (Hle1 : 8 * (sin u * sin v * sin w) <= 4 * sin w * (1 + cos w)).
    { assert (Hge : 0 <= 4 * sin w * (1 - cos (u - v))).
      { apply Rmult_le_pos; lra. }
      lra. }
    assert (Hsqrt3_pos : 0 <= sqrt 3) by apply sqrt_pos.
    assert (Hsqrt3_sq : sqrt 3 * sqrt 3 = 3) by (apply sqrt_sqrt; lra).
    assert (H3sqrt3_sq : (3 * sqrt 3) * (3 * sqrt 3) = 27).
    { assert (Hstep : (3 * sqrt 3) * (3 * sqrt 3) = 9 * (sqrt 3 * sqrt 3)) by ring.
      rewrite Hstep, Hsqrt3_sq; ring. }
    assert (Htrig : sin w * sin w + cos w * cos w = 1).
    { transitivity (Rsqr (sin w) + Rsqr (cos w)).
      - unfold Rsqr; ring.
      - apply sin2_cos2. }
    assert (HM_sq_id : (4 * sin w * (1 + cos w)) * (4 * sin w * (1 + cos w)) =
                       16 * (1 - cos w) * (1 + cos w) * (1 + cos w) * (1 + cos w) +
                       16 * (sin w * sin w + cos w * cos w - 1) * (1 + cos w) * (1 + cos w)) by ring.
    assert (Halg_id : 27 - 16 * (1 - cos w) * (1 + cos w) * (1 + cos w) * (1 + cos w) =
                      ((2 * cos w - 1) * (2 * cos w + 3)) * ((2 * cos w - 1) * (2 * cos w + 3)) +
                      2 * ((2 * cos w - 1) * (2 * cos w - 1))) by ring.
    assert (HM_sq : (4 * sin w * (1 + cos w)) * (4 * sin w * (1 + cos w)) <= 27).
    { rewrite HM_sq_id, Htrig.
      assert (Halg_ge : 0 <= 27 - 16 * (1 - cos w) * (1 + cos w) * (1 + cos w) * (1 + cos w)).
      { rewrite Halg_id.
        pose proof (Rle_0_sqr ((2 * cos w - 1) * (2 * cos w + 3))) as Hsq1.
        pose proof (Rle_0_sqr (2 * cos w - 1)) as Hsq2.
        unfold Rsqr in Hsq1, Hsq2.
        lra. }
      lra. }
    assert (Hle2 : 4 * sin w * (1 + cos w) <= 3 * sqrt 3).
    { destruct (Rle_or_lt (4 * sin w * (1 + cos w)) (3 * sqrt 3)) as [Hle | Hlt].
      - exact Hle.
      - exfalso.
        assert (Hcontra : 27 < (4 * sin w * (1 + cos w)) * (4 * sin w * (1 + cos w))).
        { assert (Hdiff_pos : 0 < (4 * sin w * (1 + cos w) - 3 * sqrt 3) * (4 * sin w * (1 + cos w) + 3 * sqrt 3)).
          { apply Rmult_lt_0_compat; lra. }
          assert (Hid : (4 * sin w * (1 + cos w)) * (4 * sin w * (1 + cos w)) - (3 * sqrt 3) * (3 * sqrt 3) =
                        (4 * sin w * (1 + cos w) - 3 * sqrt 3) * (4 * sin w * (1 + cos w) + 3 * sqrt 3)) by ring.
          rewrite H3sqrt3_sq in Hid.
          lra. }
        lra. }
    lra.
  }
  intros x y z Hsum.
  destruct (Rle_lt_dec 0 (sin z)) as [Hz | Hz].
  - apply (sin_pos_bound x y z Hsum Hz).
  - destruct (Rle_lt_dec 0 (sin x)) as [Hx | Hx].
    + replace (sin x * sin y * sin z) with (sin y * sin z * sin x) by ring.
      apply sin_pos_bound.
      * rewrite <- Hsum; ring.
      * exact Hx.
    + destruct (Rle_lt_dec 0 (sin y)) as [Hy | Hy].
      * replace (sin x * sin y * sin z) with (sin x * sin z * sin y) by ring.
        apply sin_pos_bound.
        -- rewrite <- Hsum; ring.
        -- exact Hy.
      * assert (Hpos : 0 <= sin x * sin y).
        { assert (Hstep : 0 < (- sin x) * (- sin y)).
          { apply Rmult_lt_0_compat; lra. }
          assert (Hid : (- sin x) * (- sin y) = sin x * sin y) by ring.
          rewrite Hid in Hstep.
          lra. }
        assert (Hneg : sin x * sin y * sin z <= 0).
        { assert (Hstep : 0 <= (sin x * sin y) * (- sin z)).
          { apply Rmult_le_pos; lra. }
          assert (Hid : (sin x * sin y) * (- sin z) = - (sin x * sin y * sin z)) by ring.
          rewrite Hid in Hstep.
          lra. }
        assert (Hsqrt : 0 <= sqrt 3) by apply sqrt_pos.
        lra.
Qed.
```
