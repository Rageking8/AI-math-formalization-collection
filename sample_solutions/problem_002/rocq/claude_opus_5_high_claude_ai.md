# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `4 November 2026`\
Line count: `81`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

Theorem sin_mul_upper_bound : forall x y z : R,
    x + y + z = PI ->
      sin x * sin y * sin z <= 3 * sqrt 3 / 8.
Proof.
  (* squares are nonnegative *)
  assert (sqr_nonneg : forall t : R, 0 <= t * t).
  { intros t. destruct (Rle_or_lt 0 t) as [Ht | Ht].
    - apply Rmult_le_pos; assumption.
    - replace (t * t) with ((- t) * (- t)) by ring.
      apply Rmult_le_pos; lra. }
  (* on nonnegatives, squaring reflects the order *)
  assert (sqr_le_inv : forall a b : R, 0 <= a -> 0 <= b -> a * a <= b * b -> a <= b).
  { intros a b Ha Hb Hab.
    destruct (Rle_or_lt a b) as [Hle | Hlt]; [ exact Hle | exfalso ].
    assert (Hba : b * b < a * a).
    { apply Rle_lt_trans with (b * a).
      - apply Rmult_le_compat_l; lra.
      - apply Rmult_lt_compat_r; lra. }
    lra. }
  (* key bound: on the unit circle, (1 + K) * S <= 3 * sqrt 3 / 4 *)
  assert (key : forall K S : R, 0 <= S -> K * K + S * S = 1 ->
                (1 + K) * S <= 3 * sqrt 3 / 4).
  { intros K S HS HKS.
    assert (Hs3 : sqrt 3 * sqrt 3 = 3) by (apply sqrt_sqrt; lra).
    assert (Hs3p : 0 <= sqrt 3) by apply sqrt_pos.
    assert (HSS : 0 <= S * S) by apply sqr_nonneg.
    assert (HK : -1 <= K).
    { destruct (Rle_or_lt (-1) K) as [HH | HH]; [ exact HH | exfalso ].
      assert (1 * 1 < (- K) * (- K)).
      { apply Rle_lt_trans with (1 * (- K)).
        - apply Rmult_le_compat_l; lra.
        - apply Rmult_lt_compat_r; lra. }
      lra. }
    apply sqr_le_inv.
    - apply Rmult_le_pos; lra.
    - lra.
    - assert (HR : 3 * sqrt 3 / 4 * (3 * sqrt 3 / 4) = 27 / 16).
      { replace (3 * sqrt 3 / 4 * (3 * sqrt 3 / 4))
          with (9 * (sqrt 3 * sqrt 3) / 16) by field.
        rewrite Hs3. lra. }
      rewrite HR.
      replace ((1 + K) * S * ((1 + K) * S))
        with ((1 + K) * (1 + K) * (S * S)) by ring.
      replace (S * S) with (1 - K * K) by lra.
      (* 27/16 - (1+K)^2*(1-K^2) = (2K-1)^2*((2K+3)^2+2) / 16 *)
      assert (H1 : 0 <= (2 * K - 1) * (2 * K - 1)) by apply sqr_nonneg.
      assert (H2 : 0 <= (2 * K + 3) * (2 * K + 3)) by apply sqr_nonneg.
      assert (H3 : 0 <= (2 * K - 1) * (2 * K - 1) * ((2 * K + 3) * (2 * K + 3) + 2)).
      { apply Rmult_le_pos; lra. }
      lra. }
  intros x y z H.
  destruct (COS_bound (x - y)) as [Hc1 Hc2].
  assert (Hsc : cos z * cos z + sin z * sin z = 1).
  { pose proof (cos_minus z z) as Hz.
    replace (z - z) with 0 in Hz by ring.
    rewrite cos_0 in Hz. lra. }
  (* product-to-sum: sin x * sin y = (cos (x - y) + cos z) / 2 *)
  assert (Hprod : sin x * sin y = (cos (x - y) + cos z) / 2).
  { pose proof (cos_minus x y) as E1.
    pose proof (cos_plus x y) as E2.
    assert (E3 : cos (x + y) = - cos z).
    { replace (x + y) with (PI - z) by lra.
      rewrite cos_minus, cos_PI, sin_PI. ring. }
    lra. }
  rewrite Hprod.
  destruct (Rle_or_lt 0 (sin z)) as [Hs | Hs].
  - pose proof (key (cos z) (sin z) Hs Hsc) as HKey.
    assert (Hstep : (cos (x - y) + cos z) * sin z <= (1 + cos z) * sin z).
    { apply Rmult_le_compat_r; lra. }
    lra.
  - assert (HA : 0 <= - sin z) by lra.
    assert (HB : (- cos z) * (- cos z) + (- sin z) * (- sin z) = 1) by lra.
    pose proof (key (- cos z) (- sin z) HA HB) as HKey.
    assert (Hstep : sin z * (cos (x - y) + cos z) <= sin z * (-1 + cos z)).
    { apply Rmult_le_compat_neg_l; lra. }
    lra.
Qed.
```
