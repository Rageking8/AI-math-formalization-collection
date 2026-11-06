# GPT‑6 Astra Max (Arena AI)

Model: `gpt-6-astra-max` (via Arena AI)\
Date: `6 November 2026`\
Line count: `71`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals Psatz.
Open Scope R_scope.

Theorem sin_mul_upper_bound : forall x y z : R,
    x + y + z = PI ->
      sin x * sin y * sin z <= 3 * sqrt 3 / 8.
Proof.
  intros x y z Hsum.
  assert (Hsqrt_pos : 0 < sqrt 3).
  { apply sqrt_lt_R0; lra. }
  assert (Hsqrt_sq : sqrt 3 * sqrt 3 = 3).
  { apply sqrt_sqrt; lra. }

  (* A sharp bound on the unit circle. *)
  assert (Hunit : forall s c : R,
      s ^ 2 + c ^ 2 = 1 ->
      4 * s * (1 + c) <= 3 * sqrt 3).
  {
    intros s c Hsc.
    pose proof (Rle_0_sqr (sqrt 3 * s - c - 1)) as H1.
    pose proof (Rle_0_sqr (2 * c - 1)) as H2.
    unfold Rsqr in H1, H2.
    assert (Hsq : (sqrt 3 * s) ^ 2 = 3 * s ^ 2).
    {
      replace ((sqrt 3 * s) ^ 2)
        with ((sqrt 3 * sqrt 3) * s ^ 2) by ring.
      now rewrite Hsqrt_sq.
    }
    apply (Rmult_le_reg_l (sqrt 3)); [exact Hsqrt_pos |].
    nra.
  }

  assert (Hcircle : sin z ^ 2 + cos z ^ 2 = 1).
  {
    pose proof (sin2_cos2 z) as H.
    unfold Rsqr in H.
    nra.
  }

  assert (Hprod :
      2 * sin x * sin y * sin z =
      sin z * (cos (x - y) + cos z)).
  {
    assert (Hcos : cos z = - cos (x + y)).
    {
      replace z with (PI - (x + y)) by lra.
      rewrite cos_minus, cos_PI, sin_PI.
      ring.
    }
    rewrite Hcos, cos_minus, cos_plus.
    ring.
  }

  destruct (COS_bound (x - y)) as [Hdlo Hdhi].
  destruct (Rle_dec 0 (sin z)) as [Hs | Hs].
  - pose proof (Hunit (sin z) (cos z) Hcircle) as Hb.
    assert (Hm : sin z * cos (x - y) <= sin z * 1).
    {
      apply Rmult_le_compat_l; assumption.
    }
    nra.
  - assert (Hcircle' : (- sin z) ^ 2 + (- cos z) ^ 2 = 1)
      by nra.
    pose proof (Hunit (- sin z) (- cos z) Hcircle') as Hb.
    assert (Hm :
        (- sin z) * (-1) <= (- sin z) * cos (x - y)).
    {
      apply Rmult_le_compat_l; lra.
    }
    nra.
Qed.
```
