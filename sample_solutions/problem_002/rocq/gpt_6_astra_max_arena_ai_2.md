# GPT‑6 Astra Max (Arena AI)

Model: `gpt-6-astra-max` (via Arena AI)\
Date: `6 November 2026`\
Line count: `64`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals Lra Psatz.
Open Scope R_scope.

Theorem sin_mul_upper_bound : forall x y z : R,
    x + y + z = PI ->
      sin x * sin y * sin z <= 3 * sqrt 3 / 8.
Proof.
  intros x y z Hxyz.
  set (r := sqrt 3).
  assert (Hr2 : r * r = 3).
  { unfold r. apply sqrt_def. lra. }
  assert (Hrpos : 0 < r).
  { pose proof (sqrt_pos 3) as Hr.
    change (0 <= r) in Hr.
    nra. }

  (* A sharp bound on the unit circle. *)
  assert (Hcircle : forall a b : R,
      a * a + b * b = 1 -> a * (1 + b) <= 3 * r / 4).
  {
    intros a b Hab.
    apply (Rmult_le_reg_l r); [exact Hrpos |].
    replace (r * (3 * r / 4)) with (9 / 4) by nra.
    pose proof (Rle_0_sqr (r * a - (1 + b))) as H1.
    pose proof (Rle_0_sqr (b - 1 / 2)) as H2.
    unfold Rsqr in H1, H2.
    assert (Hra : r * r * (a * a) = 3 * (a * a)).
    { now rewrite Hr2. }
    nra.
  }

  assert (Hz : sin z * sin z + cos z * cos z = 1).
  { pose proof (sin2_cos2 z) as H.
    unfold Rsqr in H.
    nra. }
  pose proof (COS_bound (x - y)) as [Hcl Hcu].

  assert (Hprod :
      2 * (sin x * sin y) = cos (x - y) + cos z).
  {
    replace z with (PI - (x + y)) by lra.
    rewrite !cos_minus, cos_plus, cos_PI, sin_PI.
    ring.
  }
  pose proof
    (f_equal (fun t : R => t * sin z) Hprod) as Hprod_z.

  destruct (Rle_dec 0 (sin z)) as [Hs | Hs].
  - pose proof (Hcircle (sin z) (cos z) Hz) as Hu.
    assert (Hcmp :
        sin z * (cos (x - y) + cos z) <=
        sin z * (1 + cos z)).
    { apply Rmult_le_compat_l; lra. }
    nra.
  - assert (Hz' :
        (- sin z) * (- sin z) + (- cos z) * (- cos z) = 1)
      by nra.
    pose proof (Hcircle (- sin z) (- cos z) Hz') as Hu.
    assert (Hcmp :
        (- sin z) * (- (cos (x - y) + cos z)) <=
        (- sin z) * (1 + (- cos z))).
    { apply Rmult_le_compat_l; lra. }
    nra.
Qed.
```
