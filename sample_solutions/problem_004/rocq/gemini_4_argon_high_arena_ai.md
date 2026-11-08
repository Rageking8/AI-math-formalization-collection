# Gemini 4 Argon High (Arena AI)

Model: `gemini-4-argon-high` (via Arena AI)\
Date: `8 November 2026`\
Line count: `42`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals Lra Psatz.
Open Scope R_scope.

Lemma log_bound_ordered (u v : R) (hu : 0 < u) (hv : 0 < v) (hvu : v <= u) :
  2 * ln ((u + v) / (2 * sqrt (u * v))) <= ln u - ln v.
Proof.
  set (s := sqrt (u * v)).
  assert (Hs : 0 < s) by (unfold s; apply sqrt_lt_R0; nra).
  assert (Hs2 : s * s = u * v) by (unfold s; apply sqrt_sqrt; nra).
  clearbody s.
  set (A := (u + v) / (2 * s)).
  assert (HA1 : A * (2 * s) = u + v) by (unfold A; field; lra).
  assert (HA2 : A * A * (4 * (u * v)) = (u + v) * (u + v))
    by (rewrite <- Hs2; unfold A; field; lra).
  clearbody A.
  assert (HA : 0 < A) by nra.
  assert (HA_sq : 0 < A * A) by nra.
  assert (HAAV : 0 < A * A * v) by nra.
  assert (Hle : A * A * v <= u) by nra.
  assert (Hln : ln (A * A * v) <= ln u).
  { destruct Hle as [Hlt | Heq].
    - left; apply ln_increasing; assumption.
    - right; rewrite Heq; reflexivity. }
  rewrite (ln_mult (A * A) v HA_sq hv) in Hln.
  rewrite (ln_mult A A HA HA) in Hln.
  lra.
Qed.

Theorem log_abs_sum_lower_bound (x y : R) (hx : 0 < x) (hy : 0 < y) :
    Rabs (ln x) + Rabs (ln y) >= 2 * ln ((x + y) / (2 * sqrt (x * y))).
Proof.
  assert (Hbound : 2 * ln ((x + y) / (2 * sqrt (x * y))) <= ln x - ln y \/
                   2 * ln ((x + y) / (2 * sqrt (x * y))) <= ln y - ln x).
  { assert (Hxy : y <= x \/ x <= y) by lra.
    destruct Hxy as [Hxy | Hxy].
    - left; apply log_bound_ordered; assumption.
    - right.
      replace (x + y) with (y + x) by lra.
      replace (x * y) with (y * x) by lra.
      apply log_bound_ordered; assumption. }
  unfold Rabs; destruct (Rcase_abs (ln x)), (Rcase_abs (ln y)); lra.
Qed.
```
