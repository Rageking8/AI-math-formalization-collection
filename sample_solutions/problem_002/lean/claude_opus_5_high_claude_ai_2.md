# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `11 August 2026`\
Line count: `30`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem sin_mul_upper_bound
    (x y z : ℝ)
    (h : x + y + z = Real.pi) :
    Real.sin x * Real.sin y * Real.sin z ≤
      (3 * Real.sqrt 3) / 8 := by
  have S := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have S' := Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)
  have K : ∀ u v : ℝ, 0 ≤ v → v ^ 2 + u ^ 2 = 1 → (1 - u) * v ≤ 3 * Real.sqrt 3 / 4 := by
    intro u v hv hp
    have h1 : 0 ≤ (1 - u) * v := mul_nonneg (by nlinarith [sq_nonneg v, sq_nonneg (u - 1)]) hv
    have h2 : ((1 - u) * v) ^ 2 ≤ 27 / 16 := by
      have e : v ^ 2 = 1 - u ^ 2 := by linarith
      rw [mul_pow, e]
      nlinarith [sq_nonneg ((u + 1/2) * (u - 3/2)), sq_nonneg (u + 1/2)]
    nlinarith [h1, h2]
  have e : Real.sin x * Real.sin y * Real.sin z
      = (Real.cos (x - y) - Real.cos (x + y)) / 2 * Real.sin (x + y) := by
    rw [show z = Real.pi - (x + y) by linarith, Real.sin_pi_sub, Real.cos_sub, Real.cos_add]; ring
  rw [e]
  have hp := Real.sin_sq_add_cos_sq (x + y)
  have t1 := Real.cos_le_one (x - y)
  have t2 := Real.neg_one_le_cos (x - y)
  rcases le_total 0 (Real.sin (x + y)) with hv | hv
  · have := K (Real.cos (x + y)) (Real.sin (x + y)) hv hp
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - Real.cos (x - y)) hv]
  · have := K (-Real.cos (x + y)) (-Real.sin (x + y)) (by linarith) (by linarith)
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + Real.cos (x - y))
      (by linarith : (0:ℝ) ≤ -Real.sin (x + y))]
```
