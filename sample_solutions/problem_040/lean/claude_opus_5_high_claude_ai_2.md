# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `31 August 2026`\
Line count: `17`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem two_rpow_sq_add_cos_sin_pos (x y z : ℝ) :
    (2 : ℝ) ^ x * (y ^ 2 + 1) + (2 : ℝ) ^ (-x) * (z ^ 2 + 1) + 2 * (y * Real.cos x + z * Real.sin x) > 0 := by
  have t : (0:ℝ) < 2 := by norm_num
  have key : ∀ a b c s : ℝ, 0 < a → 0 < b → a * b = 1 → s ^ 2 + c ^ 2 = 1 →
      0 < a * (y ^ 2 + 1) + b * (z ^ 2 + 1) + 2 * (y * c + z * s) := by
    intro a b c s ha hb hab hs
    have e : a * (y ^ 2 + 1) + b * (z ^ 2 + 1) + 2 * (y * c + z * s)
        = b * (a * y + c) ^ 2 + a * (b * z + s) ^ 2 + (a * c ^ 2 + b * s ^ 2) := by
      linear_combination (-(a * y ^ 2 + b * z ^ 2 + 2 * y * c + 2 * z * s)) * hab - (a + b) * hs
    linarith [mul_nonneg hb.le (sq_nonneg (a * y + c)), mul_nonneg ha.le (sq_nonneg (b * z + s)),
      mul_nonneg (sub_nonneg.2 (min_le_left a b)) (sq_nonneg c),
      mul_nonneg (sub_nonneg.2 (min_le_right a b)) (sq_nonneg s),
      mul_pos (lt_min ha hb) (by linarith : (0:ℝ) < s ^ 2 + c ^ 2)]
  exact key _ _ _ _ (Real.rpow_pos_of_pos t x) (Real.rpow_pos_of_pos t (-x))
    (by rw [← Real.rpow_add t]; simp) (Real.sin_sq_add_cos_sq x)
```
