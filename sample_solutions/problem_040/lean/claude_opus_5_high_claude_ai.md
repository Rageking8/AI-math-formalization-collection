# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `6 August 2026`\
Line count: `27`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem two_rpow_sq_add_cos_sin_pos (x y z : ℝ) :
    (2 : ℝ) ^ x * (y ^ 2 + 1) + (2 : ℝ) ^ (-x) * (z ^ 2 + 1) + 2 * (y * Real.cos x + z * Real.sin x) > 0 := by
  have ha : (0:ℝ) < (2:ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
  have hb : (0:ℝ) < (2:ℝ) ^ (-x) := Real.rpow_pos_of_pos (by norm_num) (-x)
  have hab : (2:ℝ) ^ x * (2:ℝ) ^ (-x) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    simp
  have hpyth : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  set a : ℝ := (2:ℝ) ^ x
  set b : ℝ := (2:ℝ) ^ (-x)
  set c : ℝ := Real.cos x
  set s : ℝ := Real.sin x
  have hkey : a * (a * (y ^ 2 + 1) + b * (z ^ 2 + 1) + 2 * (y * c + z * s))
      = (a * y + c) ^ 2 + (z + a * s) ^ 2 + a ^ 2 * c ^ 2 + s ^ 2 := by
    linear_combination (z ^ 2 + 1) * hab - (a ^ 2 + 1) * hpyth
  have hpos : 0 < (a * y + c) ^ 2 + (z + a * s) ^ 2 + a ^ 2 * c ^ 2 + s ^ 2 := by
    rcases eq_or_ne s 0 with h | h
    · have hc1 : c ^ 2 = 1 := by
        rw [h] at hpyth; simpa using hpyth
      have h2 : 0 < a ^ 2 * c ^ 2 := by
        rw [hc1, mul_one]; positivity
      nlinarith [sq_nonneg (a * y + c), sq_nonneg (z + a * s), sq_nonneg s]
    · have h2 : 0 < s ^ 2 := by positivity
      nlinarith [sq_nonneg (a * y + c), sq_nonneg (z + a * s), sq_nonneg (a * c)]
  nlinarith [hkey, hpos, ha]
```
