# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `14 September 2026`\
Line count: `45`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem two_rpow_sq_add_cos_sin_pos (x y z : ℝ) :
    (2 : ℝ) ^ x * (y ^ 2 + 1) + (2 : ℝ) ^ (-x) * (z ^ 2 + 1) + 2 * (y * Real.cos x + z * Real.sin x) > 0 := by
  have ha : (0:ℝ) < (2:ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
  have hb : (0:ℝ) < (2:ℝ) ^ (-x) := Real.rpow_pos_of_pos (by norm_num) (-x)
  have hab : (2:ℝ) ^ x * (2:ℝ) ^ (-x) = 1 := by
    have e1 : (2:ℝ) ^ x * (2:ℝ) ^ (-x) = (2:ℝ) ^ (x + -x) :=
      (Real.rpow_add (by norm_num) x (-x)).symm
    have e2 : x + -x = 0 := by ring
    rw [e1, e2, Real.rpow_zero]
  set a := (2:ℝ) ^ x
  set b := (2:ℝ) ^ (-x)
  have hpyth : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := by
    have h := Real.sin_sq_add_cos_sq x
    linarith
  have hc2 : (0:ℝ) ≤ Real.cos x ^ 2 := sq_nonneg _
  have hs2 : (0:ℝ) ≤ Real.sin x ^ 2 := sq_nonneg _
  have hpos : a * Real.cos x ^ 2 + b * Real.sin x ^ 2 > 0 := by
    by_cases hc : Real.cos x = 0
    · have hsin1 : Real.sin x ^ 2 = 1 := by
        have h := hpyth
        rw [hc] at h
        simpa using h
      have heq : a * Real.cos x ^ 2 + b * Real.sin x ^ 2 = b := by
        rw [hc, hsin1]; ring
      rw [heq]; exact hb
    · have hcpos : 0 < Real.cos x ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hc).symm
      nlinarith [mul_pos ha hcpos, mul_nonneg hb.le hs2]
  have h1 : b * (a * y + Real.cos x) ^ 2 = a * y ^ 2 + 2 * y * Real.cos x + b * Real.cos x ^ 2 := by
    have key : b * (a * y + Real.cos x) ^ 2
        = (a * b) * (a * y ^ 2 + 2 * y * Real.cos x) + b * Real.cos x ^ 2 := by ring
    rw [key, hab]; ring
  have h2 : a * (b * z + Real.sin x) ^ 2 = b * z ^ 2 + 2 * z * Real.sin x + a * Real.sin x ^ 2 := by
    have key : a * (b * z + Real.sin x) ^ 2
        = (a * b) * (b * z ^ 2 + 2 * z * Real.sin x) + a * Real.sin x ^ 2 := by ring
    rw [key, hab]; ring
  have hnn1 : (0:ℝ) ≤ b * (a * y + Real.cos x) ^ 2 := mul_nonneg hb.le (sq_nonneg _)
  have hnn2 : (0:ℝ) ≤ a * (b * z + Real.sin x) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  have haux1 : a * Real.cos x ^ 2 + a * Real.sin x ^ 2 = a := by
    rw [← mul_add, hpyth, mul_one]
  have haux2 : b * Real.cos x ^ 2 + b * Real.sin x ^ 2 = b := by
    rw [← mul_add, hpyth, mul_one]
  nlinarith [h1, h2, hnn1, hnn2, hpos, haux1, haux2]
```
