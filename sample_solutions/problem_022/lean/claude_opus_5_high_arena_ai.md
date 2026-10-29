# Claude Opus 5 High (Arena AI)

Model: `claude-opus-5-high` (via Arena AI)\
Date: `10 August 2026`\
Line count: `60`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem positive_real_inequality (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y)
      (h_sum : x ^ 2 + y ^ 2 = 1) :
      ((x ^ (2 * x)) / (3 * y)) + ((y ^ (2 * y)) / (3 * x)) > 1 / (x ^ 2 + y ^ 2 + 4 * x * y) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hxy : 0 < x * y := mul_pos hx hy
  have hx1 : x < 1 := by nlinarith [mul_pos hy hy]
  have hy1 : y < 1 := by nlinarith [mul_pos hx hx]
  have h3x : (0:ℝ) < 3 * x := by linarith
  have h3y : (0:ℝ) < 3 * y := by linarith
  have hD : (0:ℝ) < x ^ 2 + y ^ 2 + 4 * x * y := by nlinarith [hxy]
  have hne : x ^ 2 + y ^ 2 + 4 * x * y ≠ 0 := ne_of_gt hD
  -- rpow comparisons : x ^ (2x) > x ^ 2
  have hxr : x ^ (2:ℝ) < x ^ (2 * x) :=
    Real.rpow_lt_rpow_of_exponent_gt hx hx1 (by linarith)
  have hyr : y ^ (2:ℝ) < y ^ (2 * y) :=
    Real.rpow_lt_rpow_of_exponent_gt hy hy1 (by linarith)
  have hx2 : x ^ (2:ℝ) = x ^ 2 := by
    have h : (2:ℝ) = 1 + 1 := by norm_num
    rw [h, Real.rpow_add hx, Real.rpow_one]; ring
  have hy2 : y ^ (2:ℝ) = y ^ 2 := by
    have h : (2:ℝ) = 1 + 1 := by norm_num
    rw [h, Real.rpow_add hy, Real.rpow_one]; ring
  rw [hx2] at hxr
  rw [hy2] at hyr
  -- the algebraic core
  have hs : 1 ≤ x + y := by nlinarith
  have hp : 2 * (x * y) ≤ 1 := by nlinarith [sq_nonneg (x - y)]
  have hcube : x ^ 3 + y ^ 3 = (x + y) * (1 - x * y) := by
    linear_combination (x + y) * h_sum
  have hnum : 0 ≤ (x ^ 3 + y ^ 3) * (x ^ 2 + y ^ 2 + 4 * x * y) - 3 * (x * y) := by
    rw [h_sum, hcube]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hs) (by linarith : (0:ℝ) ≤ 1 - x * y))
        (by linarith : (0:ℝ) ≤ 1 + 4 * (x * y)),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 2 * (x * y))
        (by linarith : (0:ℝ) ≤ 1 + 2 * (x * y))]
  have hden : (0:ℝ) < 3 * (x * y) * (x ^ 2 + y ^ 2 + 4 * x * y) := by positivity
  have key : x ^ 2 / (3 * y) + y ^ 2 / (3 * x) - 1 / (x ^ 2 + y ^ 2 + 4 * x * y)
      = ((x ^ 3 + y ^ 3) * (x ^ 2 + y ^ 2 + 4 * x * y) - 3 * (x * y))
        / (3 * (x * y) * (x ^ 2 + y ^ 2 + 4 * x * y)) := by
    first
      | (field_simp; ring)
      | field_simp
  have keyge : 1 / (x ^ 2 + y ^ 2 + 4 * x * y) ≤ x ^ 2 / (3 * y) + y ^ 2 / (3 * x) := by
    have h : 0 ≤ ((x ^ 3 + y ^ 3) * (x ^ 2 + y ^ 2 + 4 * x * y) - 3 * (x * y))
        / (3 * (x * y) * (x ^ 2 + y ^ 2 + 4 * x * y)) := div_nonneg hnum hden.le
    rw [← key] at h
    linarith
  have e1 : x ^ 2 / (3 * y) < x ^ (2 * x) / (3 * y) := by
    have h : 0 < (x ^ (2 * x) - x ^ 2) / (3 * y) := div_pos (by linarith) h3y
    rw [sub_div] at h
    linarith
  have e2 : y ^ 2 / (3 * x) < y ^ (2 * y) / (3 * x) := by
    have h : 0 < (y ^ (2 * y) - y ^ 2) / (3 * x) := div_pos (by linarith) h3x
    rw [sub_div] at h
    linarith
  linarith
```
