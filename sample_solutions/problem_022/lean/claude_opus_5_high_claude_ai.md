# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `31 July 2026`\
Line count: `61`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem positive_real_inequality (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y)
      (h_sum : x ^ 2 + y ^ 2 = 1) :
      ((x ^ (2 * x)) / (3 * y)) + ((y ^ (2 * y)) / (3 * x)) > 1 / (x ^ 2 + y ^ 2 + 4 * x * y) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hx1 : x < 1 := by nlinarith [mul_pos hy hy]
  have hy1 : y < 1 := by nlinarith [mul_pos hx hx]
  have h3x : (0:ℝ) < 3 * x := by linarith
  have h3y : (0:ℝ) < 3 * y := by linarith
  have ht0 : 0 < x * y := mul_pos hx hy
  have ht2 : 2 * (x * y) ≤ 1 := by nlinarith [sq_nonneg (x - y)]
  have hs : 1 < x + y := by nlinarith [mul_pos hx hy]
  -- since 0 < x < 1 and 2*x < 2, rpow is decreasing in the exponent
  have hxx : x ^ (2:ℝ) < x ^ (2 * x) :=
    Real.rpow_lt_rpow_of_exponent_gt hx hx1 (by linarith)
  have hyy : y ^ (2:ℝ) < y ^ (2 * y) :=
    Real.rpow_lt_rpow_of_exponent_gt hy hy1 (by linarith)
  have hx2 : x ^ (2:ℝ) = x ^ 2 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hy2 : y ^ (2:ℝ) = y ^ 2 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [hx2] at hxx
  rw [hy2] at hyy
  have k1 : x ^ 2 / (3 * y) < x ^ (2 * x) / (3 * y) := by
    have := mul_lt_mul_of_pos_right hxx (inv_pos.mpr h3y)
    simpa [div_eq_mul_inv] using this
  have k2 : y ^ 2 / (3 * x) < y ^ (2 * y) / (3 * x) := by
    have := mul_lt_mul_of_pos_right hyy (inv_pos.mpr h3x)
    simpa [div_eq_mul_inv] using this
  -- algebraic part: (x³+y³)(1+4xy) ≥ 3xy
  have hd : (0:ℝ) < 1 + 4 * (x * y) := by linarith
  have hd0 : (1 + 4 * (x * y)) ≠ 0 := ne_of_gt hd
  have hkey2 : 3 * (x * y) ≤ (x + y) * ((1 - x * y) * (1 + 4 * (x * y))) := by
    have e1 : (0:ℝ) ≤ (x + y - 1) * ((1 - x * y) * (1 + 4 * (x * y))) := by
      apply mul_nonneg (by linarith)
      exact mul_nonneg (by linarith) (by linarith)
    have e2 : (0:ℝ) ≤ (1 - 2 * (x * y)) * (1 + 2 * (x * y)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [e1, e2]
  have hkey3 : 9 * (x * y) ≤ (3 * x ^ 3 + 3 * y ^ 3) * (1 + 4 * (x * y)) := by
    have hc : 3 * x ^ 3 + 3 * y ^ 3 = 3 * ((x + y) * (1 - x * y)) := by
      linear_combination 3 * (x + y) * h_sum
    rw [hc]
    nlinarith [hkey2]
  have key : 1 / (x ^ 2 + y ^ 2 + 4 * x * y) ≤ x ^ 2 / (3 * y) + y ^ 2 / (3 * x) := by
    have hrw : x ^ 2 + y ^ 2 + 4 * x * y = 1 + 4 * (x * y) := by rw [h_sum]; ring
    rw [hrw, ← sub_nonneg]
    have expand : x ^ 2 / (3 * y) + y ^ 2 / (3 * x) - 1 / (1 + 4 * (x * y))
        = ((3 * x ^ 3 + 3 * y ^ 3) * (1 + 4 * (x * y)) - 9 * (x * y))
          / ((9 * (x * y)) * (1 + 4 * (x * y))) := by
      field_simp
      ring
    rw [expand]
    apply div_nonneg
    · linarith [hkey3]
    · have := mul_pos (by linarith : (0:ℝ) < 9 * (x * y)) hd
      linarith
  linarith [k1, k2, key]
```
