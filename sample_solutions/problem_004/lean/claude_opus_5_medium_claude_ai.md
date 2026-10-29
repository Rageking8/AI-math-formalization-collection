# Claude Opus 5 Medium (Claude AI)

Model: `Claude Opus 5 Medium` (via Claude AI)\
Date: `28 July 2026`\
Line count: `50`\
Turn count: `3`

## Solution

```lean4
import Mathlib

theorem log_abs_sum_lower_bound (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    |Real.log x| + |Real.log y| ≥
      2 * Real.log ((x + y) / (2 * Real.sqrt (x * y))) := by
  have hxy : (0:ℝ) < x * y := mul_pos hx hy
  have hs : 0 < Real.sqrt (x * y) := Real.sqrt_pos.mpr hxy
  have hsq : Real.sqrt (x * y) ^ 2 = x * y := Real.sq_sqrt hxy.le
  have hMpos : 0 < (x + y) / (2 * Real.sqrt (x * y)) :=
    div_pos (by linarith) (by linarith)
  have hM2 : ((x + y) / (2 * Real.sqrt (x * y))) ^ 2 = (x + y) ^ 2 / (4 * (x * y)) := by
    rw [div_pow, mul_pow, hsq]
    norm_num
  have h2 : 2 * Real.log ((x + y) / (2 * Real.sqrt (x * y)))
      = Real.log (((x + y) / (2 * Real.sqrt (x * y))) ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [ge_iff_le, h2, Real.log_le_iff_le_exp (pow_pos hMpos 2), Real.exp_add, hM2]
  rcases le_or_gt 1 x with hx1 | hx1 <;> rcases le_or_gt 1 y with hy1 | hy1
  · -- 1 ≤ x, 1 ≤ y :  need (x+y)^2 ≤ (xy)(4xy)
    rw [abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (Real.log_nonneg hy1),
      Real.exp_log hx, Real.exp_log hy, div_le_iff₀ (by linarith)]
    have h1 : x + y ≤ 2 * (x * y) := by nlinarith
    have h3 : (x + y) * (x + y) ≤ (2 * (x * y)) * (2 * (x * y)) :=
      mul_le_mul h1 h1 (by linarith) (by linarith)
    nlinarith [h3]
  · -- 1 ≤ x, y < 1 :  need (x+y)^2 ≤ 4x^2
    rw [abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonpos (Real.log_nonpos hy.le hy1.le),
      Real.exp_log hx, Real.exp_neg, Real.exp_log hy, div_le_iff₀ (by linarith)]
    have hE : x * y⁻¹ * (4 * (x * y)) = 4 * x ^ 2 * (y⁻¹ * y) := by ring
    rw [hE, inv_mul_cancel₀ hy.ne']
    have hyx : y ≤ x := le_trans hy1.le hx1
    nlinarith [hyx, hx, hy]
  · -- x < 1, 1 ≤ y :  need (x+y)^2 ≤ 4y^2
    rw [abs_of_nonpos (Real.log_nonpos hx.le hx1.le),
      abs_of_nonneg (Real.log_nonneg hy1),
      Real.exp_neg, Real.exp_log hx, Real.exp_log hy, div_le_iff₀ (by linarith)]
    have hE : x⁻¹ * y * (4 * (x * y)) = 4 * y ^ 2 * (x⁻¹ * x) := by ring
    rw [hE, inv_mul_cancel₀ hx.ne']
    have hxy2 : x ≤ y := le_trans hx1.le hy1
    nlinarith [hxy2, hx, hy]
  · -- x < 1, y < 1 :  need (x+y)^2 ≤ 4
    rw [abs_of_nonpos (Real.log_nonpos hx.le hx1.le),
      abs_of_nonpos (Real.log_nonpos hy.le hy1.le),
      Real.exp_neg, Real.exp_neg, Real.exp_log hx, Real.exp_log hy,
      div_le_iff₀ (by linarith)]
    have hE : x⁻¹ * y⁻¹ * (4 * (x * y)) = 4 * (x⁻¹ * x) * (y⁻¹ * y) := by ring
    rw [hE, inv_mul_cancel₀ hx.ne', inv_mul_cancel₀ hy.ne']
    nlinarith [hx, hy, hx1, hy1]
```
