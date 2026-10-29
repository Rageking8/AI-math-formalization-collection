# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `19 August 2026`\
Line count: `76`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem rpow_sub_mul_log_sub_le_div_add_rpow (x y : ℝ)
    (hx : Real.exp 1 ≤ x) (hy : Real.exp 1 ≤ y) (hxy : y ^ x ≤ x ^ y) :
      (x / y) ^ ((x - y) * (Real.log x - Real.log y)) ≤
      (x ^ x + y ^ y) / (x ^ y + y ^ x) := by
  have he : (1:ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
  have hx1 : (1:ℝ) < x := by linarith
  have hy1 : (1:ℝ) < y := by linarith
  have hx0 : (0:ℝ) < x := by linarith
  have hy0 : (0:ℝ) < y := by linarith
  have hyne : y ≠ 0 := ne_of_gt hy0
  have hxne : x ≠ 0 := ne_of_gt hx0
  -- `log y ≥ 1`
  have hly : (1:ℝ) ≤ Real.log y := by
    have h : Real.exp 1 ≤ Real.exp (Real.log y) := by
      rw [Real.exp_log hy0]; exact hy
    exact Real.exp_le_exp.mp h
  -- take logs in the hypothesis
  have hlog : Real.log y * x ≤ Real.log x * y := by
    rw [Real.rpow_def_of_pos hy0, Real.rpow_def_of_pos hx0] at hxy
    exact Real.exp_le_exp.mp hxy
  -- hence `x ≤ y`
  have hxy' : x ≤ y := by
    by_contra hcon
    push_neg at hcon
    have hlt : Real.log y < Real.log x := Real.log_lt_log hy0 hcon
    have h1 : Real.log x - Real.log y + 1 < Real.exp (Real.log x - Real.log y) :=
      Real.add_one_lt_exp (sub_pos.mpr hlt).ne'
    rw [Real.exp_sub, Real.exp_log hx0, Real.exp_log hy0] at h1
    have h2 : y * (Real.log x - Real.log y + 1) < y * (x / y) :=
      mul_lt_mul_of_pos_left h1 hy0
    have h3 : y * (x / y) = x := by field_simp
    rw [h3] at h2
    linarith [mul_nonneg (sub_pos.mpr hcon).le (sub_nonneg.mpr hly)]
  have hll : Real.log x ≤ Real.log y := by
    have h : Real.exp (Real.log x) ≤ Real.exp (Real.log y) := by
      rw [Real.exp_log hx0, Real.exp_log hy0]; exact hxy'
    exact Real.exp_le_exp.mp h
  have hexp : (0:ℝ) ≤ (x - y) * (Real.log x - Real.log y) := by
    linarith [mul_nonneg (sub_nonneg.mpr hxy') (sub_nonneg.mpr hll)]
  -- left-hand side is at most 1
  have hlhs : (x / y) ^ ((x - y) * (Real.log x - Real.log y)) ≤ 1 := by
    rw [Real.rpow_def_of_pos (div_pos hx0 hy0), ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hlogdiv : Real.log (x / y) ≤ 0 := by
      rw [Real.log_div hxne hyne]; linarith
    linarith [mul_nonneg (neg_nonneg.mpr hlogdiv) hexp]
  -- right-hand side is at least 1
  have hkey : x + (y - x) = y := by ring
  have hd0 : (0:ℝ) ≤ y - x := by linarith
  have hxd : x ^ y = x ^ x * x ^ (y - x) := by
    rw [← Real.rpow_add hx0, hkey]
  have hyd : y ^ y = y ^ x * y ^ (y - x) := by
    rw [← Real.rpow_add hy0, hkey]
  have h1 : x ^ x ≤ y ^ x := Real.rpow_le_rpow hx0.le hxy' hx0.le
  have h2 : x ^ (y - x) ≤ y ^ (y - x) := Real.rpow_le_rpow hx0.le hxy' hd0
  have h3 : (1:ℝ) ≤ x ^ (y - x) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hx1.le hd0
    rwa [Real.one_rpow] at h
  have hpow : x ^ y + y ^ x ≤ x ^ x + y ^ y := by
    have hmul : x ^ x * (x ^ (y - x) - 1) ≤ y ^ x * (y ^ (y - x) - 1) :=
      mul_le_mul h1 (by linarith) (by linarith) (Real.rpow_pos_of_pos hy0 x).le
    rw [hxd, hyd]
    nlinarith [hmul]
  have hden : (0:ℝ) < x ^ y + y ^ x :=
    add_pos (Real.rpow_pos_of_pos hx0 y) (Real.rpow_pos_of_pos hy0 x)
  have hden' : x ^ y + y ^ x ≠ 0 := ne_of_gt hden
  have hR : (1:ℝ) ≤ (x ^ x + y ^ y) / (x ^ y + y ^ x) := by
    rw [← sub_nonneg]
    have heq : ((x ^ x + y ^ y) - (x ^ y + y ^ x)) / (x ^ y + y ^ x)
        = (x ^ x + y ^ y) / (x ^ y + y ^ x) - 1 := by
      rw [sub_div, div_self hden']
    rw [← heq]
    exact div_nonneg (by linarith) hden.le
  exact hlhs.trans hR
```
