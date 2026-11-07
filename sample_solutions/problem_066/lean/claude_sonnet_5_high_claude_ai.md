# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `58`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem rpow_sub_mul_log_sub_le_div_add_rpow (x y : ℝ)
    (hx : Real.exp 1 ≤ x) (hy : Real.exp 1 ≤ y) (hxy : y ^ x ≤ x ^ y) :
      (x / y) ^ ((x - y) * (Real.log x - Real.log y)) ≤
      (x ^ x + y ^ y) / (x ^ y + y ^ x) := by
  have he : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlogx : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hlogy : 1 ≤ Real.log y := (Real.le_log_iff_exp_le hy0).2 hy
  have h1 : x * Real.log y ≤ y * Real.log x := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hy0 x) hxy
    rw [Real.log_rpow hy0, Real.log_rpow hx0] at this
    exact this
  have hxy' : x ≤ y := by
    by_contra h
    push_neg at h
    have hne : x / y ≠ 1 := by
      intro h2
      rw [div_eq_one_iff_eq hy0.ne'] at h2
      linarith
    have hlt := Real.log_lt_sub_one_of_pos (div_pos hx0 hy0) hne
    rw [Real.log_div hx0.ne' hy0.ne'] at hlt
    have h2 := mul_lt_mul_of_pos_left hlt hy0
    have h3 : y * (x / y - 1) = x - y := by
      field_simp <;> ring
    rw [h3] at h2
    have h4 := mul_le_mul_of_nonneg_left hlogy (sub_pos.2 h).le
    nlinarith
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy'
  have hE : 0 ≤ (x - y) * (Real.log x - Real.log y) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hxy') (sub_nonneg.2 hlog)]
  have hL : (x / y) ^ ((x - y) * (Real.log x - Real.log y)) ≤ 1 :=
    Real.rpow_le_one (div_pos hx0 hy0).le ((div_le_one hy0).2 hxy') hE
  have hR : 1 ≤ (x ^ x + y ^ y) / (x ^ y + y ^ x) := by
    have hpos : 0 < x ^ y + y ^ x :=
      add_pos (Real.rpow_pos_of_pos hx0 y) (Real.rpow_pos_of_pos hy0 x)
    rw [one_le_div hpos]
    have e1 : x ^ y = x ^ x * x ^ (y - x) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have e2 : y ^ y = y ^ x * y ^ (y - x) := by
      rw [← Real.rpow_add hy0]
      congr 1
      ring
    have hd : 0 ≤ y - x := sub_nonneg.2 hxy'
    have hA0 : 0 ≤ x ^ x := (Real.rpow_pos_of_pos hx0 x).le
    have hAB : x ^ x ≤ y ^ x := Real.rpow_le_rpow hx0.le hxy' hx0.le
    have hPQ : x ^ (y - x) ≤ y ^ (y - x) := Real.rpow_le_rpow hx0.le hxy' hd
    have hP1 : 1 ≤ x ^ (y - x) := Real.one_le_rpow (by linarith) hd
    have hQ1 : 0 ≤ y ^ (y - x) - 1 := by linarith
    rw [e1, e2]
    nlinarith [mul_nonneg hA0 (sub_nonneg.2 hPQ), mul_nonneg (sub_nonneg.2 hAB) hQ1]
  exact hL.trans hR
```
