# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `7 September 2026`\
Line count: `76`\
Turn count: `3`

## Solution

```lean4
import Mathlib

theorem positive_real_inequality (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y)
      (h_sum : x ^ 2 + y ^ 2 = 1) :
      ((x ^ (2 * x)) / (3 * y)) + ((y ^ (2 * y)) / (3 * x)) > 1 / (x ^ 2 + y ^ 2 + 4 * x * y) := by
  have hxsq1 : x ^ 2 < 1 := by nlinarith [pow_pos hy 2]
  have hx1 : x < 1 := by nlinarith [hxsq1, hx]
  have hysq1 : y ^ 2 < 1 := by nlinarith [pow_pos hx 2]
  have hy1 : y < 1 := by nlinarith [hysq1, hy]
  have e2 : x ^ (2:ℝ) = x ^ (2:ℕ) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have e1 : x ^ (2 * x) = (x ^ 2) ^ x := by
    rw [Real.rpow_mul hx.le, e2]
  have hxb : x ^ 2 < x ^ (2 * x) := by
    rw [e1]
    have hb0 : (0:ℝ) < x ^ 2 := pow_pos hx 2
    calc x ^ 2 = (x ^ 2) ^ (1:ℝ) := (Real.rpow_one (x ^ 2)).symm
      _ < (x ^ 2) ^ x := Real.rpow_lt_rpow_of_exponent_gt hb0 hxsq1 hx1
  have e2' : y ^ (2:ℝ) = y ^ (2:ℕ) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have e1' : y ^ (2 * y) = (y ^ 2) ^ y := by
    rw [Real.rpow_mul hy.le, e2']
  have hyb : y ^ 2 < y ^ (2 * y) := by
    rw [e1']
    have hb0 : (0:ℝ) < y ^ 2 := pow_pos hy 2
    calc y ^ 2 = (y ^ 2) ^ (1:ℝ) := (Real.rpow_one (y ^ 2)).symm
      _ < (y ^ 2) ^ y := Real.rpow_lt_rpow_of_exponent_gt hb0 hysq1 hy1
  have hu1 : x + y > 1 := by nlinarith [mul_pos hx hy, hx, hy]
  have hu2 : (x + y) ^ 2 ≤ 2 := by nlinarith [sq_nonneg (x - y)]
  have t1 : (0:ℝ) ≤ 2 - (x + y) ^ 2 := by linarith
  have t2 : (0:ℝ) ≤ (x + y) - 1 := by linarith
  have t3 : (0:ℝ) ≤ 2 * (x + y) ^ 2 + 2 * (x + y) - 1 := by nlinarith [sq_nonneg (x + y), hu1]
  have p1 : (0:ℝ) ≤ (2 - (x + y) ^ 2) * ((x + y) - 1) := mul_nonneg t1 t2
  have p2 : (0:ℝ) ≤ (2 - (x + y) ^ 2) * ((x + y) - 1) * (2 * (x + y) ^ 2 + 2 * (x + y) - 1) :=
    mul_nonneg p1 t3
  have master : 2 * ((x ^ 3 + y ^ 3) * (1 + 4 * x * y) - 3 * x * y) =
      (-2 * (x + y) ^ 5 + 7 * (x + y) ^ 3 - 3 * (x + y) ^ 2 - 3 * (x + y) + 3)
      + (x ^ 2 + y ^ 2 - 1) * (-6 * (x + y) * (x ^ 2 + y ^ 2) - 3 * (x + y) + 8 * (x + y) ^ 3 + 3) := by
    ring
  have master2 : 2 * ((x ^ 3 + y ^ 3) * (1 + 4 * x * y) - 3 * x * y) =
      -2 * (x + y) ^ 5 + 7 * (x + y) ^ 3 - 3 * (x + y) ^ 2 - 3 * (x + y) + 3 := by
    rw [master, h_sum]; ring
  have step : -2 * (x + y) ^ 5 + 7 * (x + y) ^ 3 - 3 * (x + y) ^ 2 - 3 * (x + y) + 3 =
      2 * (2 - (x + y) ^ 2) + (2 - (x + y) ^ 2) * ((x + y) - 1) * (2 * (x + y) ^ 2 + 2 * (x + y) - 1)
      + 3 * ((x + y) - 1) := by ring
  have mainIneq : 3 * x * y ≤ (x ^ 3 + y ^ 3) * (1 + 4 * x * y) := by
    have h2 : (0:ℝ) ≤ 2 * ((x ^ 3 + y ^ 3) * (1 + 4 * x * y) - 3 * x * y) := by
      rw [master2, step]
      nlinarith [t1, t2, p2]
    linarith [h2]
  have hD : x ^ 2 + y ^ 2 + 4 * x * y = 1 + 4 * x * y := by rw [h_sum]
  rw [hD]
  have h3y : (0:ℝ) < 3 * y := by linarith
  have h3x : (0:ℝ) < 3 * x := by linarith
  have d1 : x ^ 2 / (3 * y) < x ^ (2 * x) / (3 * y) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right hxb (inv_pos.mpr h3y)
  have d2 : y ^ 2 / (3 * x) < y ^ (2 * y) / (3 * x) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right hyb (inv_pos.mpr h3x)
  have key1 : x ^ 2 / (3 * y) + y ^ 2 / (3 * x) < x ^ (2 * x) / (3 * y) + y ^ (2 * y) / (3 * x) :=
    add_lt_add d1 d2
  have hxy4 : (0:ℝ) < 1 + 4 * x * y := by positivity
  have hx' : x ≠ 0 := ne_of_gt hx
  have hy' : y ≠ 0 := ne_of_gt hy
  have h4' : (1 + 4 * x * y) ≠ 0 := ne_of_gt hxy4
  have expand : x ^ 2 / (3 * y) + y ^ 2 / (3 * x) - 1 / (1 + 4 * x * y) =
      ((x ^ 3 + y ^ 3) * (1 + 4 * x * y) - 3 * x * y) / (3 * x * y * (1 + 4 * x * y)) := by
    field_simp
  have hnum : (0:ℝ) ≤ (x ^ 3 + y ^ 3) * (1 + 4 * x * y) - 3 * x * y := by linarith [mainIneq]
  have hden : (0:ℝ) < 3 * x * y * (1 + 4 * x * y) := by positivity
  have key2 : (1:ℝ) / (1 + 4 * x * y) ≤ x ^ 2 / (3 * y) + y ^ 2 / (3 * x) := by
    have := div_nonneg hnum hden.le
    linarith [expand, this]
  linarith [key1, key2]
```
