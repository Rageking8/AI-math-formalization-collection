# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `12 August 2026`\
Line count: `37`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem positive_real_inequality (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y)
      (h_sum : x ^ 2 + y ^ 2 = 1) :
      ((x ^ (2 * x)) / (3 * y)) + ((y ^ (2 * y)) / (3 * x)) > 1 / (x ^ 2 + y ^ 2 + 4 * x * y) := by
  have key : ∀ z : ℝ, 0 < z → z < 1 → z ^ 2 < z ^ (2 * z) := fun z h0 h1 => by
    have h : z ^ (2 : ℝ) = z ^ 2 := by rw [← Real.rpow_natCast z 2] <;> norm_num
    rw [← h]; exact Real.rpow_lt_rpow_of_exponent_gt h0 h1 (by linarith)
  have hp : 0 < x * y := mul_pos hx hy
  have hxx := key x hx (by nlinarith [mul_pos hy hy])
  have hyy := key y hy (by nlinarith [mul_pos hx hx])
  have hq : x * y ≤ 1 / 2 := by nlinarith [sq_nonneg (x - y)]
  have hs : 1 ≤ x + y := by nlinarith [hp, hx, hy]
  have hN : 0 ≤ 3 * (x ^ 3 + y ^ 3) * (1 + 4 * (x * y)) - 9 * (x * y) := by
    have hE : 3 * (x ^ 3 + y ^ 3) * (1 + 4 * (x * y))
        = 3 * ((x + y) * (1 - x * y) * (1 + 4 * (x * y))) := by
      linear_combination (3 * (1 + 4 * (x * y)) * (x + y)) * h_sum
    rw [hE]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ x + y - 1)
        (by linarith : (0:ℝ) ≤ 1 - x * y)) (by linarith : (0:ℝ) ≤ 1 + 4 * (x * y)),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 2 * (x * y)) (by linarith : (0:ℝ) ≤ 1 + 2 * (x * y))]
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have h40 : 1 + 4 * (x * y) ≠ 0 := by positivity
  have hid : x ^ 2 / (3 * y) + y ^ 2 / (3 * x) - 1 / (x ^ 2 + y ^ 2 + 4 * x * y)
      = (3 * (x ^ 3 + y ^ 3) * (1 + 4 * (x * y)) - 9 * (x * y))
        / (9 * (x * y) * (1 + 4 * (x * y))) := by
    rw [h_sum]; field_simp <;> ring
  have hQ := div_nonneg hN (by positivity : (0:ℝ) ≤ 9 * (x * y) * (1 + 4 * (x * y)))
  have g1 : x ^ 2 / (3 * y) < x ^ (2 * x) / (3 * y) := by
    have h := div_pos (sub_pos.2 hxx) (by linarith : (0:ℝ) < 3 * y)
    rw [sub_div] at h; linarith
  have g2 : y ^ 2 / (3 * x) < y ^ (2 * y) / (3 * x) := by
    have h := div_pos (sub_pos.2 hyy) (by linarith : (0:ℝ) < 3 * x)
    rw [sub_div] at h; linarith
  linarith
```
