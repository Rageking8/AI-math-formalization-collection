# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `30 August 2026`\
Line count: `33`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem min_poly_eq_max_exp_iff_eq_two (x : ℝ) :
    min (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1) = max ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x) ↔ x = 2 := by
  have s : ∀ y : ℝ, y ^ (2 : ℝ) = y ^ 2 := fun y => by
    rw [← Real.rpow_natCast y 2]; norm_num
  refine ⟨fun h => ?_, fun h => by subst h; simp only [s]; norm_num⟩
  by_contra hne
  have l := le_max_left ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x)
  have r := le_max_right ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x)
  rw [← h] at l r
  have m1 := min_le_left (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1)
  have m2 := min_le_right (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h2 : (2 : ℝ) ^ x < (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
    rw [s] at h2
    nlinarith [sq_nonneg x]
  · have e3 : Real.exp (Real.log 3) = 3 := Real.exp_log (by norm_num)
    have hL : 1 ≤ Real.log 3 :=
      Real.exp_le_exp.mp (by rw [e3]; exact (Real.exp_one_lt_d9.trans (by norm_num)).le)
    have hs : Real.exp (Real.log 3 * (x / 2))
        = Real.exp (Real.log 3) * Real.exp (Real.log 3 * ((x - 2) / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e3] at hs
    have hv : 3 * (x / 2) ≤ Real.exp (Real.log 3 * (x / 2)) := by
      rw [hs]
      linarith [Real.add_one_le_exp (Real.log 3 * ((x - 2) / 2)),
        mul_nonneg (by linarith : (0:ℝ) ≤ Real.log 3 - 1) (by linarith : (0:ℝ) ≤ x - 2)]
    have hx3 : (3 : ℝ) ^ x
        = Real.exp (Real.log 3 * (x / 2)) * Real.exp (Real.log 3 * (x / 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), ← Real.exp_add]; congr 1; ring
    nlinarith [mul_self_le_mul_self (by linarith : (0:ℝ) ≤ 3 * (x / 2)) hv, sq_nonneg (x - 2)]
```
