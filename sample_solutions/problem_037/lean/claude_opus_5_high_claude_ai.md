# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `6 August 2026`\
Line count: `58`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem min_poly_eq_max_exp_iff_eq_two (x : ℝ) :
    min (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1) = max ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x) ↔ x = 2 := by
  have h3sq : (3 : ℝ) ^ (2 : ℝ) = 9 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h2sq : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- x < 2 : the min is < 3 while the max is > 3
      have hA := min_le_left (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1)
      have hB := min_le_right (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1)
      rw [h] at hA hB
      have hmax := le_max_right ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x)
      have hb : (2 : ℝ) ^ x < (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
      rw [h2sq] at hb
      have hpos : (0 : ℝ) < x ^ 2 + x + 2 := by nlinarith [sq_nonneg (2 * x + 1)]
      have hprod : (0 : ℝ) < (2 - x) * (x ^ 2 + x + 2) := mul_pos (by linarith) hpos
      nlinarith [hA, hB, hmax, hb, hprod]
    · -- x > 2 : 3 ^ x - 6 exceeds x ^ 2 - 1
      have hlog : (1 : ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)]
        linarith [Real.exp_one_lt_d9]
      have ht : (0 : ℝ) < x - 2 := by linarith
      have hexp1 : Real.exp (x - 2) ≤ (3 : ℝ) ^ (x - 2) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
        apply Real.exp_le_exp.2
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.log 3 - 1) (le_of_lt ht)]
      have hhalf : (x - 2) / 2 + 1 ≤ Real.exp ((x - 2) / 2) := Real.add_one_le_exp _
      have hxx : x / 2 ≤ Real.exp ((x - 2) / 2) := by linarith
      have hx0 : (0 : ℝ) ≤ x / 2 := by linarith
      have hmul := mul_le_mul hxx hxx hx0 (Real.exp_nonneg _)
      have hexp2 : Real.exp ((x - 2) / 2) * Real.exp ((x - 2) / 2) = Real.exp (x - 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp2] at hmul
      have h3x : (3 : ℝ) ^ x = 9 * (3 : ℝ) ^ (x - 2) := by
        have hadd : (3 : ℝ) ^ ((2 : ℝ) + (x - 2)) = (3 : ℝ) ^ (2 : ℝ) * (3 : ℝ) ^ (x - 2) :=
          Real.rpow_add (by norm_num) _ _
        rw [h3sq, show (2 : ℝ) + (x - 2) = x by ring] at hadd
        exact hadd
      have hkey : x ^ 2 + 5 < (3 : ℝ) ^ x := by
        rw [h3x]
        nlinarith [hmul, hexp1, mul_pos ht (show (0:ℝ) < x + 2 by linarith)]
      have hB := min_le_right (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1)
      rw [h] at hB
      have hmaxL := le_max_left ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x)
      linarith
  · rintro rfl
    rw [h3sq, h2sq]
    norm_num
```
