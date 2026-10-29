# Claude Sonnet 5.5 High (Arena AI)

Model: `claude-sonnet-5-5-high` (via Arena AI)\
Date: `1 October 2026`\
Line count: `45`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem min_poly_eq_max_exp_iff_eq_two (x : ℝ) :
    min (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1) = max ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x) ↔ x = 2 := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hx | hx
    · have h4 : (2:ℝ)^(2:ℝ) = 4 := by rw [Real.rpow_two]; norm_num
      have h2 : (2:ℝ)^x < 4 := by
        have : (2:ℝ)^x < (2:ℝ)^(2:ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hx
        linarith
      have hM : 3 < max ((3:ℝ)^x - 6) (7 - (2:ℝ)^x) :=
        lt_max_of_lt_right (by linarith)
      rcases le_or_gt x (-1) with hx1 | hx1
      · have hmin := min_le_left (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1)
        have hf : x ^ 3 - 2 * x ^ 2 + 3 ≤ 0 := by
          nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ -1 - x)]
        linarith
      · have hmin := min_le_right (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1)
        have : x ^ 2 - 1 < 3 := by nlinarith
        linarith
    · have hmin := min_le_right (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1)
      have hmax := le_max_left ((3:ℝ)^x - 6) (7 - (2:ℝ)^x)
      have hlog : 1 ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        have := Real.exp_one_lt_d9
        linarith
      have h3 : (3:ℝ)^x = 9 * (3:ℝ)^(x-2) := by
        have := Real.rpow_add (by norm_num : (0:ℝ) < 3) 2 (x-2)
        rw [show (2:ℝ) + (x-2) = x by ring, Real.rpow_two] at this
        rw [this]; norm_num
      have h5 : Real.exp (x-2) ≤ (3:ℝ)^(x-2) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
        apply Real.exp_le_exp.mpr
        nlinarith
      have h6 := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ x - 2)
      nlinarith
  · intro h
    subst h
    have h4 : (2:ℝ)^(2:ℝ) = 4 := by rw [Real.rpow_two]; norm_num
    have h9 : (3:ℝ)^(2:ℝ) = 9 := by rw [Real.rpow_two]; norm_num
    rw [h4, h9]
    norm_num
```
