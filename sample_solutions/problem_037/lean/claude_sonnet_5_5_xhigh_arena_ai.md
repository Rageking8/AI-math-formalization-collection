# Claude Sonnet 5.5 xHigh (Arena AI)

Model: `claude-sonnet-5-5-xhigh` (via Arena AI)\
Date: `1 October 2026`\
Line count: `55`\
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
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h2 : (2:ℝ)^x < 4 := by
        have h' : (2:ℝ)^x < (2:ℝ)^(2:ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
        have e : (2:ℝ)^(2:ℝ) = 4 := by rw [Real.rpow_two]; norm_num
        linarith
      have hmax : 3 < max ((3:ℝ)^x - 6) (7 - (2:ℝ)^x) := by
        have := le_max_right ((3:ℝ)^x - 6) (7 - (2:ℝ)^x)
        linarith
      have hmin : min (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1) < 3 := by
        by_cases hx : x ≤ -1
        · apply lt_of_le_of_lt (min_le_left _ _)
          have hx2 : 0 < x^2 := by nlinarith
          have : 0 < x^2 * (2 - x) := mul_pos hx2 (by linarith)
          nlinarith
        · push_neg at hx
          apply lt_of_le_of_lt (min_le_right _ _)
          nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : (0:ℝ) < x + 2)]
      linarith
    · have ht : 0 < x - 2 := by linarith
      have e : (3:ℝ)^(x-2) * 9 = (3:ℝ)^x := by
        have h9 : (9:ℝ) = (3:ℝ)^(2:ℝ) := by rw [Real.rpow_two]; norm_num
        rw [h9, ← Real.rpow_add (by norm_num)]
        congr 1
        ring
      have h3 : Real.exp (x-2) ≤ (3:ℝ)^(x-2) := by
        rw [← Real.exp_one_rpow]
        apply Real.rpow_le_rpow (Real.exp_pos 1).le _ ht.le
        have := Real.exp_one_lt_d9
        norm_num at this
        linarith
      have h1 : 1 + (x-2)/2 ≤ Real.exp ((x-2)/2) := by
        linarith [Real.add_one_le_exp ((x-2)/2)]
      have h2 : Real.exp (x-2) = Real.exp ((x-2)/2) * Real.exp ((x-2)/2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h3' : (1 + (x-2)/2)^2 ≤ Real.exp (x-2) := by
        rw [h2, sq]
        exact mul_self_le_mul_self (by linarith) h1
      have key : x^2 + 5 < (3:ℝ)^x := by
        nlinarith [e, h3, h3', sq_nonneg (x-2)]
      have hm1 : min (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1) ≤ x^2 - 1 := min_le_right _ _
      have hm2 : (3:ℝ)^x - 6 ≤ max ((3:ℝ)^x - 6) (7 - (2:ℝ)^x) := le_max_left _ _
      linarith
  · rintro rfl
    rw [Real.rpow_two, Real.rpow_two]
    norm_num
```
