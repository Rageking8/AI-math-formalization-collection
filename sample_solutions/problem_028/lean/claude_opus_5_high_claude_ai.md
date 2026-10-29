# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `3 August 2026`\
Line count: `56`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem unique_real_solution_nested_radical (x : ℝ) (hx : 0 ≤ x) :
    (19 * Real.sqrt (2 * x + 1) + 34 * Real.sqrt x) ^ (1 / 3 : ℝ) =
      Real.sqrt (2 * x + 1) + Real.sqrt x ↔ x = 4 := by
  have h2x : (0:ℝ) ≤ 2 * x + 1 := by linarith
  obtain ⟨a, ha0, ha2, ha⟩ : ∃ a : ℝ, 0 ≤ a ∧ a ^ 2 = 2 * x + 1 ∧ Real.sqrt (2 * x + 1) = a :=
    ⟨Real.sqrt (2 * x + 1), Real.sqrt_nonneg _, Real.sq_sqrt h2x, rfl⟩
  obtain ⟨b, hb0, hb2, hb⟩ : ∃ b : ℝ, 0 ≤ b ∧ b ^ 2 = x ∧ Real.sqrt x = b :=
    ⟨Real.sqrt x, Real.sqrt_nonneg _, Real.sq_sqrt hx, rfl⟩
  rw [ha, hb]
  have hA0 : (0:ℝ) ≤ 19 * a + 34 * b := by linarith
  have hS0 : (0:ℝ) ≤ a + b := by linarith
  have hapos : 0 < a := by nlinarith [ha0, ha2, hx]
  have expand : (a + b) ^ 3 = (5 * x + 1) * a + (7 * x + 3) * b := by
    have h : (a + b) ^ 3 = a * a ^ 2 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b * b ^ 2 := by ring
    rw [h, ha2, hb2]; ring
  have key : (19 * a + 34 * b) ^ (1 / 3 : ℝ) = a + b ↔ 19 * a + 34 * b = (a + b) ^ 3 := by
    constructor
    · intro h
      have h3 : ((19 * a + 34 * b) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = 19 * a + 34 * b := by
        rw [← Real.rpow_natCast ((19 * a + 34 * b) ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hA0]
        norm_num
      rw [← h3, h]
    · intro h
      rw [h, ← Real.rpow_natCast (a + b) 3, ← Real.rpow_mul hS0]
      norm_num
  rw [key, expand]
  constructor
  · intro h
    have heq : (5 * x - 18) * a + (7 * x - 31) * b = 0 := by linear_combination -h
    by_cases hc1 : x < 18 / 5
    · exfalso
      have t1 : (5 * x - 18) * a < 0 := mul_neg_of_neg_of_pos (by linarith) hapos
      have t2 : (7 * x - 31) * b ≤ 0 := by
        have h' : 0 ≤ (31 - 7 * x) * b := mul_nonneg (by linarith) hb0
        linarith
      linarith
    · push_neg at hc1
      have h1 : (5 * x - 18) * a = (31 - 7 * x) * b := by linarith
      have hsq : ((5 * x - 18) * a) ^ 2 = ((31 - 7 * x) * b) ^ 2 := by rw [h1]
      have hpoly : (x - 4) * (x ^ 2 + 103 * x - 81) = 0 := by
        linear_combination hsq - (5 * x - 18) ^ 2 * ha2 + (31 - 7 * x) ^ 2 * hb2
      have hposq : 0 < x ^ 2 + 103 * x - 81 := by nlinarith [sq_nonneg x]
      rcases mul_eq_zero.mp hpoly with h' | h'
      · linarith
      · linarith
  · intro h
    subst h
    have hfa : (a - 3) * (a + 3) = 0 := by linear_combination ha2
    have hfb : (b - 2) * (b + 2) = 0 := by linear_combination hb2
    rcases mul_eq_zero.mp hfa with h1 | h1
    · rcases mul_eq_zero.mp hfb with h2 | h2
      · linarith
      · linarith
    · linarith
```
