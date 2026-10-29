# Claude Opus 5 Max (Arena AI)

Model: `claude-opus-5-max` (via Arena AI)\
Date: `3 August 2026`\
Line count: `24`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem positive_solutions_sqrt_eq (x : ℝ) (hx : 0 < x) :
    Real.sqrt (2 * (x - 3) ^ 2 + 4) = Real.sqrt (12 / x) ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have hA : (0:ℝ) ≤ 2 * (x - 3) ^ 2 + 4 := by positivity
  have hB : (0:ℝ) ≤ 12 / x := le_of_lt (div_pos (by norm_num) hx)
  constructor
  · intro h
    -- square both sides
    have h3 : Real.sqrt (2 * (x - 3) ^ 2 + 4) ^ 2 = Real.sqrt (12 / x) ^ 2 := by rw [h]
    rw [Real.sq_sqrt hA, Real.sq_sqrt hB] at h3
    -- clear the denominator
    have h4 : (2 * (x - 3) ^ 2 + 4) * x = 12 := by
      rw [h3]
      field_simp
    -- factor the resulting cubic: 2(x-1)(x-2)(x-3) = 0
    have h5 : (x - 1) * ((x - 2) * (x - 3)) = 0 := by linear_combination h4 / 2
    rcases mul_eq_zero.mp h5 with h6 | h6
    · left; linarith
    · rcases mul_eq_zero.mp h6 with h7 | h7
      · right; left; linarith
      · right; right; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num
```
