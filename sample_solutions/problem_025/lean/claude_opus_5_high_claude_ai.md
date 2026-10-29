# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `2 August 2026`\
Line count: `21`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem positive_solutions_sqrt_eq (x : ℝ) (hx : 0 < x) :
    Real.sqrt (2 * (x - 3) ^ 2 + 4) = Real.sqrt (12 / x) ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have h1 : (0:ℝ) ≤ 2 * (x - 3) ^ 2 + 4 := by positivity
  have h2 : (0:ℝ) ≤ 12 / x := by positivity
  constructor
  · intro h
    have e1 : Real.sqrt (2 * (x - 3) ^ 2 + 4) ^ 2 = 2 * (x - 3) ^ 2 + 4 := Real.sq_sqrt h1
    have e2 : Real.sqrt (12 / x) ^ 2 = 12 / x := Real.sq_sqrt h2
    have h3 : 2 * (x - 3) ^ 2 + 4 = 12 / x := by rw [← e1, ← e2, h]
    have h5 : (2 * (x - 3) ^ 2 + 4) * x = 12 := by
      rw [h3]; field_simp
    have h4 : (x - 1) * ((x - 2) * (x - 3)) = 0 := by linear_combination h5 / 2
    rcases mul_eq_zero.mp h4 with h' | h'
    · left; linarith
    · rcases mul_eq_zero.mp h' with h'' | h''
      · right; left; linarith
      · right; right; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num
```
