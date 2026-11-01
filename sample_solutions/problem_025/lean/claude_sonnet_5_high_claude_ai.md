# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `7 September 2026`\
Line count: `21`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem positive_solutions_sqrt_eq (x : ℝ) (hx : 0 < x) :
    Real.sqrt (2 * (x - 3) ^ 2 + 4) = Real.sqrt (12 / x) ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  have h1 : (0:ℝ) ≤ 2 * (x - 3) ^ 2 + 4 := by positivity
  have h2 : (0:ℝ) ≤ 12 / x := by positivity
  rw [Real.sqrt_inj h1 h2]
  constructor
  · intro h
    have hx' : x ≠ 0 := ne_of_gt hx
    have heq : (2 * (x - 3) ^ 2 + 4) * x = 12 := by
      rw [h]
      field_simp
    have hfactor : (x - 1) * (x - 2) * (x - 3) = 0 := by
      linear_combination (1/2 : ℝ) * heq
    rcases mul_eq_zero.mp hfactor with h12 | h3
    · rcases mul_eq_zero.mp h12 with ha | hb
      · exact Or.inl (sub_eq_zero.mp ha)
      · exact Or.inr (Or.inl (sub_eq_zero.mp hb))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h3))
  · rintro (rfl | rfl | rfl) <;> norm_num
```
