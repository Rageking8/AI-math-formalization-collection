# Claude Opus 4.7 Thinking (Arena AI)

Model: `claude-opus-4-7-thinking` (via Arena AI)\
Date: `3 August 2026`\
Line count: `18`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem positive_solutions_sqrt_eq (x : ℝ) (hx : 0 < x) :
    Real.sqrt (2 * (x - 3) ^ 2 + 4) = Real.sqrt (12 / x) ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  have hx' : x ≠ 0 := ne_of_gt hx
  constructor
  · intro h
    have hlhs : 0 ≤ 2 * (x - 3) ^ 2 + 4 := by positivity
    have hrhs : 0 ≤ 12 / x := by positivity
    have h1 : 2 * (x - 3) ^ 2 + 4 = 12 / x := (Real.sqrt_inj hlhs hrhs).mp h
    have h2 : (2 * (x - 3) ^ 2 + 4) * x = 12 := (eq_div_iff hx').mp h1
    have h3 : (x - 1) * (x - 2) * (x - 3) = 0 := by linear_combination h2 / 2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · left; linarith
      · right; left; linarith
    · right; right; linarith
  · rintro (rfl | rfl | rfl) <;> (congr 1; norm_num)
```
