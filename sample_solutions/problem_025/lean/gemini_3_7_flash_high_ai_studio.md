# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `2 September 2026`\
Line count: `12`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem positive_solutions_sqrt_eq (x : ℝ) (hx : 0 < x) :
    Real.sqrt (2 * (x - 3) ^ 2 + 4) = Real.sqrt (12 / x) ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  have h1 : 0 ≤ 2 * (x - 3) ^ 2 + 4 := by positivity
  have h2 : 0 ≤ 12 / x := by positivity
  rw [Real.sqrt_inj h1 h2]
  rw [eq_div_iff hx.ne']
  rw [← sub_eq_zero]
  have h_poly : (2 * (x - 3) ^ 2 + 4) * x - 12 = 2 * (x - 1) * (x - 2) * (x - 3) := by ring
  rw [h_poly]
  simp [mul_eq_zero, sub_eq_zero, or_assoc]
```
