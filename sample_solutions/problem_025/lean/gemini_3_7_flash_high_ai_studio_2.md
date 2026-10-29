# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `2 September 2026`\
Line count: `22`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem positive_solutions_sqrt_eq (x : ℝ) (hx : 0 < x) :
    Real.sqrt (2 * (x - 3) ^ 2 + 4) = Real.sqrt (12 / x) ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  have h1 : 0 ≤ 2 * (x - 3) ^ 2 + 4 := by positivity
  have h2 : 0 ≤ 12 / x := by positivity
  rw [Real.sqrt_inj h1 h2]
  constructor
  · intro h
    have h_poly : 2 * (x - 1) * (x - 2) * (x - 3) = 0 := by
      calc 2 * (x - 1) * (x - 2) * (x - 3) = (2 * (x - 3) ^ 2 + 4) * x - 12 := by ring
      _ = (12 / x) * x - 12 := by rw [h]
      _ = 12 - 12 := by rw [div_mul_cancel₀ 12 hx.ne']
      _ = 0 := by ring
    rcases mul_eq_zero.mp h_poly with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · left; linarith
      · right; left; linarith
    · right; right; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num
```
