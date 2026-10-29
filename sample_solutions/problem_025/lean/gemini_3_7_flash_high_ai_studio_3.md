# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `2 September 2026`\
Line count: `7`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem positive_solutions_sqrt_eq (x : ℝ) (hx : 0 < x) :
    Real.sqrt (2 * (x - 3) ^ 2 + 4) = Real.sqrt (12 / x) ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  rw [Real.sqrt_inj (by positivity) (by positivity), eq_div_iff hx.ne', ← sub_eq_zero,
    show (2 * (x - 3) ^ 2 + 4) * x - 12 = 2 * (x - 1) * (x - 2) * (x - 3) by ring]
  simp [mul_eq_zero, sub_eq_zero, or_assoc]
```
