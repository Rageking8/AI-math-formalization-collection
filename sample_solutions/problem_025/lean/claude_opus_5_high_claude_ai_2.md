# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `13 August 2026`\
Line count: `7`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem positive_solutions_sqrt_eq (x : ℝ) (hx : 0 < x) :
    Real.sqrt (2 * (x - 3) ^ 2 + 4) = Real.sqrt (12 / x) ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  rw [Real.sqrt_inj (by positivity) (by positivity), eq_div_iff hx.ne', ← sub_eq_zero,
    show (2 * (x - 3) ^ 2 + 4) * x - 12 = 2 * ((x - 1) * ((x - 2) * (x - 3))) by ring]
  norm_num [mul_eq_zero, sub_eq_zero]
```
