# Gemini 3.5 Flash High (Arena AI)

Model: `gemini-3.5-flash-high` (via Arena AI)\
Date: `17 August 2026`\
Line count: `9`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  have h : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 =
      (x ^ 2 - 2 * x + (1 / 2 : ℝ)) ^ 2 + (23 / 8 : ℝ) * (x - (40 / 23 : ℝ)) ^ 2 + (5 / 92 : ℝ) := by ring
  rw [h]
  have h1 := sq_nonneg (x ^ 2 - 2 * x + (1 / 2 : ℝ))
  have h2 := sq_nonneg (x - (40 / 23 : ℝ))
  linarith
```
