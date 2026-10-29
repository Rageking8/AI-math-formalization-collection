# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `22 August 2026`\
Line count: `6`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  have h : 104 * (2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10) =
      13 * (4 * x ^ 2 + 5 * x - 2) ^ 2 + 3 * (13 * x + 18) ^ 2 + 16 := by ring
  linarith [sq_nonneg (4 * x ^ 2 + 5 * x - 2), sq_nonneg (13 * x + 18)]
```
