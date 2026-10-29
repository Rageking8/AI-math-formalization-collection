# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `22 August 2026`\
Line count: `8`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  have h : 248 * (2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10) =
      31 * (4 * x ^ 2 + 5 * x - 1) ^ 2 + (31 * x + 49) ^ 2 + 48 := by ring
  have h1 : 0 ≤ (4 * x ^ 2 + 5 * x - 1) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (31 * x + 49) ^ 2 := sq_nonneg _
  linarith
```
