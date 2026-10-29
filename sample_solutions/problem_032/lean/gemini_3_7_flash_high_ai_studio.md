# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `20 August 2026`\
Line count: `7`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  have h : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 =
      (x ^ 2 - 2 * x + 1 / 2) ^ 2 + (23 / 8 : ℝ) * (x - 40 / 23) ^ 2 + 5 / 92 := by ring
  rw [h]
  positivity
```
