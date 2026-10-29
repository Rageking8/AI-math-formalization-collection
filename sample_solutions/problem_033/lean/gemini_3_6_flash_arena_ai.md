# Gemini 3.6 Flash (Arena AI)

Model: `gemini-3.6-flash` (via Arena AI)\
Date: `17 August 2026`\
Line count: `10`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  have h : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 =
      2 * (x ^ 2 + 5 / 4 * x - 1 / 5) ^ 2 + 147 / 40 * (x + 80 / 49) ^ 2 + 152 / 1225 := by ring
  rw [h]
  have h1 : 0 ≤ 2 * (x ^ 2 + 5 / 4 * x - 1 / 5) ^ 2 := by positivity
  have h2 : 0 ≤ 147 / 40 * (x + 80 / 49) ^ 2 := by positivity
  have h3 : (0 : ℝ) < 152 / 1225 := by positivity
  linarith
```
