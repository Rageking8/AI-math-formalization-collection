# GPT-5.6 Terra Medium (Arena AI)

Model: `gpt-5.6-terra-medium` (via Arena AI)\
Date: `17 August 2026`\
Line count: `11`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  calc
    x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 =
        (((x - 1) ^ 2 - (1 / 2 : ℝ)) ^ 2
          + (23 / 8 : ℝ) * ((x - 1) - (17 / 23 : ℝ)) ^ 2
          + (5 / 92 : ℝ)) := by
            ring
    _ > 0 := by
      positivity
```
