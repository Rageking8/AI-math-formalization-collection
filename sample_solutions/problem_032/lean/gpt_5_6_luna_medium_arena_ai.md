# GPT-5.6 Luna Medium (Arena AI)

Model: `gpt-5.6-luna-medium` (via Arena AI)\
Date: `17 August 2026`\
Line count: `13`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  have hdecomp :
      x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 =
        (((x - 1) ^ 2 - (9 / 16 : ℝ)) ^ 2
          + 3 * (x - 1 - (17 / 24 : ℝ)) ^ 2
          + (41 / 768 : ℝ)) := by
    ring
  rw [hdecomp]
  have h₁ : 0 ≤ ((x - 1) ^ 2 - (9 / 16 : ℝ)) ^ 2 := sq_nonneg _
  have h₂ : 0 ≤ (x - 1 - (17 / 24 : ℝ)) ^ 2 := sq_nonneg _
  nlinarith
```
