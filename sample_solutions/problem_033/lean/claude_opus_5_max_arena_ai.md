# Claude Opus 5 Max (Arena AI)

Model: `claude-opus-5-max` (via Arena AI)\
Date: `17 August 2026`\
Line count: `5`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  nlinarith [sq_nonneg (20*x^2 + 25*x - 4), sq_nonneg (49*x + 80), sq_nonneg x,
             sq_nonneg (x + 1), sq_nonneg (x^2 + x)]
```
