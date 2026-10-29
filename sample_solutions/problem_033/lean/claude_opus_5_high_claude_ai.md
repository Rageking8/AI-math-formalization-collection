# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `6 August 2026`\
Line count: `5`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  nlinarith [sq_nonneg (x ^ 2 + 5 / 4 * x - 1 / 5), sq_nonneg (x + 80 / 49), sq_nonneg x,
    sq_nonneg (x ^ 2 + x)]
```
