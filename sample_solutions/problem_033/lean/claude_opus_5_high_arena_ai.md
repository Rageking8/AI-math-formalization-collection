# Claude Opus 5 High (Arena AI)

Model: `claude-opus-5-high` (via Arena AI)\
Date: `17 August 2026`\
Line count: `5`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  nlinarith [sq_nonneg (4 * x ^ 2 + 5 * x - 2), sq_nonneg (13 * x + 18), sq_nonneg x,
    sq_nonneg (x + 1), sq_nonneg (x ^ 2 + x)]
```
