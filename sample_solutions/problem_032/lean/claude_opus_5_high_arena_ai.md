# Claude Opus 5 High (Arena AI)

Model: `claude-opus-5-high` (via Arena AI)\
Date: `17 August 2026`\
Line count: `5`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  nlinarith [sq_nonneg (x ^ 2 - 2 * x + 16 / 25), sq_nonneg (519 * x - 944),
             sq_nonneg x, sq_nonneg (x - 1)]
```
