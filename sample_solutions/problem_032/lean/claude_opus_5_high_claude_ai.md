# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `6 August 2026`\
Line count: `4`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  nlinarith [sq_nonneg (x ^ 2 - 2 * x + 1 / 2), sq_nonneg (23 * x - 40)]
```
