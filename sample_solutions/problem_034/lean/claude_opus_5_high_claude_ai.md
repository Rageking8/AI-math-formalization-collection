# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `6 August 2026`\
Line count: `10`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem polynomial_pos_3x8_2x4 (x y : ℝ) :
    3 * x ^ 8 + 2 * x ^ 4 * y ^ 4 - 7 * x ^ 2 * y ^ 2 + 2 * y ^ 6 + 5 / 3 > 0 := by
  nlinarith [sq_nonneg (x ^ 4 - 539 / 1200),
             sq_nonneg (x ^ 2 - 10 / 11 * y ^ 2),
             mul_nonneg (sq_nonneg y) (sq_nonneg (y ^ 2 - 3 / 4)),
             sq_nonneg (y ^ 2 - 99 / 136),
             sq_nonneg (x ^ 2 * y ^ 2 - 21 / 40),
             sq_nonneg x, sq_nonneg y]
```
