# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `30 August 2026`\
Line count: `6`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem polynomial_pos_3x8_2x4 (x y : ℝ) :
    3 * x ^ 8 + 2 * x ^ 4 * y ^ 4 - 7 * x ^ 2 * y ^ 2 + 2 * y ^ 6 + 5 / 3 > 0 := by
  nlinarith [sq_nonneg y, sq_nonneg (x^2 - 5/8), sq_nonneg (y^2 - 4/5),
    sq_nonneg (x^2*y^2 - 1/2), sq_nonneg (x^4 - 2/3*y^2)]
```
