# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `7 September 2026`\
Line count: `4`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  nlinarith [sq_nonneg (x^2 + (5/4)*x - 1/2), sq_nonneg (x + 18/13)]
```
