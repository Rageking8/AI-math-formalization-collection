# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `2 September 2026`\
Line count: `12`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem no_real_solutions_x20_7x11 (x : ℝ) :
    x ^ 20 - 7 * x ^ 11 + 10 * x ^ 10 - 5 * x + 4 ≠ 0 := by
  have a : (0:ℝ) ≤ x ^ 10 := by positivity
  have b : (0:ℝ) ≤ x ^ 10 - 10 * x + 9 := by
    nlinarith [sq_nonneg ((x - 1) * (x ^ 4 + x ^ 3)), sq_nonneg ((x - 1) * (x ^ 3 + x ^ 2)),
      sq_nonneg ((x - 1) * (x ^ 2 + x)), sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1)]
  have c : (0:ℝ) ≤ 243 * x ^ 10 - 360 * x + 263 := by
    nlinarith [sq_nonneg (x ^ 3 * (3 * x ^ 2 - 2)), sq_nonneg (x ^ 2 * (3 * x ^ 2 - 2)),
      sq_nonneg (x * (3 * x ^ 2 - 2)), sq_nonneg (3 * x ^ 2 - 2), sq_nonneg (4 * x - 3)]
  exact ne_of_gt (by linarith [mul_nonneg a b, mul_nonneg a c, a, c])
```
