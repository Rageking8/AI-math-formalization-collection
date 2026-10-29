# Claude Opus 5 High (Arena AI)

Model: `claude-opus-5-high` (via Arena AI)\
Date: `17 August 2026`\
Line count: `16`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem polynomial_pos_3x8_2x4 (x y : ℝ) :
    3 * x ^ 8 + 2 * x ^ 4 * y ^ 4 - 7 * x ^ 2 * y ^ 2 + 2 * y ^ 6 + 5 / 3 > 0 := by
  have h1 : (0:ℝ) ≤ (x ^ 4 - 1 / 2) ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ (x ^ 2 * y ^ 2 - 1 / 2) ^ 2 := sq_nonneg _
  have h3 : (0:ℝ) ≤ (6 * x ^ 2 - 5 * y ^ 2) ^ 2 := sq_nonneg _
  have h4 : (0:ℝ) ≤ y ^ 2 * (y ^ 2 - 25 / 36) ^ 2 :=
    mul_nonneg (sq_nonneg y) (sq_nonneg _)
  have h5 : (0:ℝ) ≤ (y ^ 2 - 25 / 36) ^ 2 := sq_nonneg _
  have key : 12 * (3 * x ^ 8 + 2 * x ^ 4 * y ^ 4 - 7 * x ^ 2 * y ^ 2 + 2 * y ^ 6 + 5 / 3)
      = 36 * (x ^ 4 - 1 / 2) ^ 2 + 24 * (x ^ 2 * y ^ 2 - 1 / 2) ^ 2
        + (6 * x ^ 2 - 5 * y ^ 2) ^ 2 + 24 * (y ^ 2 * (y ^ 2 - 25 / 36) ^ 2)
        + (25 / 3) * (y ^ 2 - 25 / 36) ^ 2 + 3815 / 3888 := by
    ring
  linarith
```
