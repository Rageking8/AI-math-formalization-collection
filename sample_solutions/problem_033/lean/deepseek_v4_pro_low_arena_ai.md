# DeepSeek V4 Pro Low (Arena AI)

Model: `deepseek-v4-pro-low` (via Arena AI)\
Date: `17 August 2026`\
Line count: `11`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  have h : 248 * (2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10) =
      31 * (4 * x ^ 2 + 5 * x - 1) ^ 2 + (31 * x + 49) ^ 2 + 48 := by
    ring
  have h1 := sq_nonneg (4 * x ^ 2 + 5 * x - 1)
  have h2 := sq_nonneg (31 * x + 49)
  have hpos : 0 < 31 * (4 * x ^ 2 + 5 * x - 1) ^ 2 + (31 * x + 49) ^ 2 + 48 := by
    nlinarith
  nlinarith [h, hpos]
```
