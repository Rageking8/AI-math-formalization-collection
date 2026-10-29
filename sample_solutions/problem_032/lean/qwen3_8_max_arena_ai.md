# Qwen 3.8 Max (Arena AI)

Model: `qwen3.8-max` (via Arena AI)\
Date: `17 August 2026`\
Line count: `8`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  have h : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 =
      (x ^ 2 - 2 * x + 1 / 2) ^ 2 + (23 / 8 : ℝ) * (x - 40 / 23) ^ 2 + (5 / 92 : ℝ) := by
    ring
  rw [h]
  nlinarith [sq_nonneg (x ^ 2 - 2 * x + 1 / 2), sq_nonneg (x - 40 / 23)]
```
