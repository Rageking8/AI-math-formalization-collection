# Qwen 3.7 Max (Arena AI)

Model: `qwen3.7-max` (via Arena AI)\
Date: `17 August 2026`\
Line count: `8`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  have h : 184 * (x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9) = 
           184 * (x ^ 2 - 2 * x + 1 / 2) ^ 2 + (23 * x - 40) ^ 2 + 10 := by
    ring
  
  nlinarith [sq_nonneg (x ^ 2 - 2 * x + 1 / 2), sq_nonneg (23 * x - 40)]
```
