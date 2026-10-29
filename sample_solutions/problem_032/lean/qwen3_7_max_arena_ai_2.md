# Qwen 3.7 Max (Arena AI)

Model: `qwen3.7-max` (via Arena AI)\
Date: `17 August 2026`\
Line count: `13`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  -- Establish the algebraic identity decomposing the polynomial into a sum of squares
  have h : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 = 
           (x ^ 2 - 2 * x + 5 / 8) ^ 2 + 21 / 8 * (x - 38 / 21) ^ 2 + 19 / 1344 := by
    ring
  
  -- Rewrite the goal using our identity
  rw [h]
  
  -- Use `nlinarith` along with the fact that squares of real numbers are non-negative
  nlinarith [sq_nonneg (x ^ 2 - 2 * x + 5 / 8), sq_nonneg (x - 38 / 21)]
```
