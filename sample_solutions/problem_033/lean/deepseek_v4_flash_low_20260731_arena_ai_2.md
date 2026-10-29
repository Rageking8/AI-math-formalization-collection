# DeepSeek V4 Flash Low 20260731 (Arena AI)

Model: `deepseek-v4-flash-low-20260731` (via Arena AI)\
Date: `17 August 2026`\
Line count: `11`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  have h : (2:ℝ) * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 = 
           2 * (x^2 + (5/4) * x - 9/32)^2 + (2 * x + 397/128)^2 + (3639/16384) := by
    ring_nf
  rw [h]
  have h1 : 0 ≤ (x^2 + (5/4) * x - 9/32)^2 := sq_nonneg _
  have h2 : 0 ≤ (2 * x + 397/128)^2 := sq_nonneg _
  have h3 : (0:ℝ) < 3639/16384 := by norm_num
  nlinarith
```
