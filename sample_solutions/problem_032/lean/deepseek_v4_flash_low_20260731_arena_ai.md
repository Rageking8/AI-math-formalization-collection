# DeepSeek V4 Flash Low 20260731 (Arena AI)

Model: `deepseek-v4-flash-low-20260731` (via Arena AI)\
Date: `17 August 2026`\
Line count: `11`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  have h : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 =
      (x^2 - 2*x + (1/2 : ℝ))^2 + ((23/8 : ℝ) * (x - (40/23 : ℝ))^2) + (5/92 : ℝ) := by
    ring_nf
  rw [h]
  have h1 : 0 ≤ (x^2 - 2*x + (1/2 : ℝ))^2 := sq_nonneg _
  have h2 : 0 ≤ ((23/8 : ℝ) * (x - (40/23 : ℝ))^2) := by positivity
  have h3 : (0:ℝ) < (5/92 : ℝ) := by norm_num
  nlinarith [h1, h2, h3]
```
