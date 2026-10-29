# DeepSeek V4 Flash High 20260731 (Arena AI)

Model: `deepseek-v4-flash-high-20260731` (via Arena AI)\
Date: `17 August 2026`\
Line count: `11`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  have h : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 =
      (x^2 - 2 * x + (13 / 32 : ℝ))^2 + ((7 / 4 : ℝ) * x - (83 / 28 : ℝ))^2 + (2407 / 50176 : ℝ) := by
    ring
  have h1 : 0 ≤ (x^2 - 2 * x + (13 / 32 : ℝ))^2 := sq_nonneg _
  have h2 : 0 ≤ ((7 / 4 : ℝ) * x - (83 / 28 : ℝ))^2 := sq_nonneg _
  have h3 : 0 < (2407 / 50176 : ℝ) := by norm_num
  rw [h]
  nlinarith
```
