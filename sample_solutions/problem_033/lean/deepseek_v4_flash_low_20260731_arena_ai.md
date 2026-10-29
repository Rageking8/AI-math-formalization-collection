# DeepSeek V4 Flash Low 20260731 (Arena AI)

Model: `deepseek-v4-flash-low-20260731` (via Arena AI)\
Date: `17 August 2026`\
Line count: `14`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  have h_eq : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 =
      2 * (x ^ 2 + (5 / 4) * x - 5 / 32) ^ 2 +
      (7 / 2) * (x + 377 / 224) ^ 2 + 3717 / 100352 := by
    ring
  rw [h_eq]
  have h1 : 0 ≤ 2 * (x ^ 2 + (5 / 4) * x - 5 / 32) ^ 2 := by
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg _)
  have h2 : 0 ≤ (7 / 2) * (x + 377 / 224) ^ 2 := by
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 2) (sq_nonneg _)
  have h3 : (3717 : ℝ) / 100352 > 0 := by norm_num
  linarith
```
