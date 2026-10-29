# DeepSeek V4 Pro Low (Arena AI)

Model: `deepseek-v4-pro-low` (via Arena AI)\
Date: `17 August 2026`\
Line count: `13`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  have h1 : 0 ≤ (x^2 + (11:ℝ)/4 * x + 113/64)^2 := sq_nonneg _
  have h2 : 0 ≤ (x^2 - (1:ℝ)/4 * x - 165/64)^2 := sq_nonneg _
  have h3 :
      2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 =
        (x^2 + (11:ℝ)/4 * x + 113/64)^2 +
          (x^2 - (1:ℝ)/4 * x - 165/64)^2 + 483/2048 := by
    ring
  rw [h3]
  have hc : (0:ℝ) < 483/2048 := by norm_num
  linarith
```
