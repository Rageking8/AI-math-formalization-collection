# GPT-5.6 Terra xHigh (Arena AI)

Model: `gpt-5.6-terra-xhigh` (via Arena AI)\
Date: `17 August 2026`\
Line count: `6`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  have h₁ := sq_nonneg (x ^ 2 + (5 / 4 : ℝ) * x - 1 / 2)
  have h₂ := sq_nonneg (x + 18 / 13 : ℝ)
  nlinarith
```
