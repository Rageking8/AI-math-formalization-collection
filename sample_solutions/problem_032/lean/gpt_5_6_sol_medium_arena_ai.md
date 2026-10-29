# GPT-5.6 Sol Medium (Arena AI)

Model: `gpt-5.6-sol-medium` (via Arena AI)\
Date: `17 August 2026`\
Line count: `19`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  have h₁ : 0 < x ^ 2 - (83 / 24 : ℝ) * x + 3 := by
    calc
      x ^ 2 - (83 / 24 : ℝ) * x + 3 =
          (x - (83 / 48 : ℝ)) ^ 2 + (23 / 2304 : ℝ) := by ring
      _ > 0 := by positivity
  have h₂ : 0 < x ^ 2 - (13 / 24 : ℝ) * x + 3 := by
    calc
      x ^ 2 - (13 / 24 : ℝ) * x + 3 =
          (x - (13 / 48 : ℝ)) ^ 2 + (6743 / 2304 : ℝ) := by ring
      _ > 0 := by positivity
  calc
    x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 =
        (x ^ 2 - (83 / 24 : ℝ) * x + 3) *
          (x ^ 2 - (13 / 24 : ℝ) * x + 3) +
        x ^ 2 / 576 := by ring
    _ > 0 := add_pos_of_pos_of_nonneg (mul_pos h₁ h₂) (by positivity)
```
