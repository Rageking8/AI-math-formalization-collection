# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `18 August 2026`\
Line count: `15`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem polynomial_pos_3x8_2x4 (x y : ℝ) :
    3 * x ^ 8 + 2 * x ^ 4 * y ^ 4 - 7 * x ^ 2 * y ^ 2 + 2 * y ^ 6 + 5 / 3 > 0 := by
  have h : 3 * x ^ 8 + 2 * x ^ 4 * y ^ 4 - 7 * x ^ 2 * y ^ 2 + 2 * y ^ 6 + 5 / 3 =
      2 * (x ^ 2 * y ^ 2 - 1 / 2) ^ 2 +
      (54 / 343) * (x ^ 4) ^ 2 +
      (376 / 4563) * (y ^ 3) ^ 2 +
      (975 / 343) * (x ^ 4 - 49 / 100) ^ 2 +
      (8750 / 4563) * (y ^ 3 - 39 / 50 * y) ^ 2 +
      (175 / 234) * (y ^ 2 - 39 / 50) ^ 2 +
      (1250 / 273) * (39 / 50 * x ^ 2 - 7 / 10 * y ^ 2) ^ 2 +
      7 / 240 := by ring
  rw [h]
  positivity
```
