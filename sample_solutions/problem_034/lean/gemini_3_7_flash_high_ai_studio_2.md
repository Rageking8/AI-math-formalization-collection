# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `18 August 2026`\
Line count: `13`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem polynomial_pos_3x8_2x4 (x y : ℝ) :
    3 * x ^ 8 + 2 * x ^ 4 * y ^ 4 - 7 * x ^ 2 * y ^ 2 + 2 * y ^ 6 + 5 / 3 > 0 := by
  have h : 3 * x ^ 8 + 2 * x ^ 4 * y ^ 4 - 7 * x ^ 2 * y ^ 2 + 2 * y ^ 6 + 5 / 3 =
      3 * (x ^ 4 - 1 / 2) ^ 2 +
      3 * (x ^ 2 - 5 / 6 * y ^ 2) ^ 2 +
      2 * (y ^ 3 - 25 / 36 * y) ^ 2 +
      (25 / 36) * (y ^ 2 - 25 / 36) ^ 2 +
      2 * (x ^ 2 * y ^ 2 - 1 / 2) ^ 2 +
      3815 / 46656 := by ring
  rw [h]
  positivity
```
