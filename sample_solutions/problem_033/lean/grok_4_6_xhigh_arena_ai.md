# Grok 4.6 xHigh (Arena AI)

Model: `grok-4.6-xhigh` (via Arena AI)\
Date: `17 August 2026`\
Line count: `26`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  have id1 : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 =
      (x + 1) ^ 2 * (2 * x ^ 2 + x + 2) + 6 * x + 8 := by ring
  have id2 : 8 * (2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10) =
      (4 * x ^ 2 - 2 * x + 9) * (2 * x + 3) ^ 2 - 2 * x - 1 := by ring
  by_cases h : x < -1 / 2
  · have eqq : 4 * x ^ 2 - 2 * x + 9 = (2 * x - 1 / 2) ^ 2 + 35 / 4 := by ring
    have hq : 0 < 4 * x ^ 2 - 2 * x + 9 := by
      rw [eqq]
      nlinarith [sq_nonneg (2 * x - 1 / 2)]
    have hprod : 0 ≤ (4 * x ^ 2 - 2 * x + 9) * (2 * x + 3) ^ 2 :=
      mul_nonneg (le_of_lt hq) (sq_nonneg _)
    have hlin : 0 < -2 * x - 1 := by linarith
    have : 0 < 8 * (2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10) := by
      linarith [id2, hprod, hlin]
    linarith
  · have eqq : 2 * x ^ 2 + x + 2 = 2 * (x + 1 / 4) ^ 2 + 15 / 8 := by ring
    have hq : 0 < 2 * x ^ 2 + x + 2 := by
      rw [eqq]
      nlinarith [sq_nonneg (x + 1 / 4)]
    have hprod : 0 ≤ (x + 1) ^ 2 * (2 * x ^ 2 + x + 2) :=
      mul_nonneg (sq_nonneg _) (le_of_lt hq)
    have hlin : 0 < 6 * x + 8 := by linarith
    linarith [id1, hprod, hlin]
```
