# Claude Opus 5 Max (Arena AI)

Model: `claude-opus-5-max` (via Arena AI)\
Date: `27 July 2026`\
Line count: `20`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_real_solutions_x2_y2_4 (x y : ℝ) :
    x^2 + y^2 + 4 ≠ 2 * Real.sqrt (x^2 * y + x * y^2 + x + y) := by
  intro heq
  have hpos : 0 < Real.sqrt (x ^ 2 * y + x * y ^ 2 + x + y) := by
    linarith [sq_nonneg x, sq_nonneg y]
  have hnneg : 0 < x ^ 2 * y + x * y ^ 2 + x + y := Real.sqrt_pos.mp hpos
  have hsq : Real.sqrt (x ^ 2 * y + x * y ^ 2 + x + y) ^ 2 = x ^ 2 * y + x * y ^ 2 + x + y :=
    Real.sq_sqrt hnneg.le
  have key : 4 * (x ^ 2 * y + x * y ^ 2 + x + y) = (x ^ 2 + y ^ 2 + 4) ^ 2 := by
    rw [heq, mul_pow, hsq]; ring
  have hQ : (2 : ℝ) ≤ x ^ 2 + y ^ 2 + 3 - x - y - x * y := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  have hR : (4 : ℝ) ≤ x ^ 2 + y ^ 2 + 5 + x + y + x * y := by
    nlinarith [sq_nonneg (x + y), sq_nonneg (x + 1), sq_nonneg (y + 1)]
  have hprod : (2 : ℝ) * 4 ≤
      (x ^ 2 + y ^ 2 + 3 - x - y - x * y) * (x ^ 2 + y ^ 2 + 5 + x + y + x * y) :=
    mul_le_mul hQ hR (by norm_num) (by linarith)
  nlinarith [key, hprod, sq_nonneg (x + y - x * y - 1)]
```
