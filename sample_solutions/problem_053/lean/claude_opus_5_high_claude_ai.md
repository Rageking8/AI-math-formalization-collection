# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `14 August 2026`\
Line count: `21`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_real_solutions_x20_7x11 (x : ℝ) :
    x ^ 20 - 7 * x ^ 11 + 10 * x ^ 10 - 5 * x + 4 ≠ 0 := by
  -- tangent line at x = 1 :  x^10 - 10x + 9 = (x-1)^2 * q(x),  q > 0
  have hq : (0:ℝ) < (x ^ 4 + x ^ 3) ^ 2 + 2 * (x ^ 3 + x ^ 2) ^ 2 + 3 * (x ^ 2 + x) ^ 2
      + 4 * (x + 1) ^ 2 + 5 := by positivity
  have hT1 : (0:ℝ) ≤ x ^ 10 - 10 * x + 9 := by
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) hq.le]
  have hx10 : (0:ℝ) ≤ x ^ 10 := by positivity
  have hA : (0:ℝ) ≤ x ^ 10 * (x ^ 10 - 10 * x + 9) := mul_nonneg hx10 hT1
  -- tangent line at x = 4/5 :  x^10 - 10(4/5)^9 x + 9(4/5)^10 = (x - 4/5)^2 * Q(x),  Q > 0
  have hQ : (0:ℝ) < (x ^ 4 + (4/5) * x ^ 3) ^ 2 + (32/25) * (x ^ 3 + (4/5) * x ^ 2) ^ 2
      + (768/625) * (x ^ 2 + (4/5) * x) ^ 2 + (16384/15625) * (x + 4/5) ^ 2
      + 65536/78125 := by positivity
  have hB : (0:ℝ) ≤ x ^ 10 - (524288/390625) * x + 9437184/9765625 := by
    nlinarith [mul_nonneg (sq_nonneg (x - 4/5)) hQ.le]
  have hC : (0:ℝ) ≤ (x ^ 10 - 1) ^ 2 := sq_nonneg _
  have hD : (0:ℝ) ≤ x ^ 20 := by positivity
  intro h
  linarith [hA, hB, hC, hD]
```
