# Claude Sonnet 5 High (Arena AI)

Model: `claude-sonnet-5-high` (via Arena AI)\
Date: `17 August 2026`\
Line count: `21`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  set s := Real.sqrt (17/8) with hs_def
  have hs2 : s ^ 2 = 17/8 := by
    rw [hs_def]; exact Real.sq_sqrt (by norm_num)
  have hs_nonneg : s ≥ 0 := by rw [hs_def]; exact Real.sqrt_nonneg _
  have hbound : s < 47/32 := by
    by_contra h
    push_neg at h
    have h2 : (47/32:ℝ) * (47/32) ≤ s * s := mul_le_mul h h (by norm_num) hs_nonneg
    nlinarith [hs2, h2]
  have key : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 
      = (x^2 - (2+s)*x + 3) * (x^2 - (2-s)*x + 3) := by
    linear_combination x^2 * hs2
  have f1 : x^2 - (2+s)*x + 3 > 0 := by
    nlinarith [sq_nonneg (x - (2+s)/2), hs2, hbound]
  have f2 : x^2 - (2-s)*x + 3 > 0 := by
    nlinarith [sq_nonneg (x - (2-s)/2), hs2, hs_nonneg]
  rw [key]
  exact mul_pos f1 f2
```
