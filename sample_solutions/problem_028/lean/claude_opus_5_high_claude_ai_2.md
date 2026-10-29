# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `18 August 2026`\
Line count: `29`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem unique_real_solution_nested_radical (x : ℝ) (hx : 0 ≤ x) :
    (19 * Real.sqrt (2 * x + 1) + 34 * Real.sqrt x) ^ (1 / 3 : ℝ) =
      Real.sqrt (2 * x + 1) + Real.sqrt x ↔ x = 4 := by
  have hb : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have ha : Real.sqrt (2 * x + 1) ^ 2 = 2 * x + 1 := Real.sq_sqrt (by linarith)
  have h9 := Real.sqrt_nonneg x
  have h8 : 1 ≤ Real.sqrt (2 * x + 1) := by nlinarith [Real.sqrt_nonneg (2 * x + 1)]
  set a := Real.sqrt (2 * x + 1); set b := Real.sqrt x
  have p : (0:ℝ) ≤ 19 * a + 34 * b := by linarith
  have q : (0:ℝ) ≤ a + b := by linarith
  rw [show (19 * a + 34 * b) ^ (1 / 3 : ℝ) = a + b ↔ 19 * a + 34 * b = (a + b) ^ 3 from
      ⟨fun h => by rw [← h, ← Real.rpow_natCast _ 3, ← Real.rpow_mul p]; norm_num,
       fun h => by rw [h, ← Real.rpow_natCast (a + b) 3, ← Real.rpow_mul q]; norm_num⟩]
  refine ⟨fun h => ?_, fun h => by
    rw [show a = 3 by nlinarith, show b = 2 by nlinarith]; norm_num⟩
  have k : a * (5 * x - 18) + b * (7 * x - 31) = 0 := by
    linear_combination -h - (a + 3 * b) * ha - (3 * a + b) * hb
  have m : 18 ≤ 5 * x := by
    by_contra c
    push_neg at c
    nlinarith [mul_nonneg h9 (by linarith : (0:ℝ) ≤ 31 - 7 * x),
      mul_nonneg (by linarith : (0:ℝ) ≤ a - 1) (by linarith : (0:ℝ) ≤ 18 - 5 * x)]
  rcases mul_eq_zero.1 (show (x - 4) * (x ^ 2 + 103 * x - 81) = 0 by
    linear_combination (a * (5 * x - 18) - b * (7 * x - 31)) * k - (5 * x - 18) ^ 2 * ha +
      (7 * x - 31) ^ 2 * hb) with h5 | h5
  · linarith
  · linarith [sq_nonneg x]
```
