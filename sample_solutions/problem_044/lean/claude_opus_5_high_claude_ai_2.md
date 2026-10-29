# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `1 September 2026`\
Line count: `22`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem pos_reals_pow_eq_one (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x ^ (y ^ x) = y ∧ y ^ (x ^ y) = x ↔ x = 1 ∧ y = 1 := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; simp⟩
  obtain ⟨h1, h2⟩ := h
  have p := Real.rpow_pos_of_pos hy x
  have e1 : y ^ x * Real.log x = Real.log y := by rw [← Real.log_rpow hx, h1]
  have e2 : x ^ y * Real.log y = Real.log x := by rw [← Real.log_rpow hy, h2]
  have hA : Real.log x = 0 := by
    rcases mul_eq_zero.1 (show Real.log x * (x ^ y * y ^ x - 1) = 0 by
      linear_combination x ^ y * e1 + e2) with h | h
    · exact h
    have h3 : y * Real.log x + x * Real.log y = 0 := by
      rw [← Real.log_rpow hx, ← Real.log_rpow hy,
        ← Real.log_mul (Real.rpow_pos_of_pos hx y).ne' p.ne',
        show x ^ y * y ^ x = 1 by linarith, Real.log_one]
    rcases mul_eq_zero.1 (show Real.log x * (y + x * y ^ x) = 0 by
      linear_combination h3 + x * e1) with h4 | h4
    exacts [h4, by linarith [mul_pos hx p]]
  exact ⟨by rw [← Real.exp_log hx, hA, Real.exp_zero],
    by rw [← Real.exp_log hy, ← e1, hA, mul_zero, Real.exp_zero]⟩
```
