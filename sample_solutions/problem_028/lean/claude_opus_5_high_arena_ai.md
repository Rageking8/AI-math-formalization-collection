# Claude Opus 5 High (Arena AI)

Model: `claude-opus-5-high` (via Arena AI)\
Date: `17 August 2026`\
Line count: `58`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem unique_real_solution_nested_radical (x : ℝ) (hx : 0 ≤ x) :
    (19 * Real.sqrt (2 * x + 1) + 34 * Real.sqrt x) ^ (1 / 3 : ℝ) =
      Real.sqrt (2 * x + 1) + Real.sqrt x ↔ x = 4 := by
  have h2x : (0:ℝ) ≤ 2 * x + 1 := by linarith
  have ha2 : Real.sqrt (2 * x + 1) ^ 2 = 2 * x + 1 := Real.sq_sqrt h2x
  have hb2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have ha0 : (0:ℝ) ≤ Real.sqrt (2 * x + 1) := Real.sqrt_nonneg _
  have hb0 : (0:ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg _
  have ha1 : (1:ℝ) ≤ Real.sqrt (2 * x + 1) := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 2 * x + 1 by linarith)
    simpa using h
  have hpow : ∀ y : ℝ, 0 ≤ y → (y ^ (1 / 3 : ℝ)) ^ 3 = y := by
    intro y hy
    rw [← Real.rpow_natCast (y ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hy]
    norm_num
  have hpow2 : ∀ y : ℝ, 0 ≤ y → (y ^ 3) ^ (1 / 3 : ℝ) = y := by
    intro y hy
    rw [← Real.rpow_natCast y 3, ← Real.rpow_mul hy]
    norm_num
  constructor
  · intro h
    have hA : (0:ℝ) ≤ 19 * Real.sqrt (2 * x + 1) + 34 * Real.sqrt x := by linarith
    have hcube := hpow _ hA
    rw [h] at hcube
    have expand : (Real.sqrt (2 * x + 1) + Real.sqrt x) ^ 3
        = (5 * x + 1) * Real.sqrt (2 * x + 1) + (7 * x + 3) * Real.sqrt x := by
      have e : (Real.sqrt (2 * x + 1) + Real.sqrt x) ^ 3
          = Real.sqrt (2 * x + 1) * Real.sqrt (2 * x + 1) ^ 2
            + 3 * Real.sqrt (2 * x + 1) ^ 2 * Real.sqrt x
            + 3 * Real.sqrt (2 * x + 1) * Real.sqrt x ^ 2
            + Real.sqrt x * Real.sqrt x ^ 2 := by ring
      rw [e, ha2, hb2]
      ring
    have key : (5 * x - 18) * Real.sqrt (2 * x + 1) = (31 - 7 * x) * Real.sqrt x := by
      linear_combination hcube - expand
    have hsq : (5 * x - 18) ^ 2 * (2 * x + 1) = (31 - 7 * x) ^ 2 * x := by
      linear_combination (-(5 * x - 18) ^ 2) * ha2 + (31 - 7 * x) ^ 2 * hb2
        + ((5 * x - 18) * Real.sqrt (2 * x + 1) + (31 - 7 * x) * Real.sqrt x) * key
    have hfac : (x - 4) * (x ^ 2 + 103 * x - 81) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h1 | h1
    · linarith
    · exfalso
      have hxle : x ≤ 81 / 103 := by nlinarith [sq_nonneg x]
      have c1 : (0:ℝ) ≤ (31 - 7 * x) * Real.sqrt x := mul_nonneg (by linarith) hb0
      have c2 : (0:ℝ) ≤ (18 - 5 * x) * (Real.sqrt (2 * x + 1) - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [key, c1, c2]
  · rintro rfl
    have e1 : Real.sqrt (2 * 4 + 1) = 3 := by
      rw [show (2:ℝ) * 4 + 1 = 3 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    have e2 : Real.sqrt (4:ℝ) = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [e1, e2, show (19:ℝ) * 3 + 34 * 2 = 5 ^ 3 by norm_num, hpow2 5 (by norm_num)]
    norm_num
```
