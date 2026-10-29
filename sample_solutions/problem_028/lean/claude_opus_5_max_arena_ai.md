# Claude Opus 5 Max (Arena AI)

Model: `claude-opus-5-max` (via Arena AI)\
Date: `17 August 2026`\
Line count: `51`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem unique_real_solution_nested_radical (x : ℝ) (hx : 0 ≤ x) :
    (19 * Real.sqrt (2 * x + 1) + 34 * Real.sqrt x) ^ (1 / 3 : ℝ) =
      Real.sqrt (2 * x + 1) + Real.sqrt x ↔ x = 4 := by
  have key : ∀ A c : ℝ, 0 ≤ A → 0 ≤ c → (A ^ (1 / 3 : ℝ) = c ↔ A = c ^ 3) := by
    intro A c hA0 hc0
    constructor
    · intro hAc
      rw [← hAc, ← Real.rpow_natCast (A ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hA0]
      norm_num
    · intro hAc
      rw [hAc, ← Real.rpow_natCast c 3, ← Real.rpow_mul hc0]
      norm_num
  have h2x : (0 : ℝ) < 2 * x + 1 := by linarith
  have ha0 : 0 < Real.sqrt (2 * x + 1) := Real.sqrt_pos.mpr h2x
  have hb0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have ha2 : Real.sqrt (2 * x + 1) ^ 2 = 2 * x + 1 := Real.sq_sqrt h2x.le
  have hb2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hA : (0 : ℝ) ≤ 19 * Real.sqrt (2 * x + 1) + 34 * Real.sqrt x := by linarith
  have hc : (0 : ℝ) ≤ Real.sqrt (2 * x + 1) + Real.sqrt x := by linarith
  constructor
  · intro h
    have hcube : 19 * Real.sqrt (2 * x + 1) + 34 * Real.sqrt x =
        (Real.sqrt (2 * x + 1) + Real.sqrt x) ^ 3 := (key _ _ hA hc).mp h
    have hkey : (5 * x - 18) * Real.sqrt (2 * x + 1) + (7 * x - 31) * Real.sqrt x = 0 := by
      linear_combination -hcube - (Real.sqrt (2 * x + 1) + 3 * Real.sqrt x) * ha2 -
        (3 * Real.sqrt (2 * x + 1) + Real.sqrt x) * hb2
    have hpoly : (x - 4) * (x ^ 2 + 103 * x - 81) = 0 := by
      linear_combination ((5 * x - 18) * Real.sqrt (2 * x + 1) -
          (7 * x - 31) * Real.sqrt x) * hkey - (5 * x - 18) ^ 2 * ha2 +
        (31 - 7 * x) ^ 2 * hb2
    rcases mul_eq_zero.mp hpoly with h1 | h1
    · linarith
    · exfalso
      have hx1 : x ≤ 81 / 103 := by nlinarith [sq_nonneg x]
      have hlt : (5 * x - 18) * Real.sqrt (2 * x + 1) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) ha0
      have hle : 0 ≤ (31 - 7 * x) * Real.sqrt x := mul_nonneg (by linarith) hb0
      linarith
  · intro h
    refine (key _ _ hA hc).mpr ?_
    subst h
    have h9 : Real.sqrt (2 * 4 + 1) = 3 := by
      rw [show (2 : ℝ) * 4 + 1 = 3 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [h9, h4]
    norm_num
```
