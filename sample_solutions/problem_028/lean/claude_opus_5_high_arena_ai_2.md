# Claude Opus 5 High (Arena AI)

Model: `claude-opus-5-high` (via Arena AI)\
Date: `17 August 2026`\
Line count: `60`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem unique_real_solution_nested_radical (x : ℝ) (hx : 0 ≤ x) :
    (19 * Real.sqrt (2 * x + 1) + 34 * Real.sqrt x) ^ (1 / 3 : ℝ) =
      Real.sqrt (2 * x + 1) + Real.sqrt x ↔ x = 4 := by
  have hx1 : (0:ℝ) ≤ 2 * x + 1 := by linarith
  have ha0 : 0 ≤ Real.sqrt (2 * x + 1) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have ha2 : Real.sqrt (2 * x + 1) ^ 2 = 2 * x + 1 := Real.sq_sqrt hx1
  have hb2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hsum : 0 ≤ Real.sqrt (2 * x + 1) + Real.sqrt x := by linarith
  have hlhs : 0 ≤ 19 * Real.sqrt (2 * x + 1) + 34 * Real.sqrt x := by linarith
  have key : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → (u ^ (1 / 3 : ℝ) = v ↔ u = v ^ 3) := by
    intro u v hu hv
    have hu3 : (u ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = u := by
      rw [← Real.rpow_natCast (u ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hu]
      norm_num
    have hv3 : (v ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = v := by
      rw [← Real.rpow_natCast v 3, ← Real.rpow_mul hv]
      norm_num
    constructor
    · intro h
      exact hu3.symm.trans (by rw [h])
    · intro h
      rw [h]
      exact hv3
  rw [key _ _ hlhs hsum]
  constructor
  · intro h
    have hE : Real.sqrt (2 * x + 1) * (5 * x - 18) + Real.sqrt x * (7 * x - 31) = 0 := by
      linear_combination (-1 : ℝ) * h - (Real.sqrt (2 * x + 1) + 3 * Real.sqrt x) * ha2 -
        (3 * Real.sqrt (2 * x + 1) + Real.sqrt x) * hb2
    have hfac : (x - 4) * (x ^ 2 + 103 * x - 81) = 0 := by
      linear_combination (Real.sqrt (2 * x + 1) * (5 * x - 18) -
          Real.sqrt x * (7 * x - 31)) * hE -
        (5 * x - 18) ^ 2 * ha2 + (31 - 7 * x) ^ 2 * hb2
    rcases mul_eq_zero.mp hfac with h1 | h2
    · linarith
    · exfalso
      have hxlt : x < 1 := by linarith [sq_nonneg x]
      have hxpos : 0 < x := by
        rcases hx.lt_or_eq with hlt | heq
        · exact hlt
        · exfalso
          rw [← heq] at h2
          norm_num at h2
      have hbpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
      have hapos : 0 < Real.sqrt (2 * x + 1) := Real.sqrt_pos.mpr (by linarith)
      linarith [mul_pos hapos (show (0:ℝ) < 18 - 5 * x by linarith),
        mul_pos hbpos (show (0:ℝ) < 31 - 7 * x by linarith)]
  · intro h
    subst h
    have h9 : Real.sqrt (2 * 4 + 1) = 3 := by
      have e : (2 * (4:ℝ) + 1) = 3 ^ 2 := by norm_num
      rw [e, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
    have h4 : Real.sqrt (4:ℝ) = 2 := by
      have e : (4:ℝ) = 2 ^ 2 := by norm_num
      rw [e, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [h9, h4]
    norm_num
```
