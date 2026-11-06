# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `15 September 2026`\
Line count: `52`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem pos_reals_pow_eq_one (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x ^ (y ^ x) = y ∧ y ^ (x ^ y) = x ↔ x = 1 ∧ y = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hlog1 : y ^ x * Real.log x = Real.log y := by
      have h := congrArg Real.log h1
      rwa [Real.log_rpow hx] at h
    have hlog2 : x ^ y * Real.log y = Real.log x := by
      have h := congrArg Real.log h2
      rwa [Real.log_rpow hy] at h
    by_cases hlx : Real.log x = 0
    · have hly : Real.log y = 0 := by
        rw [hlx, mul_zero] at hlog1
        exact hlog1.symm
      have hx1 : x = 1 := by
        have h := Real.exp_log hx
        rw [hlx, Real.exp_zero] at h
        exact h.symm
      have hy1 : y = 1 := by
        have h := Real.exp_log hy
        rw [hly, Real.exp_zero] at h
        exact h.symm
      exact ⟨hx1, hy1⟩
    · exfalso
      have hp_pos : 0 < x ^ y := Real.rpow_pos_of_pos hx y
      have hq_pos : 0 < y ^ x := Real.rpow_pos_of_pos hy x
      have key : (x ^ y * y ^ x - 1) * Real.log x = 0 := by
        linear_combination x ^ y * hlog1 + hlog2
      have hpq : x ^ y * y ^ x = 1 := by
        rcases mul_eq_zero.mp key with h | h
        · linarith
        · exact absurd h hlx
      have hmul := Real.log_mul hp_pos.ne' hq_pos.ne'
      rw [hpq, Real.log_one] at hmul
      have hlogp : Real.log (x ^ y) = y * Real.log x := Real.log_rpow hx y
      have hlogq : Real.log (y ^ x) = x * Real.log y := Real.log_rpow hy x
      have heq : y * Real.log x + x * Real.log y = 0 := by
        rw [← hlogp, ← hlogq]
        exact hmul.symm
      have heq2 : Real.log x * (y + x * (y ^ x)) = 0 := by
        linear_combination heq + x * hlog1
      have h3 : 0 < x * (y ^ x) := mul_pos hx hq_pos
      have hpos : 0 < y + x * (y ^ x) := by linarith
      rcases mul_eq_zero.mp heq2 with h | h
      · exact hlx h
      · linarith
  · rintro ⟨hx1, hy1⟩
    subst hx1
    subst hy1
    simp [Real.one_rpow]
```
