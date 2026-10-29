# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `8 August 2026`\
Line count: `57`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem pos_reals_pow_eq_one (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x ^ (y ^ x) = y ∧ y ^ (x ^ y) = x ↔ x = 1 ∧ y = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hP : (0:ℝ) < y ^ x := Real.rpow_pos_of_pos hy x
    have hQ : (0:ℝ) < x ^ y := Real.rpow_pos_of_pos hx y
    have e1 : (y ^ x) * Real.log x = Real.log y := by
      have h := congrArg Real.log h1
      rwa [Real.log_rpow hx] at h
    have e2 : (x ^ y) * Real.log y = Real.log x := by
      have h := congrArg Real.log h2
      rwa [Real.log_rpow hy] at h
    have ha0 : Real.log x = 0 := by
      by_contra hne
      have habpos : 0 < Real.log x * Real.log y := by
        have hrw : Real.log x * Real.log y = (y ^ x) * (Real.log x * Real.log x) := by
          rw [← e1]; ring
        rw [hrw]
        exact mul_pos hP (mul_self_pos.mpr hne)
      have key : (x ^ y) * (y ^ x) = 1 := by
        have hmul : ((x ^ y) * (y ^ x)) * Real.log x = 1 * Real.log x := by
          rw [one_mul]
          calc ((x ^ y) * (y ^ x)) * Real.log x
              = (x ^ y) * ((y ^ x) * Real.log x) := by ring
            _ = (x ^ y) * Real.log y := by rw [e1]
            _ = Real.log x := e2
        exact mul_right_cancel₀ hne hmul
      have hlog : y * Real.log x + x * Real.log y = 0 := by
        have h := congrArg Real.log key
        rw [Real.log_mul hQ.ne' hP.ne', Real.log_rpow hx, Real.log_rpow hy,
          Real.log_one] at h
        linarith
      have hfinal : 0 < (y * Real.log x + x * Real.log y) * Real.log x := by
        have h1' : 0 < y * (Real.log x * Real.log x) := mul_pos hy (mul_self_pos.mpr hne)
        have h2' : 0 < x * (Real.log x * Real.log y) := mul_pos hx habpos
        have expand : (y * Real.log x + x * Real.log y) * Real.log x
            = y * (Real.log x * Real.log x) + x * (Real.log x * Real.log y) := by ring
        rw [expand]
        exact add_pos h1' h2'
      rw [hlog, zero_mul] at hfinal
      exact lt_irrefl 0 hfinal
    have hxx : x = 1 := by
      have h := Real.exp_log hx
      rw [ha0, Real.exp_zero] at h
      exact h.symm
    have hyy : y = 1 := by
      have h := e1
      rw [ha0, mul_zero] at h
      have h' := Real.exp_log hy
      rw [← h, Real.exp_zero] at h'
      exact h'.symm
    exact ⟨hxx, hyy⟩
  · rintro ⟨hx1, hy1⟩
    subst hx1; subst hy1
    refine ⟨?_, ?_⟩ <;> simp
```
