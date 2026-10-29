# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `31 August 2026`\
Line count: `55`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem no_pos_integers_factorial_eq :
    ¬ ∃ (x y : ℕ), 0 < x ∧ 0 < y ∧
      x.factorial + y.factorial = (x + y + 1) ^ 3 * Nat.gcd x.factorial y.factorial := by
  have A : ∀ z : ℕ, 0 < z → 1 + (z+1) * ((z+2) * (z+3)) < (2*z+1)^3 := by
    intro z hz
    obtain ⟨b, rfl⟩ : ∃ b, z = b + 1 := ⟨z - 1, by omega⟩
    nlinarith [Nat.zero_le (b^2), Nat.zero_le (b^3)]
  have B : ∀ s : ℕ, 6 ≤ s → (2*s+5)^3 < (s+1) * ((s+2) * ((s+3) * (s+4))) := by
    intro s hs
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 6 := ⟨s - 6, by omega⟩
    nlinarith [Nat.zero_le (t^2), Nat.zero_le (t^3), Nat.zero_le (t^4)]
  have K : ∀ x y : ℕ, 0 < x → x ≤ y →
      x.factorial + y.factorial ≠ (x + y + 1)^3 * x.factorial := by
    intro x y hx hxy h
    have hf : 0 < x.factorial := x.factorial_pos
    obtain ⟨P, hP⟩ := Nat.factorial_dvd_factorial hxy
    have hE : 1 + P = (x + y + 1)^3 := by
      refine Nat.eq_of_mul_eq_mul_right hf ?_
      rw [add_mul, one_mul, mul_comm P x.factorial, ← hP]; exact h
    have h4 : x + 4 ≤ y := by
      by_contra hc
      have e : (x+1+1+1).factorial = (x+1+1+1) * ((x+1+1) * ((x+1) * x.factorial)) := by
        rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
      have hu : P ≤ (x+1) * ((x+1+1) * (x+1+1+1)) := by
        refine Nat.le_of_mul_le_mul_left ?_ hf
        calc x.factorial * P = y.factorial := hP.symm
          _ ≤ (x+1+1+1).factorial := Nat.factorial_le (by omega)
          _ = x.factorial * ((x+1) * ((x+1+1) * (x+1+1+1))) := by rw [e]; ring
      linarith [A x hx, hu, hE, Nat.pow_le_pow_left (show 2*x+1 ≤ x+y+1 by omega) 3]
    obtain ⟨j, rfl⟩ : ∃ j, y = x + j + 1 + 1 + 1 + 1 := ⟨y - x - 4, by omega⟩
    have e : (x+j+1+1+1+1).factorial = (x+j+1+1+1+1) * ((x+j+1+1+1) *
        ((x+j+1+1) * ((x+j+1) * (x+j).factorial))) := by
      rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    have hl : (x+j+1) * ((x+j+2) * ((x+j+3) * (x+j+4))) ≤ P := by
      refine Nat.le_of_mul_le_mul_left ?_ hf
      calc x.factorial * ((x+j+1) * ((x+j+2) * ((x+j+3) * (x+j+4))))
          ≤ (x+j).factorial * ((x+j+1) * ((x+j+2) * ((x+j+3) * (x+j+4)))) :=
            Nat.mul_le_mul (Nat.factorial_le (by omega)) (le_refl _)
        _ = (x+j+1+1+1+1).factorial := by rw [e]; ring
        _ = x.factorial * P := hP
    have h5 : x + j ≤ 5 := by
      by_contra hc
      linarith [B (x+j) (by omega), hl, hE,
        Nat.pow_le_pow_left (show x + (x+j+1+1+1+1) + 1 ≤ 2*(x+j)+5 by omega) 3]
    have hx5 : x ≤ 5 := by omega
    have hj4 : j ≤ 4 := by omega
    interval_cases x <;> interval_cases j <;> revert h <;> decide
  rintro ⟨x, y, hx, hy, h⟩
  rcases le_total x y with hxy | hxy
  · exact K x y hx hxy (by rwa [Nat.gcd_eq_left (Nat.factorial_dvd_factorial hxy)] at h)
  · refine K y x hy hxy ?_
    rw [Nat.gcd_comm, Nat.gcd_eq_left (Nat.factorial_dvd_factorial hxy)] at h
    rw [Nat.add_comm y x, Nat.add_comm y.factorial x.factorial]; exact h
```
