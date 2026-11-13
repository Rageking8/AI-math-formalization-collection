# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `24`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem no_int_sol_prime_factor_gcd :
    ¬ ∃ (n : ℕ) (P : ℕ), 1 < n ∧ Nat.Prime P ∧ P ∣ n ∧
      (∀ q : ℕ, Nat.Prime q → q ∣ n → q ≤ P) ∧
      (P : ℤ) ^ 2 = (n : ℤ) - (Int.gcd (n : ℤ) ((P : ℤ) - 5) : ℤ) := by
  rintro ⟨n, P, hn, hP, hPn, hmax, h⟩
  have hg1 : ((Int.gcd (n : ℤ) ((P : ℤ) - 5) : ℕ) : ℤ) ∣ (P : ℤ) - 5 :=
    Int.gcd_dvd_right _ _
  have hPn' : (P : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hPn
  have hPg : (P : ℤ) ∣ ((Int.gcd (n : ℤ) ((P : ℤ) - 5) : ℕ) : ℤ) := by
    have e : ((Int.gcd (n : ℤ) ((P : ℤ) - 5) : ℕ) : ℤ) = (n : ℤ) - (P : ℤ) ^ 2 := by
      linarith
    rw [e]
    exact dvd_sub hPn' (dvd_pow_self (P : ℤ) (by norm_num))
  have hP5 : (P : ℤ) ∣ (P : ℤ) - 5 := dvd_trans hPg hg1
  have h5 : (P : ℤ) ∣ 5 := by
    have e : (5 : ℤ) = (P : ℤ) - ((P : ℤ) - 5) := by ring
    rw [e]
    exact dvd_sub dvd_rfl hP5
  have h5' : P ∣ 5 := by exact_mod_cast h5
  have hP_eq : P = 5 := (Nat.prime_dvd_prime_iff_eq hP (by norm_num)).mp h5'
  subst hP_eq
  simp at h
```
