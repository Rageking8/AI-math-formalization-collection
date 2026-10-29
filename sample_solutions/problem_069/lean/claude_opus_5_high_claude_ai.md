# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `21 August 2026`\
Line count: `40`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_int_sol_prime_factor_gcd :
    ¬ ∃ (n : ℕ) (P : ℕ), 1 < n ∧ Nat.Prime P ∧ P ∣ n ∧
      (∀ q : ℕ, Nat.Prime q → q ∣ n → q ≤ P) ∧
      (P : ℤ) ^ 2 = (n : ℤ) - (Int.gcd (n : ℤ) ((P : ℤ) - 5) : ℤ) := by
  rintro ⟨n, P, hn, hP, hPn, hmax, heq⟩
  -- the gcd equals n - P²
  have hdz : ((Int.gcd (n : ℤ) ((P : ℤ) - 5) : ℕ) : ℤ) = (n : ℤ) - (P : ℤ) ^ 2 := by
    linarith
  -- hence P divides the gcd
  have hPd : (P : ℤ) ∣ ((Int.gcd (n : ℤ) ((P : ℤ) - 5) : ℕ) : ℤ) := by
    rw [hdz]
    have hA : (P : ℤ) ∣ (n : ℤ) := by exact_mod_cast hPn
    have hB : (P : ℤ) ∣ (P : ℤ) ^ 2 := ⟨(P : ℤ), by ring⟩
    first
      | exact dvd_sub hA hB
      | exact dvd_sub' hA hB
  -- and the gcd divides P - 5
  have hdvd : ((Int.gcd (n : ℤ) ((P : ℤ) - 5) : ℕ) : ℤ) ∣ ((P : ℤ) - 5) := by
    first
      | exact Int.gcd_dvd_right
      | exact Int.gcd_dvd_right _ _
  have h1 : (P : ℤ) ∣ ((P : ℤ) - 5) := hPd.trans hdvd
  have h2 : (P : ℤ) ∣ ((P : ℤ) - ((P : ℤ) - 5)) := by
    first
      | exact dvd_sub (dvd_refl _) h1
      | exact dvd_sub' (dvd_refl _) h1
  have h3 : (P : ℤ) - ((P : ℤ) - 5) = 5 := by ring
  rw [h3] at h2
  -- so P ∣ 5, forcing P = 5
  have h5' : P ∣ 5 := by exact_mod_cast h2
  have hP5 : P = 5 := (Nat.prime_dvd_prime_iff_eq hP (by norm_num)).mp h5'
  -- then the second gcd argument is 0, so the gcd is n itself
  have hzero : ((P : ℤ) - 5) = 0 := by rw [hP5]; norm_num
  have hgcd : Int.gcd (n : ℤ) ((P : ℤ) - 5) = n := by
    rw [hzero, Int.gcd_zero_right]
    simp
  rw [hgcd, hP5] at heq
  norm_num at heq
```
