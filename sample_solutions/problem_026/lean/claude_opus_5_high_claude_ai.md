# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `3 August 2026`\
Line count: `22`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have hx2 := hx.two_le
  have hy2 := hy.two_le
  have h1 : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) x := by
    rw [Nat.coprime_comm, hx.coprime_iff_not_dvd]
    intro h
    have hxx : x ∣ x ^ (y - 1) := dvd_pow_self x (by omega)
    have hxy : x ∣ y ^ (x - 1) := (Nat.dvd_add_right hxx).mp h
    have : x ∣ y := hx.dvd_of_dvd_pow hxy
    exact hne ((Nat.prime_dvd_prime_iff_eq hx hy).mp this)
  have h2 : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) y := by
    rw [Nat.coprime_comm, hy.coprime_iff_not_dvd]
    intro h
    have hyy : y ∣ y ^ (x - 1) := dvd_pow_self y (by omega)
    rw [add_comm] at h
    have hyx : y ∣ x ^ (y - 1) := (Nat.dvd_add_right hyy).mp h
    have : y ∣ x := hy.dvd_of_dvd_pow hyx
    exact hne ((Nat.prime_dvd_prime_iff_eq hy hx).mp this).symm
  exact Nat.Coprime.mul_right h1 h2
```
