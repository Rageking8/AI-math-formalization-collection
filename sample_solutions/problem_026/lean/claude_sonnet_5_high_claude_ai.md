# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `7 September 2026`\
Line count: `43`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have hcop : Nat.Coprime x y := (Nat.coprime_primes hx hy).mpr hne
  have hx2 : 2 ≤ x := hx.two_le
  have hy2 : 2 ≤ y := hy.two_le
  have hx1 : x - 1 ≠ 0 := by omega
  have hy1 : y - 1 ≠ 0 := by omega
  have h1 : (x ^ (y - 1) + y ^ (x - 1)) ≡ 1 [MOD x] := by
    have e1 : x ^ (y - 1) ≡ 0 [MOD x] :=
      (Nat.modEq_zero_iff_dvd).mpr (dvd_pow_self x hy1)
    have e2 : y ^ (x - 1) ≡ 1 [MOD x] := by
      have hcop' : Nat.Coprime y x := hcop.symm
      have ht := Nat.ModEq.pow_totient hcop'
      rwa [Nat.totient_prime hx] at ht
    have hsum := Nat.ModEq.add e1 e2
    simpa using hsum
  have h2 : (x ^ (y - 1) + y ^ (x - 1)) ≡ 1 [MOD y] := by
    have e1 : y ^ (x - 1) ≡ 0 [MOD y] :=
      (Nat.modEq_zero_iff_dvd).mpr (dvd_pow_self y hx1)
    have e2 : x ^ (y - 1) ≡ 1 [MOD y] := by
      have ht := Nat.ModEq.pow_totient hcop
      rwa [Nat.totient_prime hy] at ht
    have hsum := Nat.ModEq.add e2 e1
    simpa using hsum
  have hxA : ¬ x ∣ (x ^ (y - 1) + y ^ (x - 1)) := by
    have hAx : (x ^ (y - 1) + y ^ (x - 1)) % x = 1 := by
      have hmod : (x ^ (y - 1) + y ^ (x - 1)) % x = 1 % x := h1
      rwa [Nat.mod_eq_of_lt (by omega : (1:ℕ) < x)] at hmod
    rw [Nat.dvd_iff_mod_eq_zero, hAx]
    omega
  have hyA : ¬ y ∣ (x ^ (y - 1) + y ^ (x - 1)) := by
    have hAy : (x ^ (y - 1) + y ^ (x - 1)) % y = 1 := by
      have hmod : (x ^ (y - 1) + y ^ (x - 1)) % y = 1 % y := h2
      rwa [Nat.mod_eq_of_lt (by omega : (1:ℕ) < y)] at hmod
    rw [Nat.dvd_iff_mod_eq_zero, hAy]
    omega
  have g1 : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) x :=
    ((hx.coprime_iff_not_dvd).mpr hxA).symm
  have g2 : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) y :=
    ((hy.coprime_iff_not_dvd).mpr hyA).symm
  exact Nat.Coprime.mul_right g1 g2
```
