# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `2 September 2026`\
Line count: `27`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have hx_coprime : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) x := by
    rw [Nat.coprime_comm, hx.coprime_iff_not_dvd]
    intro hdiv
    have hy1 : y - 1 ≠ 0 := by
      have := hy.two_le
      omega
    have hx_pow : x ∣ x ^ (y - 1) := dvd_pow_self x hy1
    have hxy_pow : x ∣ y ^ (x - 1) := (Nat.dvd_add_right hx_pow).mp hdiv
    have hxy : x ∣ y := hx.dvd_of_dvd_pow hxy_pow
    have heq : y = x := (hy.dvd_iff_eq hx.ne_one).mp hxy
    exact hne heq.symm
  have hy_coprime : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) y := by
    rw [Nat.coprime_comm, hy.coprime_iff_not_dvd]
    intro hdiv
    have hx1 : x - 1 ≠ 0 := by
      have := hx.two_le
      omega
    have hy_pow : y ∣ y ^ (x - 1) := dvd_pow_self y hx1
    have hyx_pow : y ∣ x ^ (y - 1) := (Nat.dvd_add_left hy_pow).mp hdiv
    have hyx : y ∣ x := hy.dvd_of_dvd_pow hyx_pow
    have heq : x = y := (hx.dvd_iff_eq hy.ne_one).mp hyx
    exact hne heq
  exact Nat.Coprime.mul_right hx_coprime hy_coprime
```
