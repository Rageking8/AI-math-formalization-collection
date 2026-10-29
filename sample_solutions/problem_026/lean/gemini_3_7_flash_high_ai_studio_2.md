# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `2 September 2026`\
Line count: `24`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  by_contra h
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h
  rw [Nat.dvd_gcd_iff] at hpdvd
  obtain ⟨hA, hxy⟩ := hpdvd
  rcases (Nat.Prime.dvd_mul hp).mp hxy with hpx | hpy
  · have heq : p = x := (Nat.prime_dvd_prime_iff_eq hp hx).mp hpx
    rw [heq] at hA
    have hxpow : x ∣ x ^ (y - 1) := dvd_pow_self x (by have := hy.two_le; omega)
    have hydvd : x ∣ y ^ (x - 1) := (Nat.dvd_add_right hxpow).mp hA
    have hx_dvd_y : x ∣ y := Nat.Prime.dvd_of_dvd_pow hx hydvd
    have hxy_eq : x = y := (Nat.prime_dvd_prime_iff_eq hx hy).mp hx_dvd_y
    exact hne hxy_eq
  · have heq : p = y := (Nat.prime_dvd_prime_iff_eq hp hy).mp hpy
    rw [heq] at hA
    have hypow : y ∣ y ^ (x - 1) := dvd_pow_self y (by have := hx.two_le; omega)
    rw [add_comm] at hA
    have hxdvd : y ∣ x ^ (y - 1) := (Nat.dvd_add_right hypow).mp hA
    have hy_dvd_x : y ∣ x := Nat.Prime.dvd_of_dvd_pow hy hxdvd
    have hyx_eq : y = x := (Nat.prime_dvd_prime_iff_eq hy hx).mp hy_dvd_x
    exact hne hyx_eq.symm
```
