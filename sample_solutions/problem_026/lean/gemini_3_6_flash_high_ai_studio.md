# Gemini 3.6 Flash High (AI Studio)

Model: `Gemini 3.6 Flash High` (via AI Studio)\
Date: `9 August 2026`\
Line count: `26`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have hx2 : 2 ≤ x := hx.two_le
  have hy2 : 2 ≤ y := hy.two_le
  have hx_not_dvd : ¬ x ∣ (x ^ (y - 1) + y ^ (x - 1)) := by
    intro h_sum
    have h_dvd_x : x ∣ x ^ (y - 1) := dvd_pow_self x (by omega)
    have h_dvd_pow : x ∣ y ^ (x - 1) := (Nat.dvd_add_right h_dvd_x).mp h_sum
    have h_dvd_y : x ∣ y := hx.dvd_of_dvd_pow h_dvd_pow
    have h_eq : y = x := (hy.dvd_iff_eq (by omega : x ≠ 1)).mp h_dvd_y
    exact hne h_eq.symm
  have hy_not_dvd : ¬ y ∣ (x ^ (y - 1) + y ^ (x - 1)) := by
    intro h_sum
    have h_dvd_y : y ∣ y ^ (x - 1) := dvd_pow_self y (by omega)
    rw [add_comm (x ^ (y - 1))] at h_sum
    have h_dvd_pow : y ∣ x ^ (y - 1) := (Nat.dvd_add_right h_dvd_y).mp h_sum
    have h_dvd_x : y ∣ x := hy.dvd_of_dvd_pow h_dvd_pow
    have h_eq : x = y := (hx.dvd_iff_eq (by omega : y ≠ 1)).mp h_dvd_x
    exact hne h_eq
  have h1 : Nat.Coprime x (x ^ (y - 1) + y ^ (x - 1)) :=
    (Nat.Prime.coprime_iff_not_dvd hx).mpr hx_not_dvd
  have h2 : Nat.Coprime y (x ^ (y - 1) + y ^ (x - 1)) :=
    (Nat.Prime.coprime_iff_not_dvd hy).mpr hy_not_dvd
  exact Nat.Coprime.symm (Nat.Coprime.mul_left h1 h2)
```
