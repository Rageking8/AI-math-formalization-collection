# Gemini 3.6 Flash High (AI Studio)

Model: `Gemini 3.6 Flash High` (via AI Studio)\
Date: `9 August 2026`\
Line count: `31`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have h_not_dvd_x : ¬ x ∣ (x ^ (y - 1) + y ^ (x - 1)) := by
    intro h
    have hy1 : y - 1 ≠ 0 := by
      have := hy.two_le
      omega
    have hx_pow : x ∣ x ^ (y - 1) := dvd_pow_self x hy1
    have h_dvd_y_pow : x ∣ y ^ (x - 1) := (Nat.dvd_add_right hx_pow).mp h
    have hx_dvd_y : x ∣ y := hx.dvd_of_dvd_pow h_dvd_y_pow
    have h_eq : x = y := (hy.eq_one_or_self_of_dvd x hx_dvd_y).resolve_left hx.ne_one
    exact hne h_eq
  have h_not_dvd_y : ¬ y ∣ (x ^ (y - 1) + y ^ (x - 1)) := by
    intro h
    have hx1 : x - 1 ≠ 0 := by
      have := hx.two_le
      omega
    have hy_pow : y ∣ y ^ (x - 1) := dvd_pow_self y hx1
    have h_dvd_x_pow : y ∣ x ^ (y - 1) := by
      rw [add_comm] at h
      exact (Nat.dvd_add_right hy_pow).mp h
    have hy_dvd_x : y ∣ x := hy.dvd_of_dvd_pow h_dvd_x_pow
    have h_eq : y = x := (hx.eq_one_or_self_of_dvd y hy_dvd_x).resolve_left hy.ne_one
    exact hne h_eq.symm
  have h_cop_x : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) x :=
    (hx.coprime_iff_not_dvd.mpr h_not_dvd_x).symm
  have h_cop_y : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) y :=
    (hy.coprime_iff_not_dvd.mpr h_not_dvd_y).symm
  exact h_cop_x.mul_right h_cop_y
```
