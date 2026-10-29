# Claude Opus 4.8 (Arena AI)

Model: `claude-opus-4-8` (via Arena AI)\
Date: `8 August 2026`\
Line count: `24`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have hx2 : 2 ≤ x := hx.two_le
  have hy2 : 2 ≤ y := hy.two_le
  -- x ∣ x^(y-1)
  have hxdvd : x ∣ x ^ (y - 1) := dvd_pow_self x (by omega)
  have hydvd : y ∣ y ^ (x - 1) := dvd_pow_self y (by omega)
  have cop_x : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) x := by
    rw [Nat.coprime_comm, hx.coprime_iff_not_dvd]
    intro h
    have : x ∣ y ^ (x - 1) := (Nat.dvd_add_right hxdvd).mp h
    have : x ∣ y := hx.dvd_of_dvd_pow this
    have := (Nat.prime_dvd_prime_iff_eq hx hy).mp this
    exact hne this
  have cop_y : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) y := by
    rw [Nat.coprime_comm, hy.coprime_iff_not_dvd]
    intro h
    have : y ∣ x ^ (y - 1) := (Nat.dvd_add_left hydvd).mp h
    have : y ∣ x := hy.dvd_of_dvd_pow this
    have := (Nat.prime_dvd_prime_iff_eq hy hx).mp this
    exact hne this.symm
  exact Nat.Coprime.mul_right cop_x cop_y
```
