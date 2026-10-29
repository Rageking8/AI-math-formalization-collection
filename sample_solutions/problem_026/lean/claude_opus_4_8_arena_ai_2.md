# Claude Opus 4.8 (Arena AI)

Model: `claude-opus-4-8` (via Arena AI)\
Date: `8 August 2026`\
Line count: `29`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have hx2 : 2 ≤ x := hx.two_le
  have hy2 : 2 ≤ y := hy.two_le
  have hym : 1 ≤ y - 1 := by omega
  have hxm : 1 ≤ x - 1 := by omega
  rw [← Nat.coprime_iff_gcd_eq_one]
  apply Nat.Coprime.mul_right
  · -- Coprime (x ^ (y-1) + y ^ (x-1)) x
    rw [Nat.coprime_comm]
    rw [hx.coprime_iff_not_dvd]
    intro hdvd
    -- x ∣ x^(y-1) + y^(x-1), and x ∣ x^(y-1), so x ∣ y^(x-1)
    have h1 : x ∣ x ^ (y - 1) := dvd_pow_self x (by omega)
    have h2 : x ∣ y ^ (x - 1) := (Nat.dvd_add_right h1).mp hdvd
    have h3 : x ∣ y := hx.dvd_of_dvd_pow h2
    have h4 : x = y := (Nat.prime_dvd_prime_iff_eq hx hy).mp h3
    exact hne h4
  · -- Coprime (x ^ (y-1) + y ^ (x-1)) y
    rw [Nat.coprime_comm]
    rw [hy.coprime_iff_not_dvd]
    intro hdvd
    have h1 : y ∣ y ^ (x - 1) := dvd_pow_self y (by omega)
    have h2 : y ∣ x ^ (y - 1) := (Nat.dvd_add_left h1).mp hdvd
    have h3 : y ∣ x := hy.dvd_of_dvd_pow h2
    have h4 : y = x := (Nat.prime_dvd_prime_iff_eq hy hx).mp h3
    exact hne h4.symm
```
