# Claude Opus 5 (Arena AI)

Model: `claude-opus-5` (via Arena AI)\
Date: `8 August 2026`\
Line count: `28`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have hx2 := hx.two_le
  have hy2 := hy.two_le
  have hxy1 : y - 1 ≠ 0 := by omega
  have hyx1 : x - 1 ≠ 0 := by omega
  have hdx : x ∣ x ^ (y - 1) := dvd_pow_self x hxy1
  have hdy : y ∣ y ^ (x - 1) := dvd_pow_self y hyx1
  -- x does not divide the sum
  have h1 : ¬ x ∣ (x ^ (y - 1) + y ^ (x - 1)) := by
    intro h
    have hxpow : x ∣ y ^ (x - 1) := (Nat.dvd_add_right hdx).mp h
    have hxy : x ∣ y := hx.dvd_of_dvd_pow hxpow
    exact hne ((Nat.prime_dvd_prime_iff_eq hx hy).mp hxy)
  -- y does not divide the sum
  have h2 : ¬ y ∣ (x ^ (y - 1) + y ^ (x - 1)) := by
    intro h
    have h' : y ∣ y ^ (x - 1) + x ^ (y - 1) := by rwa [add_comm] at h
    have hypow : y ∣ x ^ (y - 1) := (Nat.dvd_add_right hdy).mp h'
    have hyx : y ∣ x := hy.dvd_of_dvd_pow hypow
    exact hne ((Nat.prime_dvd_prime_iff_eq hy hx).mp hyx).symm
  have c1 : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) x :=
    ((Nat.Prime.coprime_iff_not_dvd hx).mpr h1).symm
  have c2 : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) y :=
    ((Nat.Prime.coprime_iff_not_dvd hy).mpr h2).symm
  exact Nat.Coprime.mul_right c1 c2
```
