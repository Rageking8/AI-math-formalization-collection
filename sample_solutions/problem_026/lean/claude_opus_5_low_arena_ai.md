# Claude Opus 5 Low (Arena AI)

Model: `claude-opus-5-low` (via Arena AI)\
Date: `8 August 2026`\
Line count: `18`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have key : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ¬ p ∣ (p ^ (q - 1) + q ^ (p - 1)) := by
    intro p q hp hq hpq hdvd
    have hq2 := hq.two_le
    have h1 : p ∣ p ^ (q - 1) := dvd_pow_self p (by omega)
    have h2 : p ∣ q ^ (p - 1) := (Nat.dvd_add_right h1).mp hdvd
    have h3 : p ∣ q := hp.dvd_of_dvd_pow h2
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h3)
  have h1 : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) x :=
    (hx.coprime_iff_not_dvd.mpr (key x y hx hy hne)).symm
  have h2 : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) y := by
    have h := key y x hy hx (Ne.symm hne)
    rw [add_comm] at h
    exact (hy.coprime_iff_not_dvd.mpr h).symm
  exact Nat.Coprime.mul_right h1 h2
```
