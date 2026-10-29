# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `2 September 2026`\
Line count: `8`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have H {a b} (ha : a.Prime) (hb : b.Prime) (h : a ≠ b) : (a ^ (b - 1) + b ^ (a - 1)).Coprime a :=
    ((Nat.coprime_add_iff_right (dvd_pow_self a (by have := hb.one_lt; omega))).2
      (Nat.Coprime.pow_right _ ((Nat.coprime_primes ha hb).2 h))).symm
  exact (H hx hy hne).mul_right (add_comm (y ^ (x - 1)) _ ▸ H hy hx hne.symm)
```
