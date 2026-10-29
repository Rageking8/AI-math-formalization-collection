# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `2 September 2026`\
Line count: `9`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have H {x y} (hx : x.Prime) (hy : y.Prime) (h : x ≠ y) : (x ^ (y - 1) + y ^ (x - 1)).Coprime x :=
    (hx.coprime_iff_not_dvd.2 fun d => by
      have := hx.two_le; have := hy.two_le
      rcases (Nat.dvd_prime hy).1 (hx.dvd_of_dvd_pow ((Nat.dvd_add_right (dvd_pow_self x (by omega))).1 d)) with rfl | rfl <;> omega).symm
  exact (H hx hy hne).mul_right (by rw [add_comm]; exact H hy hx hne.symm)
```
