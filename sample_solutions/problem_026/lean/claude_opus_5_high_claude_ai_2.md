# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `18 August 2026`\
Line count: `9`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have h : ∀ p q, p.Prime → q.Prime → p ≠ q → Nat.Coprime (p ^ (q - 1) + q ^ (p - 1)) p :=
    fun p q hp hq h => Nat.coprime_comm.1 <| hp.coprime_iff_not_dvd.2 fun d => h <|
      (Nat.prime_dvd_prime_iff_eq hp hq).1 <| hp.dvd_of_dvd_pow <|
        (Nat.dvd_add_right (dvd_pow_self p (Nat.sub_ne_zero_of_lt hq.one_lt))).1 d
  exact (h x y hx hy hne).mul_right (by rw [Nat.add_comm]; exact h y x hy hx hne.symm)
```
