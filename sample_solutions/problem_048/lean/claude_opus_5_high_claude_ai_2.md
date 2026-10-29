# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `1 September 2026`\
Line count: `29`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem odd_of_prime_quadratic_and_quintic (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h1 : Nat.Prime (x ^ 2 + 3 * y ^ 2 - 17))
      (h2 : Nat.Prime ((x ^ 5 + y ^ 5) / (x + y))) :
      Odd x ∧ Odd y := by
  have e : ∀ n : ℕ, n ^ 2 % 2 = n % 2 := fun n => by
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [Nat.pow_mod, h] <;> rfl
  have h3 := h1.two_le
  have hev : ¬(x % 2 = 0 ∧ y % 2 = 0) := by
    rintro ⟨hx0, hy0⟩
    obtain ⟨a, rfl⟩ : ∃ a, x = a + a := ⟨x / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, y = b + b := ⟨y / 2, by omega⟩
    obtain ⟨k, hk⟩ : a + b ∣ a ^ 5 + b ^ 5 := by
      have h : ((a : ℤ) + b) ∣ ((a : ℤ) ^ 5 + (b : ℤ) ^ 5) :=
        ⟨(a : ℤ) ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4, by ring⟩
      exact_mod_cast h
    rw [show (a + a) ^ 5 + (b + b) ^ 5 = (a + a + (b + b)) * (16 * k) by
          rw [show (a + a) ^ 5 + (b + b) ^ 5 = 32 * (a ^ 5 + b ^ 5) by ring, hk]; ring,
        Nat.mul_div_cancel_left _ (by omega : 0 < a + a + (b + b))] at h2
    rcases h2.eq_one_or_self_of_dvd 2 ⟨8 * k, by ring⟩ with h | h <;> omega
  simp only [Nat.odd_iff]
  by_contra hc
  have h19 : x ^ 2 + 3 * y ^ 2 = 19 := by
    have ex := e x; have ey := e y
    rcases h1.eq_one_or_self_of_dvd 2 ⟨(x ^ 2 + 3 * y ^ 2 - 17) / 2, by omega⟩ with h | h <;> omega
  have hx4 : x ≤ 4 := by nlinarith
  have hy2 : y ≤ 2 := by nlinarith
  interval_cases x <;> interval_cases y <;> revert h19 h2 <;> norm_num
```
