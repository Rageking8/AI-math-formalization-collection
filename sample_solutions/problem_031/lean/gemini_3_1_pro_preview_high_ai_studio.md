# Gemini 3.1 Pro Preview High (AI Studio)

Model: `Gemini 3.1 Pro Preview High` (via AI Studio)\
Date: `8 August 2026`\
Line count: `51`\
Turn count: `5`

## Solution

```lean4
import Mathlib

theorem abs_mod_mod_sub_mod_le (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    |((x % y % z : ℤ) - (x % z : ℤ))| ≤ (z : ℤ) - Nat.gcd y z := by
  -- 1. Setup fundamental modulo division equations
  have h1 : (x % y % z : ℤ) + (z : ℤ) * ((x % y / z : ℕ) : ℤ) = (x % y : ℤ) := by exact_mod_cast Nat.mod_add_div (x % y) z
  have h2 : (x % y : ℤ) + (y : ℤ) * ((x / y : ℕ) : ℤ) = (x : ℤ) := by exact_mod_cast Nat.mod_add_div x y
  have h3 : (x % z : ℤ) + (z : ℤ) * ((x / z : ℕ) : ℤ) = (x : ℤ) := by exact_mod_cast Nat.mod_add_div x z

  -- Express the modulo operations algebraically in terms of Int
  have hD : (x % y % z : ℤ) - (x % z : ℤ) = (z : ℤ) * (((x / z : ℕ) : ℤ) - ((x % y / z : ℕ) : ℤ)) - (y : ℤ) * ((x / y : ℕ) : ℤ) := by
    calc
      (x % y % z : ℤ) - (x % z : ℤ) = ((x % y % z : ℤ) + (z : ℤ) * ((x % y / z : ℕ) : ℤ)) - (z : ℤ) * ((x % y / z : ℕ) : ℤ) - ((x % z : ℤ) + (z : ℤ) * ((x / z : ℕ) : ℤ)) + (z : ℤ) * ((x / z : ℕ) : ℤ) := by ring
      _ = (x % y : ℤ) - (z : ℤ) * ((x % y / z : ℕ) : ℤ) - (x : ℤ) + (z : ℤ) * ((x / z : ℕ) : ℤ) := by rw [h1, h3]
      _ = ((x % y : ℤ) + (y : ℤ) * ((x / y : ℕ) : ℤ)) - (y : ℤ) * ((x / y : ℕ) : ℤ) - (z : ℤ) * ((x % y / z : ℕ) : ℤ) - (x : ℤ) + (z : ℤ) * ((x / z : ℕ) : ℤ) := by ring
      _ = (x : ℤ) - (y : ℤ) * ((x / y : ℕ) : ℤ) - (z : ℤ) * ((x % y / z : ℕ) : ℤ) - (x : ℤ) + (z : ℤ) * ((x / z : ℕ) : ℤ) := by rw [h2]
      _ = (z : ℤ) * (((x / z : ℕ) : ℤ) - ((x % y / z : ℕ) : ℤ)) - (y : ℤ) * ((x / y : ℕ) : ℤ) := by ring

  -- 2. Establish that Nat.gcd divides both modular expressions exactly
  have hdy : (Nat.gcd y z : ℤ) ∣ (y : ℤ) := by exact_mod_cast Nat.gcd_dvd_left y z
  have hdz : (Nat.gcd y z : ℤ) ∣ (z : ℤ) := by exact_mod_cast Nat.gcd_dvd_right y z

  have hdvd : (Nat.gcd y z : ℤ) ∣ ((x % y % z : ℤ) - (x % z : ℤ)) := by
    rw [hD]
    apply dvd_sub
    · have ⟨kz, hkz⟩ := hdz
      exact ⟨kz * (((x / z : ℕ) : ℤ) - ((x % y / z : ℕ) : ℤ)), by rw [hkz]; ring⟩
    · have ⟨ky, hky⟩ := hdy
      exact ⟨ky * ((x / y : ℕ) : ℤ), by rw [hky]; ring⟩

  -- 3. Obtain fundamental strict inequalities and non-negativity for remainders
  have hb1 : (x % y % z : ℤ) < (z : ℤ) := by exact_mod_cast Nat.mod_lt (x % y) hz
  have hb2 : 0 ≤ (x % y % z : ℤ) := Nat.cast_nonneg (x % y % z)
  have hb3 : (x % z : ℤ) < (z : ℤ) := by exact_mod_cast Nat.mod_lt x hz
  have hb4 : 0 ≤ (x % z : ℤ) := Nat.cast_nonneg (x % z)

  -- 4. Formulate constraints for solving the integer inequalities bounds 
  have hdvd1 : (Nat.gcd y z : ℤ) ∣ (z : ℤ) - ((x % y % z : ℤ) - (x % z : ℤ)) := dvd_sub hdz hdvd
  have hpos1 : 0 < (z : ℤ) - ((x % y % z : ℤ) - (x % z : ℤ)) := by omega
  have hle1 : (Nat.gcd y z : ℤ) ≤ (z : ℤ) - ((x % y % z : ℤ) - (x % z : ℤ)) := Int.le_of_dvd hpos1 hdvd1

  have hdvd2 : (Nat.gcd y z : ℤ) ∣ (z : ℤ) + ((x % y % z : ℤ) - (x % z : ℤ)) := dvd_add hdz hdvd
  have hpos2 : 0 < (z : ℤ) + ((x % y % z : ℤ) - (x % z : ℤ)) := by omega
  have hle2 : (Nat.gcd y z : ℤ) ≤ (z : ℤ) + ((x % y % z : ℤ) - (x % z : ℤ)) := Int.le_of_dvd hpos2 hdvd2

  -- 5. Complete bounds for standard absolute value
  -- |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
  rw [abs_le]
  constructor
  · omega
  · omega
```
