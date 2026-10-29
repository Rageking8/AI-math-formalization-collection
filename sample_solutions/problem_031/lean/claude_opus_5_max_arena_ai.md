# Claude Opus 5 Max (Arena AI)

Model: `claude-opus-5-max` (via Arena AI)\
Date: `8 August 2026`\
Line count: `35`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem abs_mod_mod_sub_mod_le (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    |((x % y % z : ℤ) - (x % z : ℤ))| ≤ (z : ℤ) - Nat.gcd y z := by
  have hZ : (0 : ℤ) < (z : ℤ) := by exact_mod_cast hz
  have hgy : ((Nat.gcd y z : ℕ) : ℤ) ∣ (y : ℤ) := by exact_mod_cast Nat.gcd_dvd_left y z
  have hgz : ((Nat.gcd y z : ℕ) : ℤ) ∣ (z : ℤ) := by exact_mod_cast Nat.gcd_dvd_right y z
  have hmod : ((x : ℤ) % (y : ℤ) % (z : ℤ)) % ((Nat.gcd y z : ℕ) : ℤ)
      = ((x : ℤ) % (z : ℤ)) % ((Nat.gcd y z : ℕ) : ℤ) := by
    rw [Int.emod_emod_of_dvd _ hgz, Int.emod_emod_of_dvd _ hgy, Int.emod_emod_of_dvd _ hgz]
  have hdvd : ((Nat.gcd y z : ℕ) : ℤ) ∣ ((x : ℤ) % (y : ℤ) % (z : ℤ) - (x : ℤ) % (z : ℤ)) := by
    apply Int.dvd_of_emod_eq_zero
    rw [Int.sub_emod, hmod, sub_self, Int.zero_emod]
  have h1 : (0 : ℤ) ≤ (x : ℤ) % (y : ℤ) % (z : ℤ) := Int.emod_nonneg _ hZ.ne'
  have h2 : (x : ℤ) % (y : ℤ) % (z : ℤ) < (z : ℤ) := Int.emod_lt_of_pos _ hZ
  have h3 : (0 : ℤ) ≤ (x : ℤ) % (z : ℤ) := Int.emod_nonneg _ hZ.ne'
  have h4 : (x : ℤ) % (z : ℤ) < (z : ℤ) := Int.emod_lt_of_pos _ hZ
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨m, hm⟩ := hgz
  rw [abs_le]
  constructor
  · have hd2 : ((Nat.gcd y z : ℕ) : ℤ) ∣
        ((z : ℤ) + ((x : ℤ) % (y : ℤ) % (z : ℤ) - (x : ℤ) % (z : ℤ))) :=
      ⟨m + k, by linear_combination hm + hk⟩
    have hpos : (0 : ℤ) < (z : ℤ) + ((x : ℤ) % (y : ℤ) % (z : ℤ) - (x : ℤ) % (z : ℤ)) := by
      linarith
    have hle := Int.le_of_dvd hpos hd2
    linarith
  · have hd2 : ((Nat.gcd y z : ℕ) : ℤ) ∣
        ((z : ℤ) - ((x : ℤ) % (y : ℤ) % (z : ℤ) - (x : ℤ) % (z : ℤ))) :=
      ⟨m - k, by linear_combination hm - hk⟩
    have hpos : (0 : ℤ) < (z : ℤ) - ((x : ℤ) % (y : ℤ) % (z : ℤ) - (x : ℤ) % (z : ℤ)) := by
      linarith
    have hle := Int.le_of_dvd hpos hd2
    linarith
```
