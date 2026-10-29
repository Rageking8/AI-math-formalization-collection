# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `4 August 2026`\
Line count: `32`\
Turn count: `3`

## Solution

```lean4
import Mathlib

theorem abs_mod_mod_sub_mod_le (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    |((x % y % z : ℤ) - (x % z : ℤ))| ≤ (z : ℤ) - Nat.gcd y z := by
  have hz' : (0:ℤ) < (z:ℤ) := by exact_mod_cast hz
  have hzne : (z:ℤ) ≠ 0 := ne_of_gt hz'
  have hgy : ((Nat.gcd y z : ℕ) : ℤ) ∣ (y:ℤ) := by exact_mod_cast Nat.gcd_dvd_left y z
  have hgz : ((Nat.gcd y z : ℕ) : ℤ) ∣ (z:ℤ) := by exact_mod_cast Nat.gcd_dvd_right y z
  -- both remainders lie in [0, z)
  have ha0 : (0:ℤ) ≤ (x:ℤ) % (y:ℤ) % (z:ℤ) := Int.emod_nonneg _ hzne
  have haz : (x:ℤ) % (y:ℤ) % (z:ℤ) < (z:ℤ) := Int.emod_lt_of_pos _ hz'
  have hb0 : (0:ℤ) ≤ (x:ℤ) % (z:ℤ) := Int.emod_nonneg _ hzne
  have hbz : (x:ℤ) % (z:ℤ) < (z:ℤ) := Int.emod_lt_of_pos _ hz'
  -- both remainders reduce to x modulo the gcd
  have key : ((x:ℤ) % (y:ℤ) % (z:ℤ)) % ((Nat.gcd y z : ℕ) : ℤ)
      = ((x:ℤ) % (z:ℤ)) % ((Nat.gcd y z : ℕ) : ℤ) := by
    rw [Int.emod_emod_of_dvd _ hgz, Int.emod_emod_of_dvd _ hgy, Int.emod_emod_of_dvd _ hgz]
  have hmod : Int.ModEq ((Nat.gcd y z : ℕ) : ℤ)
      ((x:ℤ) % (y:ℤ) % (z:ℤ)) ((x:ℤ) % (z:ℤ)) := key
  have hdvd : ((Nat.gcd y z : ℕ) : ℤ) ∣ ((x:ℤ) % (y:ℤ) % (z:ℤ) - (x:ℤ) % (z:ℤ)) :=
    Int.ModEq.dvd hmod.symm
  have habs : ((Nat.gcd y z : ℕ) : ℤ) ∣ |(x:ℤ) % (y:ℤ) % (z:ℤ) - (x:ℤ) % (z:ℤ)| := by
    rcases abs_choice ((x:ℤ) % (y:ℤ) % (z:ℤ) - (x:ℤ) % (z:ℤ)) with h | h <;> rw [h]
    · exact hdvd
    · exact dvd_neg.mpr hdvd
  have hlt : |(x:ℤ) % (y:ℤ) % (z:ℤ) - (x:ℤ) % (z:ℤ)| < (z:ℤ) :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  -- gcd divides z - |a - b|, which is positive, so gcd ≤ z - |a - b|
  have hsub : ((Nat.gcd y z : ℕ) : ℤ) ∣
      ((z:ℤ) - |(x:ℤ) % (y:ℤ) % (z:ℤ) - (x:ℤ) % (z:ℤ)|) := dvd_sub hgz habs
  have hle := Int.le_of_dvd (by linarith) hsub
  linarith
```
