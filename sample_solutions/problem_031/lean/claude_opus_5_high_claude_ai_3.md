# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `30 August 2026`\
Line count: `16`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem abs_mod_mod_sub_mod_le (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    |((x % y % z : ℤ) - (x % z : ℤ))| ≤ (z : ℤ) - Nat.gcd y z := by
  have h : (0:ℤ) < z := by exact_mod_cast hz
  have ha : (Nat.gcd y z : ℤ) ∣ (y:ℤ) := by exact_mod_cast Nat.gcd_dvd_left y z
  have hb : (Nat.gcd y z : ℤ) ∣ (z:ℤ) := by exact_mod_cast Nat.gcd_dvd_right y z
  have h1 := Int.emod_nonneg ((x:ℤ) % y) h.ne'
  have h2 := Int.emod_lt_of_pos ((x:ℤ) % y) h
  have h3 := Int.emod_nonneg (x:ℤ) h.ne'
  have h4 := Int.emod_lt_of_pos (x:ℤ) h
  have hlt : |(x:ℤ) % y % z - (x:ℤ) % z| < z := abs_lt.2 ⟨by linarith, by linarith⟩
  have hg : (Nat.gcd y z : ℤ) ∣ |(x:ℤ) % y % z - (x:ℤ) % z| := by
    simpa using Int.ModEq.dvd ((Int.emod_emod_of_dvd (x:ℤ) hb).trans
      (((Int.emod_emod_of_dvd ((x:ℤ) % y) hb).trans (Int.emod_emod_of_dvd (x:ℤ) ha)).symm))
  linarith [Int.le_of_dvd (by linarith) (dvd_sub hb hg)]
```
