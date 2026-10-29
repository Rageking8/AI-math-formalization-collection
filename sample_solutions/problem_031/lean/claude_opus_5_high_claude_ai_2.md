# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `20 August 2026`\
Line count: `16`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem abs_mod_mod_sub_mod_le (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    |((x % y % z : ℤ) - (x % z : ℤ))| ≤ (z : ℤ) - Nat.gcd y z := by
  have p : (0:ℤ) < z := by exact_mod_cast hz
  have g : ((y.gcd z : ℕ) : ℤ) ∣ (z : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right y z)
  have m : (x:ℤ) % z ≡ (x:ℤ) % y % z [ZMOD ((y.gcd z : ℕ) : ℤ)] :=
    (Int.emod_emod_of_dvd _ g).trans ((Int.emod_emod_of_dvd _ g).trans
      (Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left y z)))).symm
  have a1 := Int.emod_nonneg ((x:ℤ) % y) p.ne'
  have a2 := Int.emod_lt_of_pos ((x:ℤ) % y) p
  have a3 := Int.emod_nonneg (x:ℤ) p.ne'
  have a4 := Int.emod_lt_of_pos (x:ℤ) p
  have := Int.le_of_dvd (by rw [sub_pos]; exact abs_lt.2 ⟨by linarith, by linarith⟩)
    (dvd_sub g ((dvd_abs _ _).2 m.dvd))
  linarith
```
