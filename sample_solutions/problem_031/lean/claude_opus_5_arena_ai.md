# Claude Opus 5 (Arena AI)

Model: `claude-opus-5` (via Arena AI)\
Date: `8 August 2026`\
Line count: `45`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem abs_mod_mod_sub_mod_le (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    |((x % y % z : ℤ) - (x % z : ℤ))| ≤ (z : ℤ) - Nat.gcd y z := by
  have key : ∀ a b c g : ℤ, 0 < c → 0 < g → g ∣ b → g ∣ c →
      |a % b % c - a % c| ≤ c - g := by
    intro a b c g hc hg hgb hgc
    have h1 : 0 ≤ a % b % c := Int.emod_nonneg _ hc.ne'
    have h2 : a % b % c < c := Int.emod_lt_of_pos _ hc
    have h3 : 0 ≤ a % c := Int.emod_nonneg _ hc.ne'
    have h4 : a % c < c := Int.emod_lt_of_pos _ hc
    have hmod : a % c ≡ a % b % c [ZMOD g] := by
      show a % c % g = a % b % c % g
      rw [Int.emod_emod_of_dvd _ hgc, Int.emod_emod_of_dvd _ hgc,
        Int.emod_emod_of_dvd _ hgb]
    have hd : g ∣ (a % b % c - a % c) := hmod.dvd
    have hda : g ∣ |a % b % c - a % c| := by
      rcases abs_choice (a % b % c - a % c) with h | h
      · rw [h]; exact hd
      · rw [h]; exact dvd_neg.mpr hd
    have habs : |a % b % c - a % c| < c := by
      rw [abs_lt]
      constructor <;> linarith
    obtain ⟨k, hk⟩ := hgc
    obtain ⟨m, hm⟩ := hda
    have hdvd2 : g ∣ (c - |a % b % c - a % c|) := ⟨k - m, by rw [mul_sub, ← hk, ← hm]⟩
    have hle := Int.le_of_dvd (by linarith) hdvd2
    linarith
  have hzpos : (0:ℤ) < (z:ℤ) := by exact_mod_cast hz
  have hgposN : 0 < Nat.gcd y z := by
    have hdvd : Nat.gcd y z ∣ y := Nat.gcd_dvd_left y z
    rcases Nat.eq_zero_or_pos (Nat.gcd y z) with h | h
    · rw [h] at hdvd
      have hy0 : y = 0 := zero_dvd_iff.mp hdvd
      omega
    · exact h
  have hgpos : (0:ℤ) < ((Nat.gcd y z : ℕ) : ℤ) := by exact_mod_cast hgposN
  have hgy : ((Nat.gcd y z : ℕ) : ℤ) ∣ (y : ℤ) := by exact_mod_cast Nat.gcd_dvd_left y z
  have hgz : ((Nat.gcd y z : ℕ) : ℤ) ∣ (z : ℤ) := by exact_mod_cast Nat.gcd_dvd_right y z
  have final := key (x : ℤ) (y : ℤ) (z : ℤ) ((Nat.gcd y z : ℕ) : ℤ) hzpos hgpos hgy hgz
  first
    | exact final
    | exact_mod_cast final
    | (push_cast; exact final)
    | (push_cast; exact_mod_cast final)
```
