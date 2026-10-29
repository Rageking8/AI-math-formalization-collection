# Leanstral 1.5 (Mistral Vibe)

Model: `Leanstral 1.5` (via Mistral Vibe)\
Date: `3 August 2026`\
Line count: `28`\
Turn count: `Not applicable`

## Solution

```lean4
import Mathlib

theorem positive_solutions_sqrt_eq (x : ℝ) (hx : 0 < x) :
    Real.sqrt (2 * (x - 3) ^ 2 + 4) = Real.sqrt (12 / x) ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  have hx' : 0 ≤ x := by linarith
  have hpos1 : 0 ≤ 2 * (x - 3) ^ 2 + 4 := by
    have : 0 ≤ (x - 3) ^ 2 := by positivity
    nlinarith
  have hpos2 : 0 ≤ 12 / x := by
    have hpos_div : 0 < 12 / x := div_pos (by norm_num) hx
    linarith
  constructor
  · intro h
    have hsq : 2 * (x - 3) ^ 2 + 4 = 12 / x :=
      (Real.sqrt_inj hpos1 hpos2).mp h
    have h_eq : (x - 1) * (x - 2) * (x - 3) = 0 := by
      field_simp [hx.ne.symm] at hsq
      nlinarith
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h_eq with (h12 | h3)
    · rcases eq_zero_or_eq_zero_of_mul_eq_zero h12 with (h1 | h2)
      · left; linarith
      · right; left; linarith
    · right; right; linarith
  · intro h
    rcases h with (h | h | h)
    · subst h; norm_num
    · subst h; norm_num
    · subst h; norm_num
```
