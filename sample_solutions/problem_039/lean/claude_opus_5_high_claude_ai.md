# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `6 August 2026`\
Line count: `36`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem infinite_tan_zero_iff_rat (x : ℝ) :
    Set.Infinite { n : ℕ | n > 0 ∧ Real.tan ((n : ℝ) * Real.pi * x) = 0 } ↔ ∃ q : ℚ, x = q := by
  constructor
  · intro h
    obtain ⟨n, hn0, htan⟩ := h.nonempty
    rw [Real.tan_eq_zero_iff] at htan
    obtain ⟨k, hk⟩ := htan
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 : (2 * (n : ℝ) * x - (k : ℝ)) * Real.pi = 0 := by linarith
    have h3 : 2 * (n : ℝ) * x - (k : ℝ) = 0 := by
      rcases mul_eq_zero.mp h2 with h4 | h4
      · exact h4
      · exact absurd h4 Real.pi_ne_zero
    refine ⟨(k : ℚ) / (2 * (n : ℚ)), ?_⟩
    push_cast
    field_simp
    linarith
  · rintro ⟨q, rfl⟩
    have hd0 : ((q.den : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr q.den_pos.ne'
    have key : ((q.den : ℝ)) * (q : ℝ) = ((q.num : ℤ) : ℝ) := by
      rw [Rat.cast_def]
      field_simp
    refine Set.infinite_of_injective_forall_mem
      (f := fun m : ℕ => (m + 1) * q.den) ?_ ?_
    · intro a b hab
      have hab' : (a + 1) * q.den = (b + 1) * q.den := hab
      have := Nat.eq_of_mul_eq_mul_right q.den_pos hab'
      omega
    · intro m
      refine ⟨mul_pos (by omega) q.den_pos, ?_⟩
      rw [Real.tan_eq_zero_iff]
      refine ⟨2 * ((m + 1) * q.num), ?_⟩
      push_cast
      linear_combination (-((m : ℝ) + 1) * Real.pi) * key
```
