# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `31 August 2026`\
Line count: `23`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem infinite_tan_zero_iff_rat (x : ℝ) :
    Set.Infinite { n : ℕ | n > 0 ∧ Real.tan ((n : ℝ) * Real.pi * x) = 0 } ↔ ∃ q : ℚ, x = q := by
  constructor
  · intro h
    obtain ⟨n, hn, ht⟩ := h.nonempty
    obtain ⟨k, hk⟩ := Real.tan_eq_zero_iff.1 ht
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    exact ⟨(k : ℚ) / (2 * n), by
      push_cast
      rw [eq_div_iff (mul_ne_zero two_ne_zero hn0)]
      exact mul_right_cancel₀ Real.pi_ne_zero (by linear_combination -2 * hk)⟩
  · rintro ⟨q, rfl⟩
    have hd := q.den_pos
    have hd0 : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    have hq : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by rw [Rat.cast_def]; field_simp
    exact Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (m + 1) * (2 * q.den))
      (fun a b hab => by
        have := Nat.eq_of_mul_eq_mul_right (show 0 < 2 * q.den by omega) hab; omega)
      (fun m => ⟨mul_pos (by omega) (by omega), Real.tan_eq_zero_iff.2
        ⟨4 * (m + 1) * q.num, by
          push_cast; linear_combination (-2 * ((m : ℝ) + 1) * Real.pi) * hq⟩⟩)
```
