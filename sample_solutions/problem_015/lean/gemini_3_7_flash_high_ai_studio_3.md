# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `31 August 2026`\
Line count: `22`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem div_pm_mp_eq_one_zero (x y : ℝ) :
    (x - y ≠ 0 ∧ x + y ≠ 0 ∧
      (x + y) / (x - y) = (x - y) * (2 - x - y) ∧
      (x - y) / (x + y) = (x + y) * (2 - x + y)) ↔
      (x = 1 ∧ y = 0) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rw [div_eq_iff h1] at h3; rw [div_eq_iff h2] at h4
    have : y = 0 := by
      nlinarith [show 0 < 100 * y ^ 2 + 16 by positivity,
        show y * (100 * y ^ 2 + 16) = 0 by
          linear_combination ((5 * x - 21) * (x + y + 2) + 50) * h3 -
            ((5 * x - 21) * (x - y + 2) + 50) * h4]
    subst this
    obtain rfl | h := mul_eq_zero.mp (show x * (x - 1) ^ 2 = 0 by linear_combination h3)
    · cases h2 (add_zero 0)
    · rw [sq_eq_zero_iff, sub_eq_zero] at h
      exact ⟨h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    norm_num
```
