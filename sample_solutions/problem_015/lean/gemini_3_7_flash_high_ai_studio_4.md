# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `31 August 2026`\
Line count: `29`\
Turn count: `3`

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
    have h3' := (div_eq_iff h1).mp h3
    have h4' := (div_eq_iff h2).mp h4
    have hp1 : 0 < x + y := by
      have : (x + y) * (1 + (x - y)^2) = 2 * (x - y)^2 := by linear_combination h3'
      nlinarith [sq_pos_of_ne_zero h1]
    have hp2 : 0 < x - y := by
      have : (x - y) * (1 + (x + y)^2) = 2 * (x + y)^2 := by linear_combination h4'
      nlinarith [sq_pos_of_ne_zero h2]
    have H : 4 * y^2 + (2 * y * (x - y))^2 + (2 * y * (x + y))^2 + (2 * y * (x^2 - y^2))^2 +
        (x^2 - y^2) * ((x - y - 1) * (x + y - 1))^2 = 0 := by
      linear_combination 2 * y * (1 + (x + y)^2) * h3' + (x - y) * (x - y - 1)^2 * h4'
    have hy : y = 0 := sq_eq_zero_iff.mp (by nlinarith [H, hp1, hp2] : y^2 = 0)
    have hx : x = 1 := by
      have hx1 : x ≠ 0 := by rwa [hy, sub_zero] at h1
      simp only [hy, add_zero, sub_zero, div_self hx1] at h3
      have : (x - 1)^2 = 0 := by linear_combination h3
      nlinarith [sq_eq_zero_iff.mp this]
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    norm_num
```
