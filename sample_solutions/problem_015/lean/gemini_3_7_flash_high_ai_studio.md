# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `31 August 2026`\
Line count: `53`\
Turn count: `1`

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
    have e1 : x + y = (2 - (x + y)) * (x - y)^2 := by
      calc x + y = (x - y) * (2 - x - y) * (x - y) := (div_eq_iff h1).mp h3
      _ = (2 - (x + y)) * (x - y)^2 := by ring
    have e2 : x - y = (2 - (x - y)) * (x + y)^2 := by
      calc x - y = (x + y) * (2 - x + y) * (x + y) := (div_eq_iff h2).mp h4
      _ = (2 - (x - y)) * (x + y)^2 := by ring
    have he1 : (x + y) * (1 + (x - y)^2) = 2 * (x - y)^2 := by
      linear_combination e1
    have he2 : (x - y) * (1 + (x + y)^2) = 2 * (x + y)^2 := by
      linear_combination e2
    have hv_sq_pos : 0 < (x - y)^2 := sq_pos_of_ne_zero h1
    have hu_sq_pos : 0 < (x + y)^2 := sq_pos_of_ne_zero h2
    have hu_pos : 0 < x + y := by
      by_contra h
      have hle : x + y ≤ 0 := not_lt.mp h
      nlinarith [he1, hv_sq_pos, hle]
    have hv_pos : 0 < x - y := by
      by_contra h
      have hle : x - y ≤ 0 := not_lt.mp h
      nlinarith [he2, hu_sq_pos, hle]
    have hsum : ((x - y) - 1)^2 * (x - y) * (1 + (x + y)^2) +
                ((x + y) - 1)^2 * (x + y) * (1 + (x - y)^2) = 0 := by
      calc ((x - y) - 1)^2 * (x - y) * (1 + (x + y)^2) +
           ((x + y) - 1)^2 * (x + y) * (1 + (x - y)^2)
        _ = (1 + (x + y)^2) * ((x + y) - (2 - (x + y)) * (x - y)^2) +
            (1 + (x - y)^2) * ((x - y) - (2 - (x - y)) * (x + y)^2) := by ring
        _ = 0 := by rw [← e1, ← e2]; ring
    have hv1 : x - y = 1 := by
      by_contra h
      have hne : x - y - 1 ≠ 0 := sub_ne_zero.mpr h
      have hsq : 0 < (x - y - 1)^2 := sq_pos_of_ne_zero hne
      have hsq2 : 0 ≤ (x + y - 1)^2 := sq_nonneg _
      nlinarith [hsum, hv_pos, hu_pos, hsq, hsq2]
    have hu1 : x + y = 1 := by
      by_contra h
      have hne : x + y - 1 ≠ 0 := sub_ne_zero.mpr h
      have hsq : 0 < (x + y - 1)^2 := sq_pos_of_ne_zero hne
      have hsq2 : 0 ≤ (x - y - 1)^2 := sq_nonneg _
      nlinarith [hsum, hv_pos, hu_pos, hsq, hsq2]
    have hx : x = 1 := by linarith [hu1, hv1]
    have hy : y = 0 := by linarith [hu1, hv1]
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
```
