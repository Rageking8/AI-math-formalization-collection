# Gemini 3.6 Flash Medium (AI Studio)

Model: `Gemini 3.6 Flash Medium` (via AI Studio)\
Date: `31 July 2026`\
Line count: `49`\
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
    have h3_ba : (x + y) = (x - y) * (2 - (x + y)) * (x - y) := by
      calc x + y = ((x + y) / (x - y)) * (x - y) := (div_mul_cancel₀ (x + y) h1).symm
      _ = ((x - y) * (2 - x - y)) * (x - y) := by rw [h3]
      _ = (x - y) * (2 - (x + y)) * (x - y) := by ring
    have h4_ab : (x - y) = (x + y) * (2 - (x - y)) * (x + y) := by
      calc x - y = ((x - y) / (x + y)) * (x + y) := (div_mul_cancel₀ (x - y) h2).symm
      _ = ((x + y) * (2 - x + y)) * (x + y) := by rw [h4]
      _ = (x + y) * (2 - (x - y)) * (x + y) := by ring
    set a := x - y
    set b := x + y
    have he1 : b * (1 + a^2) - 2 * a^2 = 0 := by linear_combination h3_ba
    have he2 : a * (1 + b^2) - 2 * b^2 = 0 := by linear_combination h4_ab
    have h_poly : a * (5 * a^4 - 8 * a^3 + 2 * a^2 + 1) = 0 := by
      linear_combination (1 + a^2)^2 * he2 - (4 * a^3 - 8 * a^2 + (a - 2) * (b * (1 + a^2) - 2 * a^2)) * he1
    have h_poly2 : 5 * a^4 - 8 * a^3 + 2 * a^2 + 1 = 0 := by
      cases mul_eq_zero.mp h_poly with
      | inl ha => exact False.elim (h1 ha)
      | inr hb => exact hb
    have h_sq : (a - 1)^2 * (5 * a^2 + 2 * a + 1) = 0 := by
      calc (a - 1)^2 * (5 * a^2 + 2 * a + 1)
        _ = 5 * a^4 - 8 * a^3 + 2 * a^2 + 1 := by ring
        _ = 0 := h_poly2
    have h_pos : 5 * a^2 + 2 * a + 1 > 0 := by
      have : 5 * a^2 + 2 * a + 1 = 5 * (a + 1/5)^2 + 4/5 := by ring
      rw [this]
      positivity
    have h_a_sub : (a - 1)^2 = 0 := by
      have h_ne : 5 * a^2 + 2 * a + 1 ≠ 0 := ne_of_gt h_pos
      exact (mul_eq_zero.mp h_sq).resolve_right h_ne
    have ha1 : a = 1 := by
      have : a - 1 = 0 := sq_eq_zero_iff.mp h_a_sub
      linarith
    have hb1 : b = 1 := by
      rw [ha1] at he1
      linarith
    constructor
    · linarith [ha1, hb1]
    · linarith [ha1, hb1]
  · rintro ⟨rfl, rfl⟩
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
```
