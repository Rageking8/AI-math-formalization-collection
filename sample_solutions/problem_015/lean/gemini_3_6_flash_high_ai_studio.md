# Gemini 3.6 Flash High (AI Studio)

Model: `Gemini 3.6 Flash High` (via AI Studio)\
Date: `31 July 2026`\
Line count: `66`\
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
  · intro h
    rcases h with ⟨h1, h2, h3, h4⟩
    let u := x + y
    let v := x - y
    have h3' : u / v = v * (2 - u) := by
      have : (x - y) * (2 - x - y) = (x - y) * (2 - (x + y)) := by ring
      exact h3.trans this
    have h4' : v / u = u * (2 - v) := by
      have : (x + y) * (2 - x + y) = (x + y) * (2 - (x - y)) := by ring
      exact h4.trans this
    have hu : u = v^2 * (2 - u) := by
      calc u = (u / v) * v := (div_mul_cancel₀ u h1).symm
      _ = (v * (2 - u)) * v := by rw [h3']
      _ = v^2 * (2 - u) := by ring
    have hv : v = u^2 * (2 - v) := by
      calc v = (v / u) * u := (div_mul_cancel₀ v h2).symm
      _ = (u * (2 - v)) * u := by rw [h4']
      _ = u^2 * (2 - v) := by ring
    have hu2 : u * (1 + v^2) = 2 * v^2 := by linear_combination hu
    have hv2 : v * (1 + u^2) = 2 * u^2 := by linear_combination hv
    have hv_sq : 0 < v^2 := by
      rcases lt_or_gt_of_ne h1 with h | h
      · nlinarith
      · nlinarith
    have hu_sq : 0 < u^2 := by
      rcases lt_or_gt_of_ne h2 with h | h
      · nlinarith
      · nlinarith
    have h_denom_v : 0 < 1 + v^2 := by linarith [hv_sq]
    have h_denom_u : 0 < 1 + u^2 := by linarith [hu_sq]
    have hu_pos : 0 < u := by nlinarith [hu2, hv_sq, h_denom_v]
    have hv_pos : 0 < v := by nlinarith [hv2, hu_sq, h_denom_u]
    have h_prod : (u - v) * ((1 + u^2) * (1 + v^2) + 2 * (u + v)) = 0 := by
      linear_combination (1 + u^2) * hu2 - (1 + v^2) * hv2
    have h_factor : 0 < (1 + u^2) * (1 + v^2) + 2 * (u + v) := by positivity
    have h_factor_ne : (1 + u^2) * (1 + v^2) + 2 * (u + v) ≠ 0 := ne_of_gt h_factor
    have huv : u = v := by
      have h_sub : u - v = 0 := by
        cases mul_eq_zero.mp h_prod with
        | inl h => exact h
        | inr h => exact False.elim (h_factor_ne h)
      exact sub_eq_zero.mp h_sub
    rw [← huv] at hu2
    have hu3 : u * (u - 1)^2 = 0 := by linear_combination hu2
    have hu_ne : u ≠ 0 := ne_of_gt hu_pos
    have hu1_sq : (u - 1)^2 = 0 := by
      cases mul_eq_zero.mp hu3 with
      | inl h => exact False.elim (hu_ne h)
      | inr h => exact h
    have hu1 : u = 1 := by
      have h_sub1 : u - 1 = 0 := sq_eq_zero_iff.mp hu1_sq
      exact sub_eq_zero.mp h_sub1
    have hv1 : v = 1 := by rw [← huv, hu1]
    have hx : x = 1 := by linarith [hu1, hv1]
    have hy : y = 0 := by linarith [hu1, hv1]
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
```
