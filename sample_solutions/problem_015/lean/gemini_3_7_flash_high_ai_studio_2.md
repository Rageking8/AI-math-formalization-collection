# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `31 August 2026`\
Line count: `58`\
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
    have h3' : x + y = (x - y)^2 * (2 - x - y) := by
      calc x + y = (x + y) / (x - y) * (x - y) := (div_mul_cancel₀ (x + y) h1).symm
      _ = (x - y) * (2 - x - y) * (x - y) := by rw [h3]
      _ = (x - y)^2 * (2 - x - y) := by ring
    have h4' : x - y = (x + y)^2 * (2 - x + y) := by
      calc x - y = (x - y) / (x + y) * (x + y) := (div_mul_cancel₀ (x - y) h2).symm
      _ = (x + y) * (2 - x + y) * (x + y) := by rw [h4]
      _ = (x + y)^2 * (2 - x + y) := by ring
    have he2 : (x + y) * (1 + (x - y)^2) - 2 * (x - y)^2 = 0 := by
      calc (x + y) * (1 + (x - y)^2) - 2 * (x - y)^2
        _ = (x + y) - (x - y)^2 * (2 - x - y) := by ring
        _ = (x - y)^2 * (2 - x - y) - (x - y)^2 * (2 - x - y) := by rw [h3']
        _ = 0 := by ring
    have he1 : (x - y) * (1 + (x + y)^2) - 2 * (x + y)^2 = 0 := by
      calc (x - y) * (1 + (x + y)^2) - 2 * (x + y)^2
        _ = (x - y) - (x + y)^2 * (2 - x + y) := by ring
        _ = (x + y)^2 * (2 - x + y) - (x + y)^2 * (2 - x + y) := by rw [h4']
        _ = 0 := by ring
    have hu_pos : 0 < x - y := by
      by_contra h
      have h_v2 : 0 < 2 * (x + y)^2 := by positivity
      nlinarith [he1, h_v2]
    have hv_pos : 0 < x + y := by
      by_contra h
      have h_u2 : 0 < 2 * (x - y)^2 := by positivity
      nlinarith [he2, h_u2]
    have h_sum : (x + y) * (x + y - 1)^2 * (1 + (x - y)^2) + (x - y) * (x - y - 1)^2 * (1 + (x + y)^2) = 0 := by
      calc (x + y) * (x + y - 1)^2 * (1 + (x - y)^2) + (x - y) * (x - y - 1)^2 * (1 + (x + y)^2)
        _ = ((x - y) * (1 + (x + y)^2) - 2 * (x + y)^2) * (1 + (x - y)^2) +
            ((x + y) * (1 + (x - y)^2) - 2 * (x - y)^2) * (1 + (x + y)^2) := by ring
        _ = 0 * (1 + (x - y)^2) + 0 * (1 + (x + y)^2) := by rw [he1, he2]
        _ = 0 := by ring
    have h_t1_nonneg : 0 ≤ (x + y) * (x + y - 1)^2 * (1 + (x - y)^2) := by positivity
    have h_t2_nonneg : 0 ≤ (x - y) * (x - y - 1)^2 * (1 + (x + y)^2) := by positivity
    have h_t1_zero : (x + y) * (x + y - 1)^2 * (1 + (x - y)^2) = 0 := by linarith [h_sum, h_t1_nonneg, h_t2_nonneg]
    have h_t2_zero : (x - y) * (x - y - 1)^2 * (1 + (x + y)^2) = 0 := by linarith [h_sum, h_t1_nonneg, h_t2_nonneg]
    have hu1 : x - y = 1 := by
      by_contra h
      have hne : x - y - 1 ≠ 0 := by intro he; apply h; linarith
      have : 0 < (x - y) * (x - y - 1)^2 * (1 + (x + y)^2) := by positivity
      linarith [this, h_t2_zero]
    have hv1 : x + y = 1 := by
      by_contra h
      have hne : x + y - 1 ≠ 0 := by intro he; apply h; linarith
      have : 0 < (x + y) * (x + y - 1)^2 * (1 + (x - y)^2) := by positivity
      linarith [this, h_t1_zero]
    exact ⟨by linarith [hu1, hv1], by linarith [hu1, hv1]⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
```
