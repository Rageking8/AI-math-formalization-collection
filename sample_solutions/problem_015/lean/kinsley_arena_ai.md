# Kinsley (Arena AI)

Model: `kinsley` (via Arena AI)\
Date: `31 July 2026`\
Line count: `43`\
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
    have e1 : (x + y) * (1 + (x - y)^2) = 2 * (x - y)^2 := by
      have : x + y = (x - y)^2 * (2 - x - y) := by
        calc x + y = (x + y) / (x - y) * (x - y) := by field_simp [h1]
          _ = (x - y) * (2 - x - y) * (x - y) := by rw [h3]
          _ = (x - y)^2 * (2 - x - y) := by ring
      nlinarith
    have e2 : (x - y) * (1 + (x + y)^2) = 2 * (x + y)^2 := by
      have : x - y = (x + y)^2 * (2 - x + y) := by
        calc x - y = (x - y) / (x + y) * (x + y) := by field_simp [h2]
          _ = (x + y) * (2 - x + y) * (x + y) := by rw [h4]
          _ = (x + y)^2 * (2 - x + y) := by ring
      nlinarith
    have e3 : (1 + (x - y)^2) * (1 + (x + y)^2) = 4 * (x - y) * (x + y) := by
      have h_prod_ne : (x - y) * (x + y) ≠ 0 := mul_ne_zero h1 h2
      have : (x - y) * (x + y) * (1 + (x - y)^2) * (1 + (x + y)^2) = 4 * (x - y)^2 * (x + y)^2 := by
        calc (x - y) * (x + y) * (1 + (x - y)^2) * (1 + (x + y)^2)
            = ((x + y) * (1 + (x - y)^2)) * ((x - y) * (1 + (x + y)^2)) := by ring
          _ = (2 * (x - y)^2) * (2 * (x + y)^2) := by rw [e1, e2]
          _ = 4 * (x - y)^2 * (x + y)^2 := by ring
      apply mul_left_cancel₀ h_prod_ne
      nlinarith
    have e4 : (1 - (x - y) * (x + y))^2 + ((x - y) - (x + y))^2 = 0 := by
      nlinarith [e3]
    have e5 : (x - y) * (x + y) = 1 := by
      nlinarith [sq_nonneg (1 - (x - y) * (x + y)), sq_nonneg ((x - y) - (x + y))]
    have e6 : x - y = x + y := by
      nlinarith [sq_nonneg (1 - (x - y) * (x + y)), sq_nonneg ((x - y) - (x + y))]
    have e7 : y = 0 := by linarith [e6]
    have e8 : x = 1 := by
      rw [e7] at e5 e1
      nlinarith [sq_nonneg (x - 1)]
    exact ⟨e8, e7⟩
  · rintro ⟨rfl, rfl⟩
    norm_num
```
