# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `12 August 2026`\
Line count: `18`\
Turn count: `1`

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
  refine ⟨fun ⟨h1, h2, h3, h4⟩ => ?_, by rintro ⟨rfl, rfl⟩; norm_num⟩
  rw [div_eq_iff h1] at h3
  rw [div_eq_iff h2] at h4
  have a : 0 < x - y := by nlinarith [mul_self_pos.mpr h2]
  have b : 0 < x + y := by nlinarith [mul_self_pos.mpr h1]
  have c : y = 0 := by
    nlinarith [mul_nonneg a.le (sq_nonneg (x - y - 1)), sq_nonneg (x - y),
      mul_nonneg b.le (sq_nonneg (x + y - 1)), sq_nonneg (x + y)]
  subst c
  have d : (x - 1) ^ 2 = 0 := by nlinarith [a, sq_nonneg (x - 1)]
  exact ⟨by nlinarith [d], rfl⟩
```
