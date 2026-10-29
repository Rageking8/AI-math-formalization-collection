# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `29 July 2026`\
Line count: `38`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem div_pm_mp_eq_one_zero (x y : ℝ) :
    (x - y ≠ 0 ∧ x + y ≠ 0 ∧
      (x + y) / (x - y) = (x - y) * (2 - x - y) ∧
      (x - y) / (x + y) = (x + y) * (2 - x + y)) ↔
      (x = 1 ∧ y = 0) := by
  have key : ∀ a b : ℝ, a ≠ 0 → b ≠ 0 → b = a ^ 2 * (2 - b) → a = b ^ 2 * (2 - a) →
      a = 1 ∧ b = 1 := by
    intro a b ha hb e1 e2
    have ha2 : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))
    have hb2 : 0 < b ^ 2 := lt_of_le_of_ne (sq_nonneg b) (Ne.symm (pow_ne_zero 2 hb))
    have hbpos : 0 < b := by nlinarith
    have hapos : 0 < a := by nlinarith
    have h5 : b ≤ a := by nlinarith [mul_nonneg hapos.le (sq_nonneg (a - 1))]
    have h6 : a ≤ b := by nlinarith [mul_nonneg hbpos.le (sq_nonneg (b - 1))]
    have hab : a = b := le_antisymm h6 h5
    rw [← hab] at e1
    have h7 : a * (a - 1) ^ 2 = 0 := by linear_combination e1
    have h8 : (a - 1) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h7 with h | h
      · exact absurd h hapos.ne'
      · exact h
    have h9 : a = 1 := by
      have hle : a ≤ 1 := by nlinarith
      have hge : 1 ≤ a := by nlinarith
      linarith
    exact ⟨h9, by rw [← hab]; exact h9⟩
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rw [div_eq_iff h1] at h3
    rw [div_eq_iff h2] at h4
    have e1 : x + y = (x - y) ^ 2 * (2 - (x + y)) := by linear_combination h3
    have e2 : x - y = (x + y) ^ 2 * (2 - (x - y)) := by linear_combination h4
    obtain ⟨k1, k2⟩ := key (x - y) (x + y) h1 h2 e1 e2
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    norm_num
```
