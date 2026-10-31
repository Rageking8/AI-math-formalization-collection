# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `3 September 2026`\
Line count: `45`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem div_pm_mp_eq_one_zero (x y : ℝ) :
    (x - y ≠ 0 ∧ x + y ≠ 0 ∧
      (x + y) / (x - y) = (x - y) * (2 - x - y) ∧
      (x - y) / (x + y) = (x + y) * (2 - x + y)) ↔
      (x = 1 ∧ y = 0) := by
  constructor
  · rintro ⟨hx, hy, h1, h2⟩
    have key1 : 2 - x - y = 2 - (x + y) := by ring
    have key2 : 2 - x + y = 2 - (x - y) := by ring
    rw [key1] at h1
    rw [key2] at h2
    set a := x - y with ha_def
    set b := x + y with hb_def
    rw [div_eq_iff hx] at h1
    rw [div_eq_iff hy] at h2
    have I2 : b + a ^ 2 * b = 2 * a ^ 2 := by linear_combination h1
    have II2 : a + b ^ 2 * a = 2 * b ^ 2 := by linear_combination h2
    have ha2 : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (pow_ne_zero 2 hx).symm
    have hb2 : 0 < b ^ 2 := lt_of_le_of_ne (sq_nonneg b) (pow_ne_zero 2 hy).symm
    have bpos : 0 < b := by nlinarith [I2, ha2]
    have apos : 0 < a := by nlinarith [II2, hb2]
    have key : (b - a) * (1 - a * b + 2 * a + 2 * b) = 0 := by
      linear_combination I2 - II2
    rcases mul_eq_zero.mp key with hc | hc
    · have hba : b = a := by linarith [hc]
      rw [hba] at I2
      have ha1 : a * (a - 1) ^ 2 = 0 := by linear_combination I2
      rcases mul_eq_zero.mp ha1 with ha0 | ha1sq
      · exact absurd ha0 hx
      · have haux : a - 1 = 0 := sq_eq_zero_iff.mp ha1sq
        have ha_eq1 : a = 1 := by linarith [haux]
        have hb_eq1 : b = 1 := hba.trans ha_eq1
        have hxy1 : x - y = 1 := by linarith [ha_def, ha_eq1]
        have hxy2 : x + y = 1 := by linarith [hb_def, hb_eq1]
        constructor <;> linarith [hxy1, hxy2]
    · exfalso
      have T : a + b + 2 * a * b = 0 := by
        linear_combination (1/2) * I2 + (1/2) * II2 + ((a + b) / 2) * hc
      nlinarith [T, apos, bpos, mul_pos apos bpos]
  · rintro ⟨hx, hy⟩
    subst hx
    subst hy
    norm_num
```
