# Claude Opus 5 Max (Arena AI)

Model: `claude-opus-5-max` (via Arena AI)\
Date: `27 July 2026`\
Line count: `42`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem div_pm_mp_eq_one_zero (x y : ℝ) :
    (x - y ≠ 0 ∧ x + y ≠ 0 ∧
      (x + y) / (x - y) = (x - y) * (2 - x - y) ∧
      (x - y) / (x + y) = (x + y) * (2 - x + y)) ↔
      (x = 1 ∧ y = 0) := by
  have key : ∀ a b : ℝ, a ≠ 0 → b ≠ 0 → b = a * (2 - b) * a → a = b * (2 - a) * b →
      a = 1 ∧ b = 1 := by
    intro a b ha hb h1 h2
    have ha2 : (0 : ℝ) < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (pow_ne_zero 2 ha).symm
    have hb2 : (0 : ℝ) < b ^ 2 := lt_of_le_of_ne (sq_nonneg b) (pow_ne_zero 2 hb).symm
    have hA : (0 : ℝ) < 1 + a ^ 2 := by positivity
    have hB : (0 : ℝ) < 1 + b ^ 2 := by positivity
    have e1 : b * (1 + a ^ 2) = 2 * a ^ 2 := by linear_combination h1
    have e2 : a * (1 + b ^ 2) = 2 * b ^ 2 := by linear_combination h2
    have hbpos : 0 < b := by nlinarith [e1, ha2, hA]
    have hapos : 0 < a := by nlinarith [e2, hb2, hB]
    have hblt : b < 2 := by nlinarith [e1, sq_nonneg a]
    have halt : a < 2 := by nlinarith [e2, sq_nonneg b]
    have hkey : (a - b) * (2 * (a + b) - a * b + 1) = 0 := by linear_combination h2 - h1
    have hab : a = b := by
      rcases mul_eq_zero.mp hkey with h | h
      · linarith
      · exfalso
        nlinarith [mul_pos hbpos (show (0 : ℝ) < 2 - a by linarith)]
    have h5 : a * ((a - 1) * (a - 1)) = 0 := by
      linear_combination h1 + (1 + a ^ 2) * hab
    have ha1 : a = 1 := by
      rcases mul_eq_zero.mp h5 with h | h
      · exact absurd h ha
      · rcases mul_eq_zero.mp h with h' | h' <;> linarith
    exact ⟨ha1, by linarith⟩
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rw [div_eq_iff h1] at h3
    rw [div_eq_iff h2] at h4
    obtain ⟨hx, hy⟩ :=
      key (x - y) (x + y) h1 h2 (by linear_combination h3) (by linear_combination h4)
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    norm_num
```
