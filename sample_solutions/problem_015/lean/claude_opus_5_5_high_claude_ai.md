# Claude Opus 5.5 High (Claude AI)

Model: `Claude Opus 5.5 High` (via Claude AI)\
Date: `24 September 2026`\
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
  · rintro ⟨ha, hb, h1, h2⟩
    rw [div_eq_iff ha] at h1
    rw [div_eq_iff hb] at h2
    have e1 : (x + y) * (1 + (x - y) ^ 2) = 2 * (x - y) ^ 2 := by linear_combination h1
    have e2 : (x - y) * (1 + (x + y) ^ 2) = 2 * (x + y) ^ 2 := by linear_combination h2
    have sa : 0 < (x - y) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ha))
    have sb : 0 < (x + y) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hb))
    have bpos : 0 < x + y := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_nonneg (neg_nonneg.2 hc) (sq_nonneg (x - y))]
    have apos : 0 < x - y := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_nonneg (neg_nonneg.2 hc) (sq_nonneg (x + y))]
    have hle1 : x + y ≤ x - y := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_nonneg apos.le (sq_nonneg (x - y - 1)),
        mul_pos (sub_pos.2 hc) (by positivity : (0:ℝ) < 1 + (x - y) ^ 2)]
    have hle2 : x - y ≤ x + y := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_nonneg bpos.le (sq_nonneg (x + y - 1)),
        mul_pos (sub_pos.2 hc) (by positivity : (0:ℝ) < 1 + (x + y) ^ 2)]
    have hy : y = 0 := by linarith
    have hx : 0 < x := by rw [hy] at apos; linarith
    have h3 : x * (x - 1) ^ 2 = 0 := by
      rw [hy] at e1
      linear_combination e1
    rcases mul_eq_zero.1 h3 with h | h
    · linarith
    · exact ⟨by linarith [pow_eq_zero_iff (two_ne_zero) |>.1 h], hy⟩
  · rintro ⟨rfl, rfl⟩
    norm_num
```
