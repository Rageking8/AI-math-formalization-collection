# Claude Opus 4.7 (Arena AI)

Model: `claude-opus-4-7` (via Arena AI)\
Date: `31 July 2026`\
Line count: `40`\
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
    have e1 : x + y = (x - y) * (2 - x - y) * (x - y) := (div_eq_iff h1).mp h3
    have e2 : x - y = (x + y) * (2 - x + y) * (x + y) := (div_eq_iff h2).mp h4
    have key1 : (x + y) * (1 + (x - y)^2) = 2 * (x - y)^2 := by linear_combination e1
    have key2 : (x - y) * (1 + (x + y)^2) = 2 * (x + y)^2 := by linear_combination e2
    have factor : (x - y) * (x + y) * (((x - y) * (x + y) - 1)^2 + ((x - y) - (x + y))^2) = 0 := by
      linear_combination ((x - y) * (1 + (x + y)^2)) * key1 + (2 * (x - y)^2) * key2
    have hprod : (x - y) * (x + y) ≠ 0 := mul_ne_zero h1 h2
    have sos : ((x - y) * (x + y) - 1)^2 + ((x - y) - (x + y))^2 = 0 := by
      rcases mul_eq_zero.mp factor with h | h
      · exact absurd h hprod
      · exact h
    have p1 := sq_nonneg ((x - y) * (x + y) - 1)
    have p2 := sq_nonneg ((x - y) - (x + y))
    have sq1 : ((x - y) * (x + y) - 1)^2 = 0 := by linarith
    have sq2 : ((x - y) - (x + y))^2 = 0 := by linarith
    have hab_eq : (x - y) * (x + y) - 1 = 0 := sq_eq_zero_iff.mp sq1
    have hdiff : (x - y) - (x + y) = 0 := sq_eq_zero_iff.mp sq2
    have hy0 : y = 0 := by linarith
    subst hy0
    have hx_ne : x ≠ 0 := by
      intro h; apply h1; linarith
    have hx_sq : x * (x - 1)^2 = 0 := by linear_combination key1
    have hxm1 : (x - 1)^2 = 0 := by
      rcases mul_eq_zero.mp hx_sq with h | h
      · exact absurd h hx_ne
      · exact h
    have hx : x - 1 = 0 := sq_eq_zero_iff.mp hxm1
    exact ⟨by linarith, rfl⟩
  · rintro ⟨hx, hy⟩
    subst hx; subst hy
    refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> norm_num
```
