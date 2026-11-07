# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `23 September 2026`\
Line count: `60`\
Turn count: `4`

## Solution

```lean4
import Mathlib

def f (x : ℝ) : ℝ := |abs x - 3| + |x|

theorem unique_solution_f_iterate (x : ℝ) :
    f^[2026] x = 3 - x ^ 2 ↔ x = 0 := by
  have key : ∀ n : ℕ, ∀ y : ℝ, f^[n + 1] y = 3 + 2 ^ (n + 1) * max (|y| - 3) 0 := by
    intro n
    induction n with
    | zero =>
      intro y
      show f y = 3 + 2 ^ 1 * max (|y| - 3) 0
      unfold f
      by_cases h : |y| - 3 ≤ 0
      · rw [abs_of_nonpos h, max_eq_right h]
        ring
      · push_neg at h
        rw [abs_of_pos h, max_eq_left h.le]
        ring
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply', ih]
      unfold f
      have hm0 : (0:ℝ) ≤ max (|y| - 3) 0 := le_max_right _ _
      have hp0 : (0:ℝ) ≤ (2:ℝ) ^ (n + 1) := by positivity
      have h2 : (0:ℝ) ≤ 2 ^ (n + 1) * max (|y| - 3) 0 := mul_nonneg hp0 hm0
      have hnonneg : (0:ℝ) ≤ 3 + 2 ^ (n + 1) * max (|y| - 3) 0 := by linarith
      rw [abs_of_nonneg hnonneg]
      have heq : (3 + 2 ^ (n + 1) * max (|y| - 3) 0 - 3) = 2 ^ (n + 1) * max (|y| - 3) 0 := by
        ring
      rw [heq, abs_of_nonneg h2]
      have hpow : (2:ℝ) ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 := pow_succ 2 (n + 1)
      rw [hpow]
      ring
  have h2026 : f^[2026] x = 3 + 2 ^ 2026 * max (|x| - 3) 0 := key 2025 x
  rw [h2026]
  clear h2026 key
  constructor
  · intro h
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 ^ 2026 * max (|x| - 3) 0 := ⟨_, rfl⟩
    rw [← hA] at h
    have hpow2 : (0:ℝ) ≤ (2:ℝ) ^ 2026 := by positivity
    have hmax : (0:ℝ) ≤ max (|x| - 3) 0 := le_max_right _ _
    have hprod : (0:ℝ) ≤ A := by rw [hA]; exact mul_nonneg hpow2 hmax
    clear hA hpow2 hmax
    have hx2le : x ^ 2 ≤ 0 := by linarith
    have hx2 : x ^ 2 = 0 := le_antisymm hx2le (sq_nonneg x)
    have habs2 : |x| ^ 2 = 0 := by rw [sq_abs]; exact hx2
    have habs0 : |x| = 0 := by
      by_contra hne
      have hpos : 0 < |x| := lt_of_le_of_ne (abs_nonneg x) (Ne.symm hne)
      have hcontra : 0 < |x| ^ 2 := pow_pos hpos 2
      linarith
    exact abs_eq_zero.mp habs0
  · intro h
    subst h
    have e1 : |(0:ℝ)| - 3 = -3 := by simp
    have e2 : max (-3:ℝ) 0 = 0 := max_eq_right (by norm_num)
    rw [e1, e2]
    norm_num
```
