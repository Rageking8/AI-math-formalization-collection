# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `2 September 2026`\
Line count: `19`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

def f (x : ℝ) : ℝ := |abs x - 3| + |x|

theorem unique_solution_f_iterate (x : ℝ) :
    f^[2026] x = 3 - x ^ 2 ↔ x = 0 := by
  have n : (2026 : ℕ) = 2025 + 1 := rfl
  have e : ∀ y : ℝ, 0 ≤ y → y ≤ 3 → f y = 3 := fun y h _ => by
    simp only [f, abs_of_nonneg h, abs_of_nonpos (by linarith : y - 3 ≤ 0)]; ring
  have key : ∀ y : ℝ, 3 ≤ f y := fun y => by
    rcases abs_cases (|y| - 3) with ⟨a, b⟩ | ⟨a, b⟩ <;> simp only [f, a] <;> linarith
  constructor
  · intro h
    rw [n, Function.iterate_succ_apply'] at h
    nlinarith [key (f^[2025] x), sq_nonneg x]
  · rintro rfl
    rw [n, Function.iterate_succ_apply, e 0 le_rfl (by norm_num),
      Function.iterate_fixed (e 3 (by norm_num) le_rfl)]
    norm_num
```
