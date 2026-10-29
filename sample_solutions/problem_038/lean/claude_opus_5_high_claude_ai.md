# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `6 August 2026`\
Line count: `26`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem min_abs_diff_le_two (a b c d e : ℝ)
    (h_sum : a + b + c + d + e = 0) (h_sq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 10) :
      (min |a - b| (min |b - c| (min |c - d| (min |d - e| |e - a|)))) ≤ 2 := by
  have key : ∀ x : ℝ, 2 < |x| → 2 < x ∨ x < -2 := by
    intro x hx
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h] at hx
      exact Or.inl hx
    · rw [h] at hx
      exact Or.inr (by linarith)
  by_contra hcon
  push_neg at hcon
  simp only [lt_min_iff] at hcon
  obtain ⟨h1, h2, h3, h4, h5⟩ := hcon
  rcases key _ h1 with h1 | h1 <;> rcases key _ h2 with h2 | h2 <;>
    rcases key _ h3 with h3 | h3 <;> rcases key _ h4 with h4 | h4 <;>
      rcases key _ h5 with h5 | h5 <;>
  linarith [sq_nonneg (a - 2), sq_nonneg (a - 1), sq_nonneg a, sq_nonneg (a + 1),
    sq_nonneg (a + 2), sq_nonneg (b - 2), sq_nonneg (b - 1), sq_nonneg b,
    sq_nonneg (b + 1), sq_nonneg (b + 2), sq_nonneg (c - 2), sq_nonneg (c - 1),
    sq_nonneg c, sq_nonneg (c + 1), sq_nonneg (c + 2), sq_nonneg (d - 2),
    sq_nonneg (d - 1), sq_nonneg d, sq_nonneg (d + 1), sq_nonneg (d + 2),
    sq_nonneg (e - 2), sq_nonneg (e - 1), sq_nonneg e, sq_nonneg (e + 1),
    sq_nonneg (e + 2)]
```
