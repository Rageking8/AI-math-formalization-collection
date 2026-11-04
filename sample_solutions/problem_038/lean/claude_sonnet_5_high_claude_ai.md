# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `14 September 2026`\
Line count: `64`\
Turn count: `3 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem min_abs_diff_le_two (a b c d e : ℝ)
    (h_sum : a + b + c + d + e = 0) (h_sq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 10) :
      (min |a - b| (min |b - c| (min |c - d| (min |d - e| |e - a|)))) ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  simp only [lt_min_iff] at hcon
  obtain ⟨g1, g2, g3, g4, g5⟩ := hcon
  have h1 : a - b > 2 ∨ a - b < -2 := by
    by_cases hab : 0 ≤ a - b
    · left; rw [abs_of_nonneg hab] at g1; linarith
    · right; push_neg at hab; rw [abs_of_neg hab] at g1; linarith
  have h2 : b - c > 2 ∨ b - c < -2 := by
    by_cases hab : 0 ≤ b - c
    · left; rw [abs_of_nonneg hab] at g2; linarith
    · right; push_neg at hab; rw [abs_of_neg hab] at g2; linarith
  have h3 : c - d > 2 ∨ c - d < -2 := by
    by_cases hab : 0 ≤ c - d
    · left; rw [abs_of_nonneg hab] at g3; linarith
    · right; push_neg at hab; rw [abs_of_neg hab] at g3; linarith
  have h4 : d - e > 2 ∨ d - e < -2 := by
    by_cases hab : 0 ≤ d - e
    · left; rw [abs_of_nonneg hab] at g4; linarith
    · right; push_neg at hab; rw [abs_of_neg hab] at g4; linarith
  have h5 : e - a > 2 ∨ e - a < -2 := by
    by_cases hab : 0 ≤ e - a
    · left; rw [abs_of_nonneg hab] at g5; linarith
    · right; push_neg at hab; rw [abs_of_neg hab] at g5; linarith
  clear g1 g2 g3 g4 g5
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5
  · nlinarith [sq_nonneg (a-3), sq_nonneg (b-1), sq_nonneg (c+1), sq_nonneg (d+3), sq_nonneg e]
  · nlinarith [sq_nonneg (a-3), sq_nonneg (b-1), sq_nonneg (c+1), sq_nonneg (d+3), sq_nonneg e]
  · nlinarith [sq_nonneg (a-3), sq_nonneg (b-1), sq_nonneg (c+1), sq_nonneg (d+3), sq_nonneg e]
  · nlinarith [sq_nonneg (a-3), sq_nonneg (b-1), sq_nonneg (c+1), sq_nonneg (d+3), sq_nonneg e]
  · nlinarith [sq_nonneg b, sq_nonneg (c+2), sq_nonneg (d-1), sq_nonneg (e+1), sq_nonneg (a-2)]
  · nlinarith [sq_nonneg b, sq_nonneg (c+2), sq_nonneg (d-1), sq_nonneg (e+1), sq_nonneg (a-2)]
  · nlinarith [sq_nonneg (e-3), sq_nonneg (a-1), sq_nonneg (b+1), sq_nonneg (c+3), sq_nonneg d]
  · nlinarith [sq_nonneg (c+3), sq_nonneg (d+1), sq_nonneg (e-1), sq_nonneg (a-3), sq_nonneg b]
  · nlinarith [sq_nonneg d, sq_nonneg (e+2), sq_nonneg (a-1), sq_nonneg (b+1), sq_nonneg (c-2)]
  · nlinarith [sq_nonneg d, sq_nonneg (e+2), sq_nonneg (a-1), sq_nonneg (b+1), sq_nonneg (c-2)]
  · nlinarith [sq_nonneg a, sq_nonneg (b+2), sq_nonneg (c-1), sq_nonneg (d+1), sq_nonneg (e-2)]
  · nlinarith [sq_nonneg e, sq_nonneg (a-2), sq_nonneg (b+1), sq_nonneg (c-1), sq_nonneg (d+2)]
  · nlinarith [sq_nonneg (d-3), sq_nonneg (e-1), sq_nonneg (a+1), sq_nonneg (b+3), sq_nonneg c]
  · nlinarith [sq_nonneg c, sq_nonneg (d-2), sq_nonneg (e+1), sq_nonneg (a-1), sq_nonneg (b+2)]
  · nlinarith [sq_nonneg (b+3), sq_nonneg (c+1), sq_nonneg (d-1), sq_nonneg (e-3), sq_nonneg a]
  · nlinarith [sq_nonneg (b+3), sq_nonneg (c+1), sq_nonneg (d-1), sq_nonneg (e-3), sq_nonneg a]
  · nlinarith [sq_nonneg (b-3), sq_nonneg (c-1), sq_nonneg (d+1), sq_nonneg (e+3), sq_nonneg a]
  · nlinarith [sq_nonneg (b-3), sq_nonneg (c-1), sq_nonneg (d+1), sq_nonneg (e+3), sq_nonneg a]
  · nlinarith [sq_nonneg c, sq_nonneg (d+2), sq_nonneg (e-1), sq_nonneg (a+1), sq_nonneg (b-2)]
  · nlinarith [sq_nonneg (d+3), sq_nonneg (e+1), sq_nonneg (a-1), sq_nonneg (b-3), sq_nonneg c]
  · nlinarith [sq_nonneg e, sq_nonneg (a+2), sq_nonneg (b-1), sq_nonneg (c+1), sq_nonneg (d-2)]
  · nlinarith [sq_nonneg a, sq_nonneg (b-2), sq_nonneg (c+1), sq_nonneg (d-1), sq_nonneg (e+2)]
  · nlinarith [sq_nonneg d, sq_nonneg (e-2), sq_nonneg (a+1), sq_nonneg (b-1), sq_nonneg (c+2)]
  · nlinarith [sq_nonneg d, sq_nonneg (e-2), sq_nonneg (a+1), sq_nonneg (b-1), sq_nonneg (c+2)]
  · nlinarith [sq_nonneg (c-3), sq_nonneg (d-1), sq_nonneg (e+1), sq_nonneg (a+3), sq_nonneg b]
  · nlinarith [sq_nonneg (e+3), sq_nonneg (a+1), sq_nonneg (b-1), sq_nonneg (c-3), sq_nonneg d]
  · nlinarith [sq_nonneg b, sq_nonneg (c-2), sq_nonneg (d+1), sq_nonneg (e-1), sq_nonneg (a+2)]
  · nlinarith [sq_nonneg b, sq_nonneg (c-2), sq_nonneg (d+1), sq_nonneg (e-1), sq_nonneg (a+2)]
  · nlinarith [sq_nonneg (a+3), sq_nonneg (b+1), sq_nonneg (c-1), sq_nonneg (d-3), sq_nonneg e]
  · nlinarith [sq_nonneg (a+3), sq_nonneg (b+1), sq_nonneg (c-1), sq_nonneg (d-3), sq_nonneg e]
  · nlinarith [sq_nonneg (a+3), sq_nonneg (b+1), sq_nonneg (c-1), sq_nonneg (d-3), sq_nonneg e]
  · nlinarith [sq_nonneg (a+3), sq_nonneg (b+1), sq_nonneg (c-1), sq_nonneg (d-3), sq_nonneg e]
```
