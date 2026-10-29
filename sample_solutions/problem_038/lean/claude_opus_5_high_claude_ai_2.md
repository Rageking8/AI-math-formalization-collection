# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `31 August 2026`\
Line count: `27`\
Turn count: `3`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

set_option maxHeartbeats 1000000 in
theorem min_abs_diff_le_two (a b c d e : ℝ)
    (h_sum : a + b + c + d + e = 0) (h_sq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 10) :
      (min |a - b| (min |b - c| (min |c - d| (min |d - e| |e - a|)))) ≤ 2 := by
  by_contra hc
  push_neg at hc
  simp only [lt_min_iff] at hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  have h0 : (a-b)^2 + (b-c)^2 + (c-d)^2 + (d-e)^2 + (e-a)^2
      + ((a-c)^2 + (b-d)^2 + (c-e)^2 + (d-a)^2 + (e-b)^2) = 50 := by
    linear_combination 5 * h_sq - (a+b+c+d+e) * h_sum
  rcases lt_abs.1 h1 with h1|h1 <;> rcases lt_abs.1 h2 with h2|h2 <;>
    rcases lt_abs.1 h3 with h3|h3 <;> rcases lt_abs.1 h4 with h4|h4 <;>
      rcases lt_abs.1 h5 with h5|h5 <;>
  linarith [h0,
    sq_nonneg (a-b-2), sq_nonneg (a-b+2), sq_nonneg (a-b-3), sq_nonneg (a-b+3),
    sq_nonneg (b-c-2), sq_nonneg (b-c+2), sq_nonneg (b-c-3), sq_nonneg (b-c+3),
    sq_nonneg (c-d-2), sq_nonneg (c-d+2), sq_nonneg (c-d-3), sq_nonneg (c-d+3),
    sq_nonneg (d-e-2), sq_nonneg (d-e+2), sq_nonneg (d-e-3), sq_nonneg (d-e+3),
    sq_nonneg (e-a-2), sq_nonneg (e-a+2), sq_nonneg (e-a-3), sq_nonneg (e-a+3),
    sq_nonneg (a-c-4), sq_nonneg (a-c+4), sq_nonneg (a-c-1), sq_nonneg (a-c+1),
    sq_nonneg (b-d-4), sq_nonneg (b-d+4), sq_nonneg (b-d-1), sq_nonneg (b-d+1),
    sq_nonneg (c-e-4), sq_nonneg (c-e+4), sq_nonneg (c-e-1), sq_nonneg (c-e+1),
    sq_nonneg (d-a-4), sq_nonneg (d-a+4), sq_nonneg (d-a-1), sq_nonneg (d-a+1),
    sq_nonneg (e-b-4), sq_nonneg (e-b+4), sq_nonneg (e-b-1), sq_nonneg (e-b+1)]
```
