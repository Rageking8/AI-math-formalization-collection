# Gemini 3.6 Flash High (AI Studio)

Model: `Gemini 3.6 Flash High` (via AI Studio)\
Date: `2 August 2026`\
Line count: `26`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem positive_solutions_sqrt_eq (x : ℝ) (hx : 0 < x) :
    Real.sqrt (2 * (x - 3) ^ 2 + 4) = Real.sqrt (12 / x) ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  constructor
  · intro h
    have h1 : 0 ≤ 2 * (x - 3) ^ 2 + 4 := by positivity
    have h2 : 0 ≤ 12 / x := by positivity
    have h_sq := congr_arg (fun y => y ^ 2) h
    rw [Real.sq_sqrt h1, Real.sq_sqrt h2] at h_sq
    have hx_ne : x ≠ 0 := by positivity
    have h3 : (2 * (x - 3) ^ 2 + 4) * x = 12 := by
      rw [h_sq, div_mul_cancel₀ _ hx_ne]
    have h5 : 2 * (x - 1) * (x - 2) * (x - 3) = 0 := by
      calc 2 * (x - 1) * (x - 2) * (x - 3) = (2 * (x - 3) ^ 2 + 4) * x - 12 := by ring
      _ = 12 - 12 := by rw [h3]
      _ = 0 := by ring
    simp [mul_eq_zero, sub_eq_zero] at h5
    rcases h5 with ((rfl | rfl) | rfl)
    · left; rfl
    · right; left; rfl
    · right; right; rfl
  · rintro (rfl | rfl | rfl)
    · congr 1; norm_num
    · congr 1; norm_num
    · congr 1; norm_num
```
