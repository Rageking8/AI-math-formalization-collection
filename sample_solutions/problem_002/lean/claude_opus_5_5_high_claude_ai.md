# Claude Opus 5.5 High (Claude AI)

Model: `Claude Opus 5.5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `50`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem sin_mul_upper_bound
    (x y z : ℝ)
    (h : x + y + z = Real.pi) :
    Real.sin x * Real.sin y * Real.sin z ≤
      (3 * Real.sqrt 3) / 8 := by
  have hz : z = Real.pi - (x + y) := by linarith
  subst hz
  rw [Real.sin_pi_sub]
  have h1 : Real.sin x * Real.sin y
      = (Real.cos (x - y) - Real.cos (x + y)) / 2 := by
    rw [Real.cos_sub, Real.cos_add]; ring
  rw [h1]
  have hu1 : Real.cos (x - y) ≤ 1 := Real.cos_le_one _
  have hu2 : -1 ≤ Real.cos (x - y) := Real.neg_one_le_cos _
  have hst : Real.sin (x + y) ^ 2 + Real.cos (x + y) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < Real.sqrt 3 := by positivity
  set u := Real.cos (x - y) with hu
  set s := Real.sin (x + y) with hs
  set t := Real.cos (x + y) with ht
  set r := Real.sqrt 3 with hrdef
  by_cases hs0 : 0 ≤ s
  · have key : r * (3 * r / 4 - (1 - t) * s)
        = (r * s - (1 - t)) ^ 2 / 2 + (t + 1 / 2) ^ 2 := by
      linear_combination (3 / 4 - s ^ 2 / 2) * hr - (3 / 2) * hst
    have h2 : 0 ≤ r * (3 * r / 4 - (1 - t) * s) := by
      rw [key]; positivity
    have h3 : 0 ≤ 3 * r / 4 - (1 - t) * s := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_pos hr0 (by linarith : (0:ℝ) < -(3 * r / 4 - (1 - t) * s))]
    have hus : (u - 1) * s ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hs0
    nlinarith [h3, hus]
  · push_neg at hs0
    have key : r * (3 * r / 4 - (1 + t) * (-s))
        = (r * (-s) - (1 + t)) ^ 2 / 2 + (t - 1 / 2) ^ 2 := by
      linear_combination (3 / 4 - s ^ 2 / 2) * hr - (3 / 2) * hst
    have h2 : 0 ≤ r * (3 * r / 4 - (1 + t) * (-s)) := by
      rw [key]; positivity
    have h3 : 0 ≤ 3 * r / 4 - (1 + t) * (-s) := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_pos hr0 (by linarith : (0:ℝ) < -(3 * r / 4 - (1 + t) * (-s)))]
    have hus : (u + 1) * s ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hs0.le
    nlinarith [h3, hus]
```
