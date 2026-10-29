# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `16 August 2026`\
Line count: `90`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem sgn_add_sub_eq (x y : ℝ) :
    Real.sign (x + y) + Real.sign (x - y) =
      Real.sign (Real.sin x + x) * (1 + Real.sign (x ^ 4 - y ^ 4)) := by
  -- Step 1: `sin z + z > 0` whenever `z > 0`
  have key : ∀ z : ℝ, 0 < z → 0 < Real.sin z + z := by
    intro z hz
    by_cases h : z < Real.pi
    · have h1 := Real.sin_pos_of_pos_of_lt_pi hz h
      linarith
    · push_neg at h
      have h1 : -1 ≤ Real.sin z := Real.neg_one_le_sin z
      have h2 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      linarith
  -- Step 2: hence `sign (sin x + x) = sign x`
  have hsign : Real.sign (Real.sin x + x) = Real.sign x := by
    rcases lt_trichotomy x 0 with h | h | h
    · have h1 : 0 < Real.sin (-x) + -x := key (-x) (by linarith)
      rw [Real.sin_neg] at h1
      rw [Real.sign_of_neg (show Real.sin x + x < 0 by linarith), Real.sign_of_neg h]
    · rw [h]; simp
    · rw [Real.sign_of_pos (key x h), Real.sign_of_pos h]
  rw [hsign]
  -- Step 3: case analysis on the signs of `x + y` and `x - y`
  rcases lt_trichotomy (x + y) 0 with ha | ha | ha <;>
    rcases lt_trichotomy (x - y) 0 with hb | hb | hb
  · have hx : x < 0 := by linarith
    have h2 : 0 < x ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg y, mul_pos_of_neg_of_neg hx hx]
    have h1 : 0 < (x + y) * (x - y) := mul_pos_of_neg_of_neg ha hb
    have h3 : 0 < x ^ 4 - y ^ 4 := by
      have e : x ^ 4 - y ^ 4 = (x + y) * (x - y) * (x ^ 2 + y ^ 2) := by ring
      rw [e]; exact mul_pos h1 h2
    rw [Real.sign_of_neg ha, Real.sign_of_neg hb, Real.sign_of_neg hx,
      Real.sign_of_pos h3]
    ring
  · have hx : x < 0 := by linarith
    have h3 : x ^ 4 - y ^ 4 = 0 := by
      have e : x = y := by linarith
      rw [e]; ring
    rw [Real.sign_of_neg ha, hb, Real.sign_of_neg hx, h3, Real.sign_zero]
    ring
  · have h2 : 0 < x ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg (x - y), mul_pos_of_neg_of_neg ha ha]
    have h1 : (x + y) * (x - y) < 0 := mul_neg_of_neg_of_pos ha hb
    have h3 : x ^ 4 - y ^ 4 < 0 := by
      have e : x ^ 4 - y ^ 4 = (x + y) * (x - y) * (x ^ 2 + y ^ 2) := by ring
      rw [e]; exact mul_neg_of_neg_of_pos h1 h2
    rw [Real.sign_of_neg ha, Real.sign_of_pos hb, Real.sign_of_neg h3]
    ring
  · have hx : x < 0 := by linarith
    have h3 : x ^ 4 - y ^ 4 = 0 := by
      have e : y = -x := by linarith
      rw [e]; ring
    rw [ha, Real.sign_of_neg hb, Real.sign_of_neg hx, h3, Real.sign_zero]
    ring
  · have hx : x = 0 := by linarith
    have hy : y = 0 := by linarith
    rw [hx, hy]
    norm_num
  · have hx : 0 < x := by linarith
    have h3 : x ^ 4 - y ^ 4 = 0 := by
      have e : y = -x := by linarith
      rw [e]; ring
    rw [ha, Real.sign_of_pos hb, Real.sign_of_pos hx, h3, Real.sign_zero]
    ring
  · have h2 : 0 < x ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg (x - y), mul_pos ha ha]
    have h1 : (x + y) * (x - y) < 0 := mul_neg_of_pos_of_neg ha hb
    have h3 : x ^ 4 - y ^ 4 < 0 := by
      have e : x ^ 4 - y ^ 4 = (x + y) * (x - y) * (x ^ 2 + y ^ 2) := by ring
      rw [e]; exact mul_neg_of_neg_of_pos h1 h2
    rw [Real.sign_of_pos ha, Real.sign_of_neg hb, Real.sign_of_neg h3]
    ring
  · have hx : 0 < x := by linarith
    have h3 : x ^ 4 - y ^ 4 = 0 := by
      have e : x = y := by linarith
      rw [e]; ring
    rw [Real.sign_of_pos ha, hb, Real.sign_of_pos hx, h3, Real.sign_zero]
    ring
  · have hx : 0 < x := by linarith
    have h2 : 0 < x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y, mul_pos hx hx]
    have h1 : 0 < (x + y) * (x - y) := mul_pos ha hb
    have h3 : 0 < x ^ 4 - y ^ 4 := by
      have e : x ^ 4 - y ^ 4 = (x + y) * (x - y) * (x ^ 2 + y ^ 2) := by ring
      rw [e]; exact mul_pos h1 h2
    rw [Real.sign_of_pos ha, Real.sign_of_pos hb, Real.sign_of_pos hx,
      Real.sign_of_pos h3]
    ring
```
