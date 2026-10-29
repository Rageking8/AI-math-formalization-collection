# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `2 September 2026`\
Line count: `39`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem sgn_add_sub_eq (x y : ℝ) :
    Real.sign (x + y) + Real.sign (x - y) =
      Real.sign (Real.sin x + x) * (1 + Real.sign (x ^ 4 - y ^ 4)) := by
  have P : ∀ z : ℝ, 0 < z → 0 < Real.sin z + z := fun z h => by
    rcases le_or_gt z 1 with g | g
    · linarith [Real.sin_pos_of_pos_of_lt_pi h (by linarith [Real.pi_gt_three])]
    · linarith [Real.neg_one_le_sin z]
  have Q : ∀ a b : ℝ, b ^ 2 < a ^ 2 → 0 < a ^ 4 - b ^ 4 := fun a b h => by
    nlinarith [sq_nonneg a, sq_nonneg b]
  have hs : Real.sign (Real.sin x + x) = Real.sign x := by
    rcases lt_trichotomy x 0 with h | h | h
    · have := P (-x) (by linarith); rw [Real.sin_neg] at this
      rw [Real.sign_of_neg (by linarith : Real.sin x + x < 0), Real.sign_of_neg h]
    · rw [h]; norm_num
    · rw [Real.sign_of_pos (P x h), Real.sign_of_pos h]
  rw [hs]
  rcases lt_trichotomy (x + y) 0 with h1 | h1 | h1 <;>
    rcases lt_trichotomy (x - y) 0 with h2 | h2 | h2
  · rw [Real.sign_of_neg h1, Real.sign_of_neg h2, Real.sign_of_neg (by linarith : x < 0),
      Real.sign_of_pos (Q x y (by nlinarith))]; norm_num
  · rw [Real.sign_of_neg h1, Real.sign_of_neg (by linarith : x < 0), h2,
      show x ^ 4 - y ^ 4 = 0 by linear_combination (x^3 + x^2*y + x*y^2 + y^3) * h2]; norm_num
  · rw [Real.sign_of_neg h1, Real.sign_of_pos h2,
      Real.sign_of_neg (by linarith [Q y x (by nlinarith : x ^ 2 < y ^ 2)] : x ^ 4 - y ^ 4 < 0)]
    norm_num
  · rw [h1, Real.sign_of_neg h2, Real.sign_of_neg (by linarith : x < 0),
      show x ^ 4 - y ^ 4 = 0 by linear_combination (x^3 - x^2*y + x*y^2 - y^3) * h1]; norm_num
  · rw [show x = 0 by linarith, show y = 0 by linarith]; norm_num
  · rw [h1, Real.sign_of_pos h2, Real.sign_of_pos (by linarith : (0:ℝ) < x),
      show x ^ 4 - y ^ 4 = 0 by linear_combination (x^3 - x^2*y + x*y^2 - y^3) * h1]; norm_num
  · rw [Real.sign_of_pos h1, Real.sign_of_neg h2,
      Real.sign_of_neg (by linarith [Q y x (by nlinarith : x ^ 2 < y ^ 2)] : x ^ 4 - y ^ 4 < 0)]
    norm_num
  · rw [Real.sign_of_pos h1, Real.sign_of_pos (by linarith : (0:ℝ) < x), h2,
      show x ^ 4 - y ^ 4 = 0 by linear_combination (x^3 + x^2*y + x*y^2 + y^3) * h2]; norm_num
  · rw [Real.sign_of_pos h1, Real.sign_of_pos h2, Real.sign_of_pos (by linarith : (0:ℝ) < x),
      Real.sign_of_pos (Q x y (by nlinarith))]; norm_num
```
