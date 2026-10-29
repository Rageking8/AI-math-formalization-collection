# GPT-6.1 Sol Max (Arena AI)

Model: `gpt-6.1-sol-max` (via Arena AI)\
Date: `1 October 2026`\
Line count: `68`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem min_poly_eq_max_exp_iff_eq_two (x : ℝ) :
    min (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1) = max ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x) ↔ x = 2 := by
  constructor
  · intro h
    rcases lt_trichotomy x (2 : ℝ) with hx | hx | hx
    · exfalso
      have hp : x ^ 3 - 2 * x ^ 2 + 3 ≤ 3 := by
        have hm : x ^ 2 * (x - 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x)
            (by linarith only [hx])
        nlinarith only [hm]
      have he : (2 : ℝ) ^ x < 4 := by
        calc
          (2 : ℝ) ^ x < (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hx
          _ = 4 := by norm_num [Real.rpow_natCast]
      have hmin :=
        min_le_left (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1)
      have hmax :=
        le_max_right ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x)
      rw [h] at hmin
      linarith only [hmin, hmax, hp, he]
    · exact hx
    · exfalso
      have hlog : (2 : ℝ) / 3 ≤ Real.log 3 := by
        have hi := Real.log_le_sub_one_of_pos
          (by norm_num : 0 < (3 : ℝ)⁻¹)
        rw [Real.log_inv] at hi
        norm_num at hi
        linarith only [hi]
      let t : ℝ := (x - 2) / 2 * Real.log 3
      have ht : (x - 2) / 3 ≤ t := by
        dsimp [t]
        have hm : 0 ≤ (x - 2) * (Real.log 3 - 2 / 3) :=
          mul_nonneg (by linarith only [hx]) (sub_nonneg.mpr hlog)
        nlinarith only [hm]
      have hexp : x + 1 ≤ 3 * Real.exp t := by
        linarith only [ht, Real.add_one_le_exp t]
      have heq : (3 * Real.exp t) ^ 2 = (3 : ℝ) ^ x := by
        calc
          (3 * Real.exp t) ^ 2 =
              (Real.exp (Real.log 3) * Real.exp t) ^ 2 := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
          _ = Real.exp ((Real.log 3 + t) + (Real.log 3 + t)) := by
            rw [← Real.exp_add, pow_two, ← Real.exp_add]
          _ = Real.exp (Real.log 3 * x) := by
            congr 1
            dsimp [t]
            ring
          _ = (3 : ℝ) ^ x := by
            rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      have hprod :
          0 ≤ (3 * Real.exp t - (x + 1)) *
            (3 * Real.exp t + (x + 1)) :=
        mul_nonneg (sub_nonneg.mpr hexp)
          (by linarith only [hx, hexp])
      have hpow : x ^ 2 + 5 < (3 : ℝ) ^ x := by
        nlinarith only [hprod, heq, hx]
      have hmin :=
        min_le_right (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1)
      have hmax :=
        le_max_left ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x)
      rw [h] at hmin
      linarith only [hmin, hmax, hpow]
  · rintro rfl
    norm_num [Real.rpow_natCast]
```
