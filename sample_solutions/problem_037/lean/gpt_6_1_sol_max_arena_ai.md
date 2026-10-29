# GPT-6.1 Sol Max (Arena AI)

Model: `gpt-6.1-sol-max` (via Arena AI)\
Date: `1 October 2026`\
Line count: `64`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem min_poly_eq_max_exp_iff_eq_two (x : ℝ) :
    min (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1) = max ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x) ↔ x = 2 := by
  constructor
  · intro heq
    rcases lt_trichotomy x 2 with hx | hx | hx
    · exfalso
      have hf : x ^ 3 - 2 * x ^ 2 + 3 ≤ 3 := by
        have hm : x ^ 2 * (x - 2) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) (by linarith)
        nlinarith only [hm]
      have hp : (2 : ℝ) ^ x < 4 := by
        have hh : (2 : ℝ) ^ x < (2 : ℝ) ^ (2 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          · norm_num
          · exact hx
        norm_num [Real.rpow_natCast] at hh
        exact hh
      have hmin := min_le_left (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1)
      have hmax := le_max_right ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x)
      linarith only [heq, hf, hp, hmin, hmax]
    · exact hx
    · exfalso
      have hlog : (2 : ℝ) / 3 ≤ Real.log 3 := by
        have he := Real.add_one_le_exp (-Real.log (3 : ℝ))
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)] at he
        norm_num at he
        linarith only [he]
      have ht : 0 ≤ (x - 2) / 2 := by
        linarith only [hx]
      have hy : (x + 1) / 3 ≤ (3 : ℝ) ^ ((x - 2) / 2) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
        have he := Real.add_one_le_exp (Real.log (3 : ℝ) * ((x - 2) / 2))
        have hm := mul_le_mul_of_nonneg_right hlog ht
        linarith only [he, hm]
      have hsq :
          ((x + 1) / 3) ^ 2 ≤ ((3 : ℝ) ^ ((x - 2) / 2)) ^ 2 := by
        have ha : 0 ≤ (x + 1) / 3 := by
          linarith only [hx]
        have hb : 0 ≤ (3 : ℝ) ^ ((x - 2) / 2) := by
          positivity
        simpa only [pow_two] using mul_le_mul hy hy ha hb
      have hpow :
          (3 : ℝ) ^ x = 9 * ((3 : ℝ) ^ ((x - 2) / 2)) ^ 2 := by
        simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
        have he :
            Real.log (3 : ℝ) * x =
              (Real.log (3 : ℝ) + Real.log (3 : ℝ)) +
                (Real.log (3 : ℝ) * ((x - 2) / 2) +
                  Real.log (3 : ℝ) * ((x - 2) / 2)) := by
          ring
        rw [he]
        simp only [Real.exp_add,
          Real.exp_log (by norm_num : (0 : ℝ) < 3), pow_two]
        ring
      have hgt : x ^ 2 - 1 < (3 : ℝ) ^ x - 6 := by
        rw [hpow]
        nlinarith only [hx, hsq]
      have hmin := min_le_right (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1)
      have hmax := le_max_left ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x)
      linarith only [heq, hgt, hmin, hmax]
  · rintro rfl
    norm_num [Real.rpow_natCast]
```
