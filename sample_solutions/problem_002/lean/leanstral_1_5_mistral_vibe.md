# Leanstral 1.5 (Mistral Vibe)

Model: `Leanstral 1.5` (via Mistral Vibe)\
Date: `28 July 2026`\
Line count: `139`\
Turn count: `Not applicable`

## Solution

```lean4
import Mathlib

theorem sin_mul_upper_bound
    (x y z : ℝ)
    (h : x + y + z = Real.pi) :
    Real.sin x * Real.sin y * Real.sin z ≤
      (3 * Real.sqrt 3) / 8 := by
  -- identity: sin a * sin b = (cos (a - b) - cos (a + b)) / 2
  have sin_mul_sin_eq (a b : ℝ) : Real.sin a * Real.sin b = (Real.cos (a - b) - Real.cos (a + b)) / 2 := by
    have hcos_sub := Real.cos_sub a b
    have hcos_add := Real.cos_add a b
    linarith
  have hsum : x + y = Real.pi - z := by linarith
  have cos_sum : Real.cos (x + y) = -Real.cos z := by
    rw [hsum, Real.cos_pi_sub]
  rw [sin_mul_sin_eq x y, cos_sum]
  -- Simplify to ((cos (x - y) + cos z) / 2) * sin z
  have h_simplify : (Real.cos (x - y) - (-Real.cos z)) / 2 * Real.sin z =
      (Real.cos (x - y) + Real.cos z) * Real.sin z / 2 := by ring
  rw [h_simplify]
  -- cos(x-y) ≤ 1 and cos(x-y) ≥ -1
  have h_cos_le_one : Real.cos (x - y) ≤ 1 := Real.cos_le_one _
  have h_neg_one_le_cos : -1 ≤ Real.cos (x - y) := by
    have h := Real.cos_sq_add_sin_sq (x - y)
    nlinarith
  by_cases hsinz_nonneg : 0 ≤ Real.sin z
  · -- Case 1: sin z ≥ 0, use cos(x-y) ≤ 1
    have h_bound : (Real.cos (x - y) + Real.cos z) * Real.sin z / 2 ≤
        (1 + Real.cos z) * Real.sin z / 2 := by
      nlinarith
    refine le_trans h_bound ?_
    -- Need: (1 + cos z) * sin z / 2 ≤ 3√3/8
    set c := Real.cos z with hc
    set s := Real.sin z with hs
    have h_sq_sum : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq z
    have hs_nonneg : 0 ≤ s := hsinz_nonneg
    have hL_nonneg : 0 ≤ (1 + c) * s / 2 := by
      have : -1 ≤ c := by
        have h := Real.cos_sq_add_sin_sq z
        nlinarith
      nlinarith
    have hR_nonneg : 0 ≤ (3 * Real.sqrt 3) / 8 := by positivity
    -- Prove via squared difference
    have h_sq_diff_nonneg : 0 ≤ ((3 * Real.sqrt 3) / 8) ^ 2 - ((1 + c) * s / 2) ^ 2 := by
      have h_sq_eq : s ^ 2 = 1 - c ^ 2 := by linarith
      have h_diff : ((3 * Real.sqrt 3) / 8) ^ 2 - ((1 + c) * s / 2) ^ 2 =
          ((2 * c - 1) ^ 2 * (4 * c ^ 2 + 12 * c + 11)) / 64 := by
        calc
          ((3 * Real.sqrt 3) / 8) ^ 2 - ((1 + c) * s / 2) ^ 2
              = (9 * ((Real.sqrt 3) ^ 2)) / 64 - ((1 + c) ^ 2 * s ^ 2) / 4 := by ring
          _ = (9 * 3) / 64 - ((1 + c) ^ 2 * (1 - c ^ 2)) / 4 := by
            rw [Real.sq_sqrt (show 0 ≤ 3 by norm_num), h_sq_eq]
          _ = 27/64 - ((1 + c) ^ 2 * (1 - c ^ 2)) / 4 := by ring
          _ = (27 - 16 * (1 + c) ^ 2 * (1 - c ^ 2)) / 64 := by ring
          _ = ((2 * c - 1) ^ 2 * (4 * c ^ 2 + 12 * c + 11)) / 64 := by ring
      rw [h_diff]
      refine div_nonneg ?_ (by norm_num)
      have h_sq_nonneg : 0 ≤ (2 * c - 1) ^ 2 := pow_two_nonneg _
      have h_quad_pos : 0 ≤ 4 * c ^ 2 + 12 * c + 11 := by
        have : 4 * c ^ 2 + 12 * c + 11 = 4 * (c + 3/2) ^ 2 + 2 := by ring
        rw [this]
        positivity
      nlinarith
    have h_sq_le : ((1 + c) * s / 2) ^ 2 ≤ ((3 * Real.sqrt 3) / 8) ^ 2 := by linarith
    -- From L² ≤ R² and L, R ≥ 0, deduce L ≤ R
    have h_sum_nonneg : 0 ≤ (3 * Real.sqrt 3) / 8 + (1 + c) * s / 2 := by nlinarith
    by_cases h_sum_pos : 0 < (3 * Real.sqrt 3) / 8 + (1 + c) * s / 2
    · have h_prod : 0 ≤ ((3 * Real.sqrt 3) / 8 - (1 + c) * s / 2) *
          ((3 * Real.sqrt 3) / 8 + (1 + c) * s / 2) := by linarith
      have h_diff_nonneg : 0 ≤ (3 * Real.sqrt 3) / 8 - (1 + c) * s / 2 :=
        nonneg_of_mul_nonneg_right (by simpa [mul_comm] using h_prod) h_sum_pos
      linarith
    · have h_sum_zero : (3 * Real.sqrt 3) / 8 + (1 + c) * s / 2 = 0 := by linarith
      have hR_pos : 0 < (3 * Real.sqrt 3) / 8 := by positivity
      nlinarith
  · -- Case 2: sin z < 0, use cos(x-y) ≥ -1
    have hsinz_neg : Real.sin z < 0 := by linarith
    have h_bound : (Real.cos (x - y) + Real.cos z) * Real.sin z / 2 ≤
        (-1 + Real.cos z) * Real.sin z / 2 := by
      nlinarith
    -- Reduce to case 1 via w = π + z
    set w := Real.pi + z with hw
    have hsinw : Real.sin w = -Real.sin z := by
      rw [hw, Real.sin_add, Real.sin_pi, Real.cos_pi]
      ring
    have hcosw : Real.cos w = -Real.cos z := by
      rw [hw, Real.cos_add, Real.cos_pi, Real.sin_pi]
      ring
    have hsinw_nonneg : 0 ≤ Real.sin w := by
      rw [hsinw]
      linarith
    have h_expr_eq : (-1 + Real.cos z) * Real.sin z / 2 = (1 + Real.cos w) * Real.sin w / 2 := by
      rw [hsinw, hcosw]
      ring
    rw [h_expr_eq] at h_bound
    -- Now we need the same inequality as case 1 for w
    have h_case1 : (1 + Real.cos w) * Real.sin w / 2 ≤ (3 * Real.sqrt 3) / 8 := by
      set c := Real.cos w with hc
      set s := Real.sin w with hs
      have h_sq_sum : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq w
      have hs_nonneg : 0 ≤ s := hsinw_nonneg
      have hL_nonneg : 0 ≤ (1 + c) * s / 2 := by
        have : -1 ≤ c := by
          have h := Real.cos_sq_add_sin_sq w
          nlinarith
        nlinarith
      have hR_nonneg : 0 ≤ (3 * Real.sqrt 3) / 8 := by positivity
      have h_sq_diff_nonneg : 0 ≤ ((3 * Real.sqrt 3) / 8) ^ 2 - ((1 + c) * s / 2) ^ 2 := by
        have h_sq_eq : s ^ 2 = 1 - c ^ 2 := by linarith
        have h_diff : ((3 * Real.sqrt 3) / 8) ^ 2 - ((1 + c) * s / 2) ^ 2 =
            ((2 * c - 1) ^ 2 * (4 * c ^ 2 + 12 * c + 11)) / 64 := by
          calc
            ((3 * Real.sqrt 3) / 8) ^ 2 - ((1 + c) * s / 2) ^ 2
                = (9 * ((Real.sqrt 3) ^ 2)) / 64 - ((1 + c) ^ 2 * s ^ 2) / 4 := by ring
            _ = (9 * 3) / 64 - ((1 + c) ^ 2 * (1 - c ^ 2)) / 4 := by
              rw [Real.sq_sqrt (show 0 ≤ 3 by norm_num), h_sq_eq]
            _ = 27/64 - ((1 + c) ^ 2 * (1 - c ^ 2)) / 4 := by ring
            _ = (27 - 16 * (1 + c) ^ 2 * (1 - c ^ 2)) / 64 := by ring
            _ = ((2 * c - 1) ^ 2 * (4 * c ^ 2 + 12 * c + 11)) / 64 := by ring
        rw [h_diff]
        refine div_nonneg ?_ (by norm_num)
        have h_sq_nonneg : 0 ≤ (2 * c - 1) ^ 2 := pow_two_nonneg _
        have h_quad_pos : 0 ≤ 4 * c ^ 2 + 12 * c + 11 := by
          have : 4 * c ^ 2 + 12 * c + 11 = 4 * (c + 3/2) ^ 2 + 2 := by ring
          rw [this]
          positivity
        nlinarith
      have h_sq_le : ((1 + c) * s / 2) ^ 2 ≤ ((3 * Real.sqrt 3) / 8) ^ 2 := by linarith
      have h_sum_nonneg : 0 ≤ (3 * Real.sqrt 3) / 8 + (1 + c) * s / 2 := by nlinarith
      by_cases h_sum_pos : 0 < (3 * Real.sqrt 3) / 8 + (1 + c) * s / 2
      · have h_prod : 0 ≤ ((3 * Real.sqrt 3) / 8 - (1 + c) * s / 2) *
            ((3 * Real.sqrt 3) / 8 + (1 + c) * s / 2) := by linarith
        have h_diff_nonneg : 0 ≤ (3 * Real.sqrt 3) / 8 - (1 + c) * s / 2 :=
          nonneg_of_mul_nonneg_right (by simpa [mul_comm] using h_prod) h_sum_pos
        linarith
      · have h_sum_zero : (3 * Real.sqrt 3) / 8 + (1 + c) * s / 2 = 0 := by linarith
        have hR_pos : 0 < (3 * Real.sqrt 3) / 8 := by positivity
        nlinarith
    exact le_trans h_bound h_case1
```
