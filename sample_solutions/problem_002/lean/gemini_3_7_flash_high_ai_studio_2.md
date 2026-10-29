# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `23 August 2026`\
Line count: `78`\
Turn count: `1`

## Solution

```lean4
import Mathlib

lemma one_sub_cos_mul_sin_le (w : ℝ) :
    (1 - Real.cos w) * Real.sin w ≤ (3 * Real.sqrt 3) / 4 := by
  rcases le_total (Real.sin w) 0 with hsin | hsin
  · have h1 : (1 - Real.cos w) * Real.sin w ≤ 0 := by
      nlinarith [Real.cos_le_one w, hsin]
    have h2 : 0 ≤ (3 * Real.sqrt 3) / 4 := by positivity
    linarith
  · have hA_nonneg : 0 ≤ (1 - Real.cos w) * Real.sin w := by
      nlinarith [Real.cos_le_one w, hsin]
    have hB_nonneg : 0 ≤ (3 * Real.sqrt 3) / 4 := by positivity
    have h_sqrt3_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hB_sq : ((3 * Real.sqrt 3) / 4) ^ 2 = 27 / 16 := by
      calc ((3 * Real.sqrt 3) / 4) ^ 2
        _ = 9 * (Real.sqrt 3) ^ 2 / 16 := by ring
        _ = 9 * 3 / 16 := by rw [h_sqrt3_sq]
        _ = 27 / 16 := by norm_num
    have h_pyth := Real.sin_sq_add_cos_sq w
    set c := Real.cos w
    set s := Real.sin w
    have h_sos : 0 ≤ (2 * c + 1) ^ 2 * ((2 * c - 3) ^ 2 + 2) / 16 := by positivity
    have h_alg : (1 - c) ^ 2 * s ^ 2 ≤ 27 / 16 := by
      calc (1 - c) ^ 2 * s ^ 2
        _ = (1 - c) ^ 2 * (1 - c ^ 2) := by
          have : s ^ 2 = 1 - c ^ 2 := by linarith [h_pyth]
          rw [this]
        _ = 27 / 16 - (2 * c + 1) ^ 2 * ((2 * c - 3) ^ 2 + 2) / 16 := by ring
        _ ≤ 27 / 16 := by linarith [h_sos]
    have hA_sq : ((1 - c) * s) ^ 2 ≤ ((3 * Real.sqrt 3) / 4) ^ 2 := by
      calc ((1 - c) * s) ^ 2
        _ = (1 - c) ^ 2 * s ^ 2 := by ring
        _ ≤ 27 / 16 := h_alg
        _ = ((3 * Real.sqrt 3) / 4) ^ 2 := hB_sq.symm
    calc (1 - Real.cos w) * Real.sin w
      _ = Real.sqrt (((1 - Real.cos w) * Real.sin w) ^ 2) := (Real.sqrt_sq hA_nonneg).symm
      _ ≤ Real.sqrt (((3 * Real.sqrt 3) / 4) ^ 2) := Real.sqrt_le_sqrt hA_sq
      _ = (3 * Real.sqrt 3) / 4 := Real.sqrt_sq hB_nonneg

theorem sin_mul_upper_bound
    (x y z : ℝ)
    (h : x + y + z = Real.pi) :
    Real.sin x * Real.sin y * Real.sin z ≤
      (3 * Real.sqrt 3) / 8 := by
  have hz : z = Real.pi - (x + y) := by linarith
  have hsinz : Real.sin z = Real.sin (x + y) := by
    rw [hz, Real.sin_pi_sub]
  have h_prod : 2 * (Real.sin x * Real.sin y) = Real.cos (x - y) - Real.cos (x + y) := by
    rw [Real.cos_sub, Real.cos_add]
    ring
  have h_2P : 2 * (Real.sin x * Real.sin y * Real.sin z) =
      (Real.cos (x - y) - Real.cos (x + y)) * Real.sin (x + y) := by
    calc 2 * (Real.sin x * Real.sin y * Real.sin z)
      _ = (2 * (Real.sin x * Real.sin y)) * Real.sin z := by ring
      _ = (Real.cos (x - y) - Real.cos (x + y)) * Real.sin (x + y) := by rw [h_prod, hsinz]
  rcases le_total 0 (Real.sin (x + y)) with hsin_nonneg | hsin_nonpos
  · have h_le_1 : Real.cos (x - y) - Real.cos (x + y) ≤ 1 - Real.cos (x + y) := by
      linarith [Real.cos_le_one (x - y)]
    have h_bound1 : (Real.cos (x - y) - Real.cos (x + y)) * Real.sin (x + y) ≤
        (1 - Real.cos (x + y)) * Real.sin (x + y) := by
      nlinarith [h_le_1, hsin_nonneg]
    have h_bound2 := one_sub_cos_mul_sin_le (x + y)
    have h_2P_le : 2 * (Real.sin x * Real.sin y * Real.sin z) ≤ (3 * Real.sqrt 3) / 4 := by
      linarith [h_2P, h_bound1, h_bound2]
    linarith [h_2P_le]
  · have h_ge_neg1 : -1 - Real.cos (x + y) ≤ Real.cos (x - y) - Real.cos (x + y) := by
      linarith [Real.neg_one_le_cos (x - y)]
    have h_bound1 : (Real.cos (x - y) - Real.cos (x + y)) * Real.sin (x + y) ≤
        (-1 - Real.cos (x + y)) * Real.sin (x + y) := by
      nlinarith [h_ge_neg1, hsin_nonpos]
    have h_shift : (-1 - Real.cos (x + y)) * Real.sin (x + y) =
        (1 - Real.cos (x + y + Real.pi)) * Real.sin (x + y + Real.pi) := by
      rw [Real.cos_add_pi (x + y), Real.sin_add_pi (x + y)]
      ring
    have h_bound2 := one_sub_cos_mul_sin_le (x + y + Real.pi)
    have h_2P_le : 2 * (Real.sin x * Real.sin y * Real.sin z) ≤ (3 * Real.sqrt 3) / 4 := by
      linarith [h_2P, h_bound1, h_shift, h_bound2]
    linarith [h_2P_le]
```
