# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `23 August 2026`\
Line count: `99`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem sin_mul_upper_bound
    (x y z : ℝ)
    (h : x + y + z = Real.pi) :
    Real.sin x * Real.sin y * Real.sin z ≤
      (3 * Real.sqrt 3) / 8 := by
  have h1 : x + y = Real.pi - z := by linarith [h]
  have h2 : Real.cos (x + y) = -Real.cos z := by rw [h1, Real.cos_pi_sub]
  have h3 : 2 * (Real.sin x * Real.sin y) = Real.cos (x - y) + Real.cos z := by
    have hcos_sub := Real.cos_sub x y
    have hcos_add := Real.cos_add x y
    linarith [h2, hcos_sub, hcos_add]
  have h4 : 2 * (Real.sin x * Real.sin y * Real.sin z) =
      (Real.cos (x - y) + Real.cos z) * Real.sin z := by
    calc
      2 * (Real.sin x * Real.sin y * Real.sin z) =
        (2 * (Real.sin x * Real.sin y)) * Real.sin z := by ring
      _ = (Real.cos (x - y) + Real.cos z) * Real.sin z := by rw [h3]
  have h5 : 4 * (Real.sin x * Real.sin y * Real.sin z) ^ 2 =
      (1 - Real.cos z ^ 2) * (Real.cos (x - y) + Real.cos z) ^ 2 := by
    have hsin_sq := Real.sin_sq z
    calc
      4 * (Real.sin x * Real.sin y * Real.sin z) ^ 2 =
        (2 * (Real.sin x * Real.sin y * Real.sin z)) ^ 2 := by ring
      _ = ((Real.cos (x - y) + Real.cos z) * Real.sin z) ^ 2 := by rw [h4]
      _ = (Real.sin z ^ 2) * (Real.cos (x - y) + Real.cos z) ^ 2 := by ring
      _ = (1 - Real.cos z ^ 2) * (Real.cos (x - y) + Real.cos z) ^ 2 := by rw [hsin_sq]
  have hA1 : Real.cos (x - y) ≤ 1 := Real.cos_le_one _
  have hA2 : -1 ≤ Real.cos (x - y) := Real.neg_one_le_cos _
  have hB1 : Real.cos z ≤ 1 := Real.cos_le_one _
  have hB2 : -1 ≤ Real.cos z := Real.neg_one_le_cos _
  have h6 : (1 - Real.cos z ^ 2) * (Real.cos (x - y) + Real.cos z) ^ 2 ≤ 27 / 16 := by
    rcases le_total 0 (Real.cos z) with hB | hB
    · have h_diff : (1 + Real.cos z) ^ 2 - (Real.cos (x - y) + Real.cos z) ^ 2 =
          (1 - Real.cos (x - y)) * (1 + Real.cos (x - y) + 2 * Real.cos z) := by ring
      have h_nonneg1 : 0 ≤ 1 - Real.cos (x - y) := by linarith [hA1]
      have h_nonneg2 : 0 ≤ 1 + Real.cos (x - y) + 2 * Real.cos z := by linarith [hA2, hB]
      have h_diff_nonneg : 0 ≤ (1 - Real.cos (x - y)) *
          (1 + Real.cos (x - y) + 2 * Real.cos z) :=
        mul_nonneg h_nonneg1 h_nonneg2
      have h_le : (Real.cos (x - y) + Real.cos z) ^ 2 ≤ (1 + Real.cos z) ^ 2 := by
        linarith [h_diff, h_diff_nonneg]
      have h1_B_sq : 0 ≤ 1 - Real.cos z ^ 2 := by
        have : 1 - Real.cos z ^ 2 = (1 - Real.cos z) * (1 + Real.cos z) := by ring
        have ha : 0 ≤ 1 - Real.cos z := by linarith [hB1]
        have hb : 0 ≤ 1 + Real.cos z := by linarith [hB2]
        linarith [this, mul_nonneg ha hb]
      have h_prod_le : (1 - Real.cos z ^ 2) * (Real.cos (x - y) + Real.cos z) ^ 2 ≤
          (1 - Real.cos z ^ 2) * (1 + Real.cos z) ^ 2 := by
        nlinarith [h_le, h1_B_sq]
      have h_poly : 27 / 16 - (1 - Real.cos z ^ 2) * (1 + Real.cos z) ^ 2 =
          ((2 * Real.cos z - 1) ^ 2 * ((2 * Real.cos z + 3) ^ 2 + 2)) / 16 := by ring
      have h_poly_nonneg : 0 ≤ ((2 * Real.cos z - 1) ^ 2 *
          ((2 * Real.cos z + 3) ^ 2 + 2)) / 16 := by positivity
      linarith [h_poly, h_poly_nonneg, h_prod_le]
    · have h_diff : (1 - Real.cos z) ^ 2 - (Real.cos (x - y) + Real.cos z) ^ 2 =
          (1 + Real.cos (x - y)) * (1 - Real.cos (x - y) - 2 * Real.cos z) := by ring
      have h_nonneg1 : 0 ≤ 1 + Real.cos (x - y) := by linarith [hA2]
      have h_nonneg2 : 0 ≤ 1 - Real.cos (x - y) - 2 * Real.cos z := by linarith [hA1, hB]
      have h_diff_nonneg : 0 ≤ (1 + Real.cos (x - y)) *
          (1 - Real.cos (x - y) - 2 * Real.cos z) :=
        mul_nonneg h_nonneg1 h_nonneg2
      have h_le : (Real.cos (x - y) + Real.cos z) ^ 2 ≤ (1 - Real.cos z) ^ 2 := by
        linarith [h_diff, h_diff_nonneg]
      have h1_B_sq : 0 ≤ 1 - Real.cos z ^ 2 := by
        have : 1 - Real.cos z ^ 2 = (1 - Real.cos z) * (1 + Real.cos z) := by ring
        have ha : 0 ≤ 1 - Real.cos z := by linarith [hB1]
        have hb : 0 ≤ 1 + Real.cos z := by linarith [hB2]
        linarith [this, mul_nonneg ha hb]
      have h_prod_le : (1 - Real.cos z ^ 2) * (Real.cos (x - y) + Real.cos z) ^ 2 ≤
          (1 - Real.cos z ^ 2) * (1 - Real.cos z) ^ 2 := by
        nlinarith [h_le, h1_B_sq]
      have h_poly : 27 / 16 - (1 - Real.cos z ^ 2) * (1 - Real.cos z) ^ 2 =
          ((2 * Real.cos z + 1) ^ 2 * ((2 * Real.cos z - 3) ^ 2 + 2)) / 16 := by ring
      have h_poly_nonneg : 0 ≤ ((2 * Real.cos z + 1) ^ 2 *
          ((2 * Real.cos z - 3) ^ 2 + 2)) / 16 := by positivity
      linarith [h_poly, h_poly_nonneg, h_prod_le]
  have h7 : (Real.sin x * Real.sin y * Real.sin z) ^ 2 ≤ 27 / 64 := by linarith [h5, h6]
  have hC_sq : ((3 * Real.sqrt 3) / 8) ^ 2 = 27 / 64 := by
    have h3_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by positivity)
    calc
      ((3 * Real.sqrt 3) / 8) ^ 2 = (9 * (Real.sqrt 3) ^ 2) / 64 := by ring
      _ = 27 / 64 := by rw [h3_sq]; ring
  have hC_nonneg : 0 ≤ (3 * Real.sqrt 3) / 8 := by positivity
  by_contra h_gt
  push_neg at h_gt
  have hS_pos : 0 < Real.sin x * Real.sin y * Real.sin z := by linarith [h_gt, hC_nonneg]
  have h_diff : (Real.sin x * Real.sin y * Real.sin z) ^ 2 - ((3 * Real.sqrt 3) / 8) ^ 2 =
      (Real.sin x * Real.sin y * Real.sin z - (3 * Real.sqrt 3) / 8) *
      (Real.sin x * Real.sin y * Real.sin z + (3 * Real.sqrt 3) / 8) := by ring
  have h_mul_pos : 0 < (Real.sin x * Real.sin y * Real.sin z - (3 * Real.sqrt 3) / 8) *
      (Real.sin x * Real.sin y * Real.sin z + (3 * Real.sqrt 3) / 8) := by
    apply mul_pos
    · linarith [h_gt]
    · linarith [hS_pos, hC_nonneg]
  have h_contra : ((3 * Real.sqrt 3) / 8) ^ 2 < (Real.sin x * Real.sin y * Real.sin z) ^ 2 := by
    linarith [h_diff, h_mul_pos]
  linarith [h7, hC_sq, h_contra]
```
