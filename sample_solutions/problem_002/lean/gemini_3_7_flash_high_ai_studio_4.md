# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `23 August 2026`\
Line count: `33`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem sin_mul_upper_bound
    (x y z : ℝ)
    (h : x + y + z = Real.pi) :
    Real.sin x * Real.sin y * Real.sin z ≤
      (3 * Real.sqrt 3) / 8 := by
  have h1 : Real.sin x * Real.sin y * Real.sin z =
      (Real.cos (x - y) + Real.cos z) * Real.sin z / 2 := by
    rw [show z = Real.pi - (x + y) by linarith, Real.cos_pi_sub, Real.cos_sub, Real.cos_add]; ring
  rw [h1, ← mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 8 * Real.sqrt 3)]
  have hT : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by positivity)
  have hC : Real.sin z ^ 2 + Real.cos z ^ 2 = 1 := Real.sin_sq_add_cos_sq z
  rcases le_total 0 (Real.sin z) with hz | hz
  · have hid : 8 * Real.sqrt 3 * (3 * Real.sqrt 3 / 8) -
        8 * Real.sqrt 3 * ((Real.cos (x - y) + Real.cos z) * Real.sin z / 2) =
        (2 * Real.sin z - Real.sqrt 3) ^ 2 + 2 * (Real.sqrt 3 * Real.cos z - Real.sin z) ^ 2 +
        4 * Real.sqrt 3 * (1 - Real.cos (x - y)) * Real.sin z := by
      linear_combination 2 * (1 - Real.cos z ^ 2) * hT - 6 * hC
    have : 0 ≤ 1 - Real.cos (x - y) := by linarith [Real.cos_le_one (x - y)]
    have : 0 ≤ 4 * Real.sqrt 3 * (1 - Real.cos (x - y)) * Real.sin z := by positivity
    linarith [sq_nonneg (2 * Real.sin z - Real.sqrt 3),
      sq_nonneg (Real.sqrt 3 * Real.cos z - Real.sin z)]
  · have hid : 8 * Real.sqrt 3 * (3 * Real.sqrt 3 / 8) -
        8 * Real.sqrt 3 * ((Real.cos (x - y) + Real.cos z) * Real.sin z / 2) =
        (2 * Real.sin z + Real.sqrt 3) ^ 2 + 2 * (Real.sqrt 3 * Real.cos z - Real.sin z) ^ 2 +
        4 * Real.sqrt 3 * (1 + Real.cos (x - y)) * (-Real.sin z) := by
      linear_combination 2 * (1 - Real.cos z ^ 2) * hT - 6 * hC
    have : 0 ≤ 1 + Real.cos (x - y) := by linarith [Real.neg_one_le_cos (x - y)]
    have : 0 ≤ -Real.sin z := by linarith
    have : 0 ≤ 4 * Real.sqrt 3 * (1 + Real.cos (x - y)) * (-Real.sin z) := by positivity
    linarith [sq_nonneg (2 * Real.sin z + Real.sqrt 3),
      sq_nonneg (Real.sqrt 3 * Real.cos z - Real.sin z)]
```
