# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `23 August 2026`\
Line count: `17`\
Turn count: `1`

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
  rw [show z = Real.pi - (x + y) by linarith, Real.sin_pi_sub, Real.sin_add]
  let s1 := Real.sin x; let c1 := Real.cos x; let s2 := Real.sin y; let c2 := Real.cos y
  let u := s1 ^ 2 + s2 ^ 2
  let T := (1 / 64 : ℝ) * (2 * u - 3) ^ 2 * ((2 * u + 1) ^ 2 + 2) +
    (1 / 4) * (s1 ^ 2 - s2 ^ 2) ^ 2 * u * (c1 ^ 2 + c2 ^ 2) +
    s1 ^ 2 * s2 ^ 2 * (s1 * c1 - s2 * c2) ^ 2
  have hid : 27 / 64 - (s1 * s2 * (s1 * c2 + c1 * s2)) ^ 2 = T := by
    linear_combination -(1 / 4 * u ^ 3) * Real.sin_sq_add_cos_sq x - (1 / 4 * u ^ 3) * Real.sin_sq_add_cos_sq y
  have hT : 0 ≤ T := by positivity
  nlinarith [hid, hT, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
```
