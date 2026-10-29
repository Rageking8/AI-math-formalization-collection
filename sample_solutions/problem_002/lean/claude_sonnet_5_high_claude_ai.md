# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `30 July 2026`\
Line count: `67`\
Turn count: `2 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem sin_mul_upper_bound
    (x y z : ℝ)
    (h : x + y + z = Real.pi) :
    Real.sin x * Real.sin y * Real.sin z ≤
      (3 * Real.sqrt 3) / 8 := by
  have key : ∀ S C : ℝ, 0 ≤ S → S ^ 2 + C ^ 2 = 1 → S * (1 - C) ≤ 3 * Real.sqrt 3 / 4 := by
    intro S C hS hSC
    have hC1 : C ≤ 1 := by nlinarith [sq_nonneg (C - 1), sq_nonneg S]
    have hnn : 0 ≤ S * (1 - C) := mul_nonneg hS (by linarith)
    have hsqrt3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hK : (3 * Real.sqrt 3 / 4) ^ 2 = 27 / 16 := by
      have e : (3 * Real.sqrt 3 / 4) ^ 2 = 9 * (Real.sqrt 3 ^ 2) / 16 := by ring
      rw [e, hsqrt3sq]; norm_num
    have hKnn : 0 ≤ 3 * Real.sqrt 3 / 4 := by positivity
    have hS2 : S ^ 2 = 1 - C ^ 2 := by linarith
    have hexpand : (S * (1 - C)) ^ 2 = (1 - C) ^ 3 * (1 + C) := by
      have step : (S * (1 - C)) ^ 2 = S ^ 2 * (1 - C) ^ 2 := by ring
      rw [step, hS2]; ring
    have hpoly : (S * (1 - C)) ^ 2 ≤ (3 * Real.sqrt 3 / 4) ^ 2 := by
      rw [hK, hexpand]
      nlinarith [sq_nonneg (C + 1/2), sq_nonneg (C - 3/2),
        mul_nonneg (sq_nonneg (C + 1/2)) (sq_nonneg (C - 3/2))]
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < S * (1 - C) + 3 * Real.sqrt 3 / 4 := by linarith
    have hprod2 : (S * (1 - C) - 3 * Real.sqrt 3 / 4) * (S * (1 - C) + 3 * Real.sqrt 3 / 4) > 0 :=
      mul_pos (by linarith) hpos
    nlinarith [hprod2, hpoly]
  have hz : z = Real.pi - (x + y) := by linarith
  have hsinz : Real.sin z = Real.sin (x + y) := by rw [hz, Real.sin_pi_sub]
  rw [hsinz]
  have hprod : Real.sin x * Real.sin y = (Real.cos (x - y) - Real.cos (x + y)) / 2 := by
    have hca : Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y :=
      Real.cos_sub x y
    have hcb : Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y :=
      Real.cos_add x y
    linarith
  have expand2 : Real.sin x * Real.sin y * Real.sin (x + y)
      = Real.sin (x + y) * (Real.cos (x - y) - Real.cos (x + y)) / 2 := by
    rw [hprod]; ring
  rw [expand2]
  have hSC : Real.sin (x + y) ^ 2 + Real.cos (x + y) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x + y)
  have hCd1 : Real.cos (x - y) ≤ 1 := Real.cos_le_one _
  have hCdm1 : -1 ≤ Real.cos (x - y) := Real.neg_one_le_cos _
  have hbound : Real.sin (x + y) * Real.cos (x - y) ≤ |Real.sin (x + y)| := by
    calc Real.sin (x + y) * Real.cos (x - y)
        ≤ |Real.sin (x + y) * Real.cos (x - y)| := le_abs_self _
      _ = |Real.sin (x + y)| * |Real.cos (x - y)| := abs_mul _ _
      _ ≤ |Real.sin (x + y)| * 1 :=
          mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hCdm1, hCd1⟩) (abs_nonneg _)
      _ = |Real.sin (x + y)| := mul_one _
  have habs : |Real.sin (x + y)| - Real.sin (x + y) * Real.cos (x + y) ≤ 3 * Real.sqrt 3 / 4 := by
    rcases le_total 0 (Real.sin (x + y)) with hSpos | hSneg
    · rw [abs_of_nonneg hSpos]
      nlinarith [key (Real.sin (x + y)) (Real.cos (x + y)) hSpos hSC]
    · rw [abs_of_nonpos hSneg]
      have hSC' : (-(Real.sin (x + y))) ^ 2 + (-(Real.cos (x + y))) ^ 2 = 1 := by
        have e : (-(Real.sin (x + y))) ^ 2 + (-(Real.cos (x + y))) ^ 2
            = Real.sin (x + y) ^ 2 + Real.cos (x + y) ^ 2 := by ring
        rw [e]; exact hSC
      have h' := key (-(Real.sin (x + y))) (-(Real.cos (x + y))) (by linarith) hSC'
      nlinarith [h']
  have final : Real.sin (x + y) * (Real.cos (x - y) - Real.cos (x + y)) ≤ 3 * Real.sqrt 3 / 4 := by
    nlinarith [hbound, habs]
  linarith [final]
```
