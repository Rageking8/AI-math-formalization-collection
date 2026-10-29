# Grok 4.6 xHigh (Arena AI)

Model: `grok-4.6-xhigh` (via Arena AI)\
Date: `17 August 2026`\
Line count: `60`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  let s := Real.sqrt (17 / 8)
  have hs2 : s ^ 2 = 17 / 8 := Real.sq_sqrt (by norm_num)
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hs_lt : s < 47 / 32 := by
    have hsq : s ^ 2 < (47 / 32) ^ 2 := by
      rw [hs2]
      norm_num
    have hd : 0 < (47 / 32) ^ 2 - s ^ 2 := sub_pos.mpr hsq
    rw [sq_sub_sq] at hd
    have hsumpos : 0 < 47 / 32 + s := by positivity
    rcases (mul_pos_iff.mp hd) with ⟨hdiffpos, _⟩ | ⟨_, hsumneg⟩
    · linarith
    · linarith
  have heq : x ^ 4 - 4 * x ^ 3 + (63 / 8) * x ^ 2 - 12 * x + 9 =
      (x ^ 2 + (-2 + s) * x + 3) * (x ^ 2 + (-2 - s) * x + 3) := by
    have htemp : (x ^ 2 + (-2 + s) * x + 3) * (x ^ 2 + (-2 - s) * x + 3) =
        x ^ 4 - 4 * x ^ 3 + (10 - s ^ 2) * x ^ 2 - 12 * x + 9 := by ring
    rw [htemp, hs2]
    ring
  rw [heq]
  have hquad1 : x ^ 2 + (-2 + s) * x + 3 > 0 := by
    let a := -2 + s
    have ha_lt : a ^ 2 < 12 := by
      have : a ^ 2 = 49 / 8 - 4 * s := by
        calc a ^ 2 = (-2 + s) ^ 2 := rfl
          _ = 4 - 4 * s + s ^ 2 := by ring
          _ = 4 - 4 * s + 17 / 8 := by rw [hs2]
          _ = 49 / 8 - 4 * s := by ring
      rw [this]
      have h49 : (49 / 8 : ℝ) < 12 := by norm_num
      linarith [hs_nn, h49]
    have h4 : (4 : ℝ) * (x ^ 2 + a * x + 3) = (2 * x + a) ^ 2 + (12 - a ^ 2) := by ring
    have h12 : 0 < 12 - a ^ 2 := sub_pos.mpr ha_lt
    have : 0 < 4 * (x ^ 2 + a * x + 3) := by
      rw [h4]
      nlinarith [sq_nonneg (2 * x + a)]
    linarith
  have hquad2 : x ^ 2 + (-2 - s) * x + 3 > 0 := by
    let b := -2 - s
    have hb_lt : b ^ 2 < 12 := by
      have : b ^ 2 = 49 / 8 + 4 * s := by
        calc b ^ 2 = (-2 - s) ^ 2 := rfl
          _ = 4 + 4 * s + s ^ 2 := by ring
          _ = 4 + 4 * s + 17 / 8 := by rw [hs2]
          _ = 49 / 8 + 4 * s := by ring
      rw [this]
      have hs4 : 4 * s < 47 / 8 := by
        have : (4 : ℝ) * (47 / 32) = 47 / 8 := by norm_num
        linarith [hs_lt]
      linarith [hs4]
    have h4 : (4 : ℝ) * (x ^ 2 + b * x + 3) = (2 * x + b) ^ 2 + (12 - b ^ 2) := by ring
    have h12 : 0 < 12 - b ^ 2 := sub_pos.mpr hb_lt
    have : 0 < 4 * (x ^ 2 + b * x + 3) := by
      rw [h4]
      nlinarith [sq_nonneg (2 * x + b)]
    linarith
  exact mul_pos hquad1 hquad2
```
