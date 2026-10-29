# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `24 August 2026`\
Line count: `210`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem floor_ceil_eq_fourth_root (x : ℝ) :
    (⌊x * ⌊x⌋⌋ : ℝ) - (⌈x * ⌈x⌉⌉ : ℝ) ^ 3 = x ^ 4 - 31 ↔ x = (5 : ℝ) ^ ((1 : ℝ) / 4) := by
  have cube_mono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → a ^ 3 ≤ b ^ 3 := by
    intro a b ha hab
    have hb : (0:ℝ) ≤ b := le_trans ha hab
    nlinarith [mul_nonneg ha hb, sq_nonneg a, sq_nonneg b]
  have hy0 : (0:ℝ) < (5:ℝ) ^ ((1:ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hy4 : ((5:ℝ) ^ ((1:ℝ) / 4)) ^ 4 = 5 := by
    rw [← Real.rpow_natCast ((5:ℝ) ^ ((1:ℝ) / 4)) 4,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 5)]
    norm_num
  have key : ∀ z : ℝ, 0 < z → z ^ 4 = 5 → z = (5:ℝ) ^ ((1:ℝ) / 4) := by
    intro z hz hz4
    have hfac : (z - (5:ℝ) ^ ((1:ℝ) / 4)) *
        ((z + (5:ℝ) ^ ((1:ℝ) / 4)) * (z ^ 2 + ((5:ℝ) ^ ((1:ℝ) / 4)) ^ 2)) = 0 := by
      linear_combination hz4 - hy4
    rcases mul_eq_zero.1 hfac with h' | h'
    · linarith
    · exfalso
      have hpos : 0 < (z + (5:ℝ) ^ ((1:ℝ) / 4)) * (z ^ 2 + ((5:ℝ) ^ ((1:ℝ) / 4)) ^ 2) :=
        mul_pos (by linarith) (by nlinarith [sq_nonneg z, hy0])
      linarith
  constructor
  · intro h
    rcases le_or_gt 2 x with hx2 | hx2
    · exfalso
      have hx0 : (0:ℝ) ≤ x := by linarith
      have hfl : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
      have hcl : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
      have hAle : x * (⌊x⌋ : ℝ) ≤ x ^ 2 := by nlinarith
      have hA : (⌊x * (⌊x⌋ : ℝ)⌋ : ℝ) ≤ x ^ 2 := le_trans (Int.floor_le _) hAle
      have hBle : x ^ 2 ≤ x * (⌈x⌉ : ℝ) := by nlinarith
      have hB : x ^ 2 ≤ (⌈x * (⌈x⌉ : ℝ)⌉ : ℝ) := le_trans hBle (Int.le_ceil _)
      have hB3 : (x ^ 2) ^ 3 ≤ ((⌈x * (⌈x⌉ : ℝ)⌉ : ℝ)) ^ 3 := cube_mono _ _ (sq_nonneg x) hB
      have k2 : (4:ℝ) ≤ x ^ 2 := by nlinarith
      have k4 : (16:ℝ) ≤ x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 4)]
      have k6 : 16 * x ^ 2 ≤ x ^ 6 := by nlinarith [sq_nonneg x]
      nlinarith [h, hA, hB3]
    · rcases le_or_gt 1 x with hx1 | hx1
      · rcases eq_or_lt_of_le hx1 with heq | hx1'
        · exfalso
          rw [← heq] at h
          norm_num at h
        · have hfl : ⌊x⌋ = 1 := by
            have h1 : (1:ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by push_cast; linarith)
            have h2 : ⌊x⌋ < 2 := Int.floor_lt.mpr (by push_cast; linarith)
            omega
          have hce : ⌈x⌉ = 2 := by
            have h1 : ⌈x⌉ ≤ 2 := Int.ceil_le.mpr (by push_cast; linarith)
            have h2 : (1:ℤ) < ⌈x⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
            omega
          have hv : x * (⌊x⌋ : ℝ) = x := by rw [hfl]; push_cast; ring
          have hA1 : (⌊x * (⌊x⌋ : ℝ)⌋ : ℝ) = 1 := by
            rw [hv, hfl]; norm_num
          have hw : x * (⌈x⌉ : ℝ) = 2 * x := by rw [hce]; push_cast; ring
          have hBlow : (2:ℤ) < ⌈x * (⌈x⌉ : ℝ)⌉ := by
            rw [Int.lt_ceil, hw]; push_cast; linarith
          have hBhigh : ⌈x * (⌈x⌉ : ℝ)⌉ ≤ 4 := by
            rw [Int.ceil_le, hw]; push_cast; linarith
          have hBcase : ⌈x * (⌈x⌉ : ℝ)⌉ = 3 ∨ ⌈x * (⌈x⌉ : ℝ)⌉ = 4 := by omega
          rw [hA1] at h
          rcases hBcase with hB | hB
          · rw [hB] at h
            push_cast at h
            exact key x (by linarith) (by linarith)
          · exfalso
            rw [hB] at h
            push_cast at h
            nlinarith [h, sq_nonneg (x ^ 2)]
      · rcases le_or_gt 0 x with hx0 | hx0
        · exfalso
          have hfl : ⌊x⌋ = 0 := by
            have h1 : (0:ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by push_cast; linarith)
            have h2 : ⌊x⌋ < 1 := Int.floor_lt.mpr (by push_cast; linarith)
            omega
          have hv : x * (⌊x⌋ : ℝ) = 0 := by rw [hfl]; push_cast; ring
          have hA0 : (⌊x * (⌊x⌋ : ℝ)⌋ : ℝ) = 0 := by
            rw [hv]; norm_num
          have hc2 : (⌈x⌉ : ℝ) ≤ 1 := by
            have : ⌈x⌉ ≤ 1 := Int.ceil_le.mpr (by push_cast; linarith)
            exact_mod_cast this
          have hc1 : (0:ℝ) ≤ (⌈x⌉ : ℝ) := le_trans hx0 (Int.le_ceil x)
          have hp1 : (0:ℝ) ≤ x * (⌈x⌉ : ℝ) := mul_nonneg hx0 hc1
          have hp2 : x * (⌈x⌉ : ℝ) ≤ 1 := by nlinarith
          have hBl : ⌈x * (⌈x⌉ : ℝ)⌉ ≤ 1 := Int.ceil_le.mpr (by push_cast; linarith)
          have hBg : (-1:ℤ) < ⌈x * (⌈x⌉ : ℝ)⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
          have hBr1 : (0:ℝ) ≤ (⌈x * (⌈x⌉ : ℝ)⌉ : ℝ) := by
            have : (0:ℤ) ≤ ⌈x * (⌈x⌉ : ℝ)⌉ := by omega
            exact_mod_cast this
          have hBr2 : (⌈x * (⌈x⌉ : ℝ)⌉ : ℝ) ≤ 1 := by exact_mod_cast hBl
          have hcube : (⌈x * (⌈x⌉ : ℝ)⌉ : ℝ) ^ 3 ≤ 1 := by
            have h' := cube_mono _ 1 hBr1 hBr2
            linarith
          have hxsq : x ^ 2 ≤ 1 := by nlinarith
          have hx4 : x ^ 4 ≤ 1 := by nlinarith [sq_nonneg x]
          rw [hA0] at h
          linarith
        · rcases le_or_gt (-1) x with hxm1 | hxm1
          · exfalso
            have hfl : ⌊x⌋ = -1 := by
              have h1 : (-1:ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by push_cast; linarith)
              have h2 : ⌊x⌋ < 0 := Int.floor_lt.mpr (by push_cast; linarith)
              omega
            have hv : x * (⌊x⌋ : ℝ) = -x := by rw [hfl]; push_cast; ring
            have hAge : (0:ℤ) ≤ ⌊x * (⌊x⌋ : ℝ)⌋ := by
              rw [Int.le_floor, hv]; push_cast; linarith
            have hc1 : (-1:ℝ) ≤ (⌈x⌉ : ℝ) := le_trans hxm1 (Int.le_ceil x)
            have hc2 : (⌈x⌉ : ℝ) ≤ 0 := by
              have : ⌈x⌉ ≤ 0 := Int.ceil_le.mpr (by push_cast; linarith)
              exact_mod_cast this
            have hp1 : (0:ℝ) ≤ x * (⌈x⌉ : ℝ) := by nlinarith
            have hp2 : x * (⌈x⌉ : ℝ) ≤ 1 := by nlinarith
            have hBl : ⌈x * (⌈x⌉ : ℝ)⌉ ≤ 1 := Int.ceil_le.mpr (by push_cast; linarith)
            have hBg : (-1:ℤ) < ⌈x * (⌈x⌉ : ℝ)⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
            have hBr1 : (0:ℝ) ≤ (⌈x * (⌈x⌉ : ℝ)⌉ : ℝ) := by
              have : (0:ℤ) ≤ ⌈x * (⌈x⌉ : ℝ)⌉ := by omega
              exact_mod_cast this
            have hBr2 : (⌈x * (⌈x⌉ : ℝ)⌉ : ℝ) ≤ 1 := by exact_mod_cast hBl
            have hcube : (⌈x * (⌈x⌉ : ℝ)⌉ : ℝ) ^ 3 ≤ 1 := by
              have h' := cube_mono _ 1 hBr1 hBr2
              linarith
            have hAr1 : (0:ℝ) ≤ (⌊x * (⌊x⌋ : ℝ)⌋ : ℝ) := by exact_mod_cast hAge
            have hxsq : x ^ 2 ≤ 1 := by nlinarith
            have hx4 : x ^ 4 ≤ 1 := by nlinarith [sq_nonneg x]
            linarith
          · rcases le_or_gt x (-2) with hxm2 | hxm2
            · exfalso
              have hxneg : x < 0 := by linarith
              have hf1 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
              have hAle : x * (⌊x⌋ : ℝ) ≤ x * (x - 1) := by nlinarith
              have hA : (⌊x * (⌊x⌋ : ℝ)⌋ : ℝ) ≤ x * (x - 1) := le_trans (Int.floor_le _) hAle
              have hclr : (⌈x⌉ : ℝ) ≤ -2 := by
                have : ⌈x⌉ ≤ -2 := Int.ceil_le.mpr (by push_cast; linarith)
                exact_mod_cast this
              have hBge : -2 * x ≤ x * (⌈x⌉ : ℝ) := by nlinarith
              have hB : -2 * x ≤ (⌈x * (⌈x⌉ : ℝ)⌉ : ℝ) := le_trans hBge (Int.le_ceil _)
              have hB3 : (-2 * x) ^ 3 ≤ ((⌈x * (⌈x⌉ : ℝ)⌉ : ℝ)) ^ 3 :=
                cube_mono _ _ (by linarith) hB
              have k1 : x ^ 3 ≤ -2 * x ^ 2 := by nlinarith [sq_nonneg x]
              have k2 : (4:ℝ) ≤ x ^ 2 := by nlinarith
              have k3 : -(x ^ 2) ≤ x := by nlinarith
              have k4 : 4 * x ^ 2 ≤ x ^ 4 := by nlinarith [sq_nonneg x]
              nlinarith [h, hA, hB3, k1, k2, k3, k4]
            · exfalso
              have hfl : ⌊x⌋ = -2 := by
                have h1 : (-2:ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by push_cast; linarith)
                have h2 : ⌊x⌋ < -1 := Int.floor_lt.mpr (by push_cast; linarith)
                omega
              have hce : ⌈x⌉ = -1 := by
                have h1 : ⌈x⌉ ≤ -1 := Int.ceil_le.mpr (by push_cast; linarith)
                have h2 : (-2:ℤ) < ⌈x⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
                omega
              have hv : x * (⌊x⌋ : ℝ) = -2 * x := by rw [hfl]; push_cast; ring
              have hw : x * (⌈x⌉ : ℝ) = -x := by rw [hce]; push_cast; ring
              have hAge : (2:ℤ) ≤ ⌊x * (⌊x⌋ : ℝ)⌋ := by
                rw [Int.le_floor, hv]; push_cast; linarith
              have hBle : ⌈x * (⌈x⌉ : ℝ)⌉ ≤ 2 := by
                rw [Int.ceil_le, hw]; push_cast; linarith
              have hBge : (-1:ℤ) < ⌈x * (⌈x⌉ : ℝ)⌉ := by
                rw [Int.lt_ceil, hw]; push_cast; linarith
              have hAr : (2:ℝ) ≤ (⌊x * (⌊x⌋ : ℝ)⌋ : ℝ) := by exact_mod_cast hAge
              have hBr1 : (0:ℝ) ≤ (⌈x * (⌈x⌉ : ℝ)⌉ : ℝ) := by
                have : (0:ℤ) ≤ ⌈x * (⌈x⌉ : ℝ)⌉ := by omega
                exact_mod_cast this
              have hBr2 : (⌈x * (⌈x⌉ : ℝ)⌉ : ℝ) ≤ 2 := by exact_mod_cast hBle
              have hcube : (⌈x * (⌈x⌉ : ℝ)⌉ : ℝ) ^ 3 ≤ 8 := by
                have h' := cube_mono _ 2 hBr1 hBr2
                linarith
              have hxsq : x ^ 2 < 4 := by nlinarith
              have hx4 : x ^ 4 < 16 := by nlinarith [sq_nonneg x]
              linarith
  · intro h
    subst h
    have hy1 : (1:ℝ) < (5:ℝ) ^ ((1:ℝ) / 4) := by
      by_contra hc
      push_neg at hc
      have h1 : ((5:ℝ) ^ ((1:ℝ) / 4)) ^ 2 ≤ 1 := by nlinarith
      have h2 : ((5:ℝ) ^ ((1:ℝ) / 4)) ^ 4 ≤ 1 := by
        nlinarith [h1, sq_nonneg ((5:ℝ) ^ ((1:ℝ) / 4))]
      linarith
    have hy15 : (5:ℝ) ^ ((1:ℝ) / 4) < 3 / 2 := by
      by_contra hc
      push_neg at hc
      have h1 : (9:ℝ) / 4 ≤ ((5:ℝ) ^ ((1:ℝ) / 4)) ^ 2 := by nlinarith
      have h2 : (81:ℝ) / 16 ≤ ((5:ℝ) ^ ((1:ℝ) / 4)) ^ 4 := by nlinarith [h1]
      linarith
    have hfl : ⌊(5:ℝ) ^ ((1:ℝ) / 4)⌋ = 1 := by
      have h1 : (1:ℤ) ≤ ⌊(5:ℝ) ^ ((1:ℝ) / 4)⌋ := Int.le_floor.mpr (by push_cast; linarith)
      have h2 : ⌊(5:ℝ) ^ ((1:ℝ) / 4)⌋ < 2 := Int.floor_lt.mpr (by push_cast; linarith)
      omega
    have hce : ⌈(5:ℝ) ^ ((1:ℝ) / 4)⌉ = 2 := by
      have h1 : ⌈(5:ℝ) ^ ((1:ℝ) / 4)⌉ ≤ 2 := Int.ceil_le.mpr (by push_cast; linarith)
      have h2 : (1:ℤ) < ⌈(5:ℝ) ^ ((1:ℝ) / 4)⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
      omega
    have hmul : (5:ℝ) ^ ((1:ℝ) / 4) * (⌊(5:ℝ) ^ ((1:ℝ) / 4)⌋ : ℝ) = (5:ℝ) ^ ((1:ℝ) / 4) := by
      rw [hfl]; push_cast; ring
    have e1 : (⌊(5:ℝ) ^ ((1:ℝ) / 4) * (⌊(5:ℝ) ^ ((1:ℝ) / 4)⌋ : ℝ)⌋ : ℝ) = 1 := by
      rw [hmul, hfl]; norm_num
    have hw : (5:ℝ) ^ ((1:ℝ) / 4) * (⌈(5:ℝ) ^ ((1:ℝ) / 4)⌉ : ℝ)
        = 2 * (5:ℝ) ^ ((1:ℝ) / 4) := by rw [hce]; push_cast; ring
    have e2 : ⌈(5:ℝ) ^ ((1:ℝ) / 4) * (⌈(5:ℝ) ^ ((1:ℝ) / 4)⌉ : ℝ)⌉ = 3 := by
      have h1 : ⌈(5:ℝ) ^ ((1:ℝ) / 4) * (⌈(5:ℝ) ^ ((1:ℝ) / 4)⌉ : ℝ)⌉ ≤ 3 := by
        rw [Int.ceil_le, hw]; push_cast; linarith
      have h2 : (2:ℤ) < ⌈(5:ℝ) ^ ((1:ℝ) / 4) * (⌈(5:ℝ) ^ ((1:ℝ) / 4)⌉ : ℝ)⌉ := by
        rw [Int.lt_ceil, hw]; push_cast; linarith
      omega
    rw [e1, e2, hy4]
    norm_num
```
