# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `2 August 2026`\
Line count: `158`\
Turn count: `2`

## Note

The conversation contained 1 "Continue" message not included in the turn count.

## Solution

```lean4
import Mathlib

theorem ceil_floor_eq_solutions (x : ℝ) (hx : 0 < x) :
    x ^ ⌈x⌉ = (⌈x⌉ : ℝ) ^ ⌊x⌋ + 1 ↔ x = Real.sqrt 3 ∨ x = (10 : ℝ) ^ (1 / 3 : ℝ) := by
  constructor
  · intro heq
    have hfc : ⌊x⌋ ≤ ⌈x⌉ := by
      have h1 : (⌊x⌋:ℝ) ≤ x := Int.floor_le x
      have h2 : x ≤ (⌈x⌉:ℝ) := Int.le_ceil x
      exact_mod_cast h1.trans h2
    have hcf1 : ⌈x⌉ ≤ ⌊x⌋ + 1 := by
      apply Int.ceil_le.mpr
      push_cast
      exact (Int.lt_floor_add_one x).le
    rcases (show ⌈x⌉ = ⌊x⌋ ∨ ⌈x⌉ = ⌊x⌋ + 1 by omega) with hcase | hcase
    · exfalso
      have hcast : (⌈x⌉:ℝ) = (⌊x⌋:ℝ) := by exact_mod_cast hcase
      have h1 : (⌊x⌋:ℝ) ≤ x := Int.floor_le x
      have h2 : x ≤ (⌈x⌉:ℝ) := Int.le_ceil x
      rw [hcast] at h2
      have hxeq : x = (⌊x⌋:ℝ) := le_antisymm h2 h1
      have hpoweq : x ^ ⌊x⌋ = (⌊x⌋:ℝ) ^ ⌊x⌋ := congrArg (· ^ (⌊x⌋:ℤ)) hxeq
      rw [hcase, hpoweq] at heq
      linarith
    · have hxgt : (⌊x⌋:ℝ) < x := by
        rcases (Int.floor_le x).lt_or_eq with h | h
        · exact h
        · exfalso
          have hxeq2 : x = (⌊x⌋:ℝ) := h.symm
          have hceil_eq2 : ⌈x⌉ = ⌈(⌊x⌋:ℝ)⌉ := congrArg Int.ceil hxeq2
          have hceil_int : ⌈(⌊x⌋:ℝ)⌉ = ⌊x⌋ := by
            have h1 : ((⌊x⌋:ℤ):ℝ) - 1 < (⌊x⌋:ℝ) := by linarith
            have h2 : (⌊x⌋:ℝ) ≤ ((⌊x⌋:ℤ):ℝ) := le_refl _
            exact Int.ceil_eq_iff.mpr ⟨h1, h2⟩
          rw [hceil_int] at hceil_eq2
          omega
      have hxlt : x < (⌊x⌋:ℝ) + 1 := Int.lt_floor_add_one x
      have hf0 : 0 ≤ ⌊x⌋ := Int.le_floor.mpr (by exact_mod_cast hx.le)
      obtain ⟨m, hmf⟩ : ∃ m : ℕ, (m:ℤ) = ⌊x⌋ := ⟨⌊x⌋.toNat, Int.toNat_of_nonneg hf0⟩
      have hmR : (m:ℝ) = (⌊x⌋:ℝ) := by exact_mod_cast hmf
      have hmlt : (m:ℝ) < x := by rw [hmR]; exact hxgt
      have hmlt1 : x < (m:ℝ) + 1 := by rw [hmR]; exact hxlt
      have hceil_eq_nat : ⌈x⌉ = ((m+1 : ℕ):ℤ) := by
        rw [hcase, ← hmf]; push_cast; ring
      have e1 : x ^ ⌈x⌉ = x ^ (m+1) := by rw [hceil_eq_nat, zpow_natCast]
      have e2 : (⌈x⌉:ℝ) ^ ⌊x⌋ = ((m:ℝ)+1) ^ m := by
        rw [← hmf, zpow_natCast, hceil_eq_nat]
        push_cast
        ring
      rw [e1, e2] at heq
      by_cases hm2 : m ≤ 2
      · interval_cases m
        · exfalso
          norm_num at heq hmlt1
          linarith
        · norm_num at heq
          left
          have hx0 : 0 ≤ x := hx.le
          have h3 : Real.sqrt (x ^ 2) = Real.sqrt 3 := by rw [heq]
          rwa [Real.sqrt_sq hx0] at h3
        · norm_num at heq
          right
          have hx0 : 0 ≤ x := hx.le
          have hstep : x ^ (3:ℝ) = 10 := by
            have h' : x ^ ((3:ℕ):ℝ) = 10 := by rw [Real.rpow_natCast]; exact heq
            simpa using h'
          have hfin : (x ^ (3:ℝ)) ^ (1/3:ℝ) = (10:ℝ) ^ (1/3:ℝ) := by rw [hstep]
          have hlhs : (x ^ (3:ℝ)) ^ (1/3:ℝ) = x ^ ((3:ℝ) * (1/3:ℝ)) :=
            (Real.rpow_mul hx0 3 (1/3)).symm
          rw [hlhs] at hfin
          have h31 : (3:ℝ) * (1/3:ℝ) = 1 := by norm_num
          rw [h31, Real.rpow_one] at hfin
          exact hfin
      · push_neg at hm2
        exfalso
        have hm3 : 3 ≤ m := by omega
        have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
        have hmne : (m:ℝ) ≠ 0 := ne_of_gt hm0
        have hstep1 : (1 + 1/(m:ℝ)) ≤ Real.exp (1/(m:ℝ)) := by
          have := Real.add_one_le_exp (1/(m:ℝ))
          linarith
        have hstep2 : (1 + 1/(m:ℝ))^m ≤ (Real.exp (1/(m:ℝ)))^m :=
          pow_le_pow_left₀ (by positivity) hstep1 m
        have hstep3 : (Real.exp (1/(m:ℝ)))^m = Real.exp 1 := by
          rw [← Real.exp_nat_mul]
          congr 1
          rw [mul_one_div, div_self hmne]
        have hstep4 : (1 + 1/(m:ℝ))^m ≤ Real.exp 1 := by rw [← hstep3]; exact hstep2
        have hexp_lt3 : Real.exp 1 < 3 := by
          have := Real.exp_one_lt_d9
          linarith
        have hm_ge3 : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm3
        have hstep5 : (1 + 1/(m:ℝ))^m < (m:ℝ) := by linarith
        have hmpow_pos : (0:ℝ) < (m:ℝ)^m := by positivity
        have hstep6 : (1 + 1/(m:ℝ))^m * (m:ℝ)^m < (m:ℝ) * (m:ℝ)^m :=
          mul_lt_mul_of_pos_right hstep5 hmpow_pos
        have hbase : (1 + 1/(m:ℝ)) * (m:ℝ) = (m:ℝ) + 1 := by
          rw [add_mul, one_mul, one_div, inv_mul_cancel₀ hmne]
        have heq7 : (1 + 1/(m:ℝ))^m * (m:ℝ)^m = ((m:ℝ)+1)^m := by
          rw [← mul_pow, hbase]
        have heq8 : (m:ℝ) * (m:ℝ)^m = (m:ℝ)^(m+1) := by
          rw [pow_succ]; ring
        rw [heq7, heq8] at hstep6
        have hnat_lt : (m+1)^m < m^(m+1) := by
          have hcast2 : (((m+1)^m : ℕ) : ℝ) < ((m^(m+1) : ℕ) : ℝ) := by
            push_cast
            exact hstep6
          exact_mod_cast hcast2
        have h1 : (m+1)^m + 1 ≤ m^(m+1) := by omega
        have hreal_le : ((m:ℝ)+1)^m + 1 ≤ (m:ℝ)^(m+1) := by exact_mod_cast h1
        have hxpow : (m:ℝ)^(m+1) < x^(m+1) := by
          have hne : m + 1 ≠ 0 := by omega
          exact pow_lt_pow_left₀ hmlt (by positivity) hne
        linarith [heq, hreal_le, hxpow]
  · rintro (rfl | rfl)
    · have hs2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have hsnn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
      have hs1 : 1 < Real.sqrt 3 := by nlinarith
      have hs2' : Real.sqrt 3 < 2 := by nlinarith
      have hfloor : ⌊Real.sqrt 3⌋ = ((1:ℕ):ℤ) := by
        have h1 : (((1:ℕ):ℤ):ℝ) ≤ Real.sqrt 3 := by push_cast; linarith
        have h2 : Real.sqrt 3 < (((1:ℕ):ℤ):ℝ) + 1 := by push_cast; linarith
        exact Int.floor_eq_iff.mpr ⟨h1, h2⟩
      have hceil : ⌈Real.sqrt 3⌉ = ((2:ℕ):ℤ) := by
        have h1 : (((2:ℕ):ℤ):ℝ) - 1 < Real.sqrt 3 := by push_cast; linarith
        have h2 : Real.sqrt 3 ≤ (((2:ℕ):ℤ):ℝ) := by push_cast; linarith
        exact Int.ceil_eq_iff.mpr ⟨h1, h2⟩
      rw [hfloor, hceil, zpow_natCast, zpow_natCast]
      push_cast
      norm_num [hs2]
    · have hypos : 0 < (10:ℝ) ^ (1/3:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      have step : (1/3:ℝ) * ((3:ℕ):ℝ) = 1 := by push_cast; norm_num
      have hy_cube : ((10:ℝ) ^ (1/3:ℝ)) ^ (3:ℕ) = 10 := by
        rw [← Real.rpow_natCast ((10:ℝ) ^ (1/3:ℝ)) 3,
            ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10), step, Real.rpow_one]
      have hy2 : 2 < (10:ℝ) ^ (1/3:ℝ) := by
        by_contra h
        push_neg at h
        have hle : ((10:ℝ) ^ (1/3:ℝ)) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hypos.le h 3
        norm_num at hle
        linarith [hy_cube]
      have hy3 : (10:ℝ) ^ (1/3:ℝ) < 3 := by
        by_contra h
        push_neg at h
        have hle : (3:ℝ) ^ 3 ≤ ((10:ℝ) ^ (1/3:ℝ)) ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
        norm_num at hle
        linarith [hy_cube]
      have hfloor : ⌊(10:ℝ) ^ (1/3:ℝ)⌋ = ((2:ℕ):ℤ) := by
        have h1 : (((2:ℕ):ℤ):ℝ) ≤ (10:ℝ) ^ (1/3:ℝ) := by push_cast; linarith
        have h2 : (10:ℝ) ^ (1/3:ℝ) < (((2:ℕ):ℤ):ℝ) + 1 := by push_cast; linarith
        exact Int.floor_eq_iff.mpr ⟨h1, h2⟩
      have hceil : ⌈(10:ℝ) ^ (1/3:ℝ)⌉ = ((3:ℕ):ℤ) := by
        have h1 : (((3:ℕ):ℤ):ℝ) - 1 < (10:ℝ) ^ (1/3:ℝ) := by push_cast; linarith
        have h2 : (10:ℝ) ^ (1/3:ℝ) ≤ (((3:ℕ):ℤ):ℝ) := by push_cast; linarith
        exact Int.ceil_eq_iff.mpr ⟨h1, h2⟩
      rw [hfloor, hceil, zpow_natCast, zpow_natCast]
      push_cast
      norm_num [hy_cube]
```
