# Claude Opus 5.5 High (Claude AI)

Model: `Claude Opus 5.5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `106`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem ceil_floor_eq_solutions (x : ℝ) (hx : 0 < x) :
    x ^ ⌈x⌉ = (⌈x⌉ : ℝ) ^ ⌊x⌋ + 1 ↔ x = Real.sqrt 3 ∨ x = (10 : ℝ) ^ (1 / 3 : ℝ) := by
  have h10 : ((10:ℝ) ^ (1/3:ℝ)) ^ (3:ℕ) = 10 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h10pos : (0:ℝ) < (10:ℝ) ^ (1/3:ℝ) := by positivity
  have h10gt : (2:ℝ) < (10:ℝ) ^ (1/3:ℝ) := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonneg (mul_nonneg h10pos.le h10pos.le) (sub_nonneg.mpr h),
      mul_nonneg h10pos.le (sub_nonneg.mpr h)]
  have h10lt : (10:ℝ) ^ (1/3:ℝ) < 3 := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonneg (mul_nonneg h10pos.le h10pos.le) (sub_nonneg.mpr h),
      mul_nonneg h10pos.le (sub_nonneg.mpr h)]
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1 < Real.sqrt 3 := by nlinarith
  have hs2 : Real.sqrt 3 < 2 := by nlinarith
  constructor
  · intro h
    have key : ∀ n : ℕ, 3 ≤ n → ((n:ℝ)+1)^n < (n:ℝ)^(n+1) := by
      intro n hn
      have hnr : (3:ℝ) ≤ n := by exact_mod_cast hn
      have hnpos : (0:ℝ) < n := by linarith
      have hn0 : (n:ℝ) ≠ 0 := hnpos.ne'
      have h1 : (n:ℝ) + 1 = n * (1 + 1/n) := by field_simp <;> ring
      have h2 : (1 + 1/(n:ℝ)) ^ n ≤ Real.exp 1 := by
        have h3 : 1 + 1/(n:ℝ) ≤ Real.exp (1/n) := by
          linarith [Real.add_one_le_exp (1/(n:ℝ))]
        calc (1 + 1/(n:ℝ))^n ≤ Real.exp (1/n) ^ n := by gcongr
          _ = Real.exp 1 := by
            rw [← Real.exp_nat_mul]
            congr 1
            field_simp
      have h4 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      rw [h1, mul_pow, pow_succ]
      have : (0:ℝ) < (n:ℝ)^n := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 this.le, mul_lt_mul_of_pos_left h4 this,
        mul_le_mul_of_nonneg_left hnr this.le]
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Int.floor_nonneg.mpr hx.le)
    have hfl : (n:ℝ) ≤ x := by
      have := Int.floor_le x
      rw [hn] at this
      exact_mod_cast this
    have hfu : x < (n:ℝ) + 1 := by
      have := Int.lt_floor_add_one x
      rw [hn] at this
      exact_mod_cast this
    by_cases hxn : x = n
    · exfalso
      have hc : ⌈x⌉ = (n:ℤ) := by
        rw [hxn]; exact Int.ceil_natCast n
      rw [hc, hn, zpow_natCast, zpow_natCast, hxn] at h
      push_cast at h
      linarith
    · have hlt : (n:ℝ) < x := lt_of_le_of_ne hfl (Ne.symm hxn)
      have hc : ⌈x⌉ = ((n+1 : ℕ) : ℤ) := by
        rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
      rw [hc, hn, zpow_natCast, zpow_natCast] at h
      push_cast at h
      rcases Nat.lt_or_ge n 3 with hn3 | hn3
      · interval_cases n
        · exfalso
          norm_num at h hfu
          linarith
        · left
          have h' : x^2 = 3 := by norm_num at h; linarith
          rw [← h', Real.sqrt_sq hx.le]
        · right
          have h' : x^3 = 10 := by norm_num at h; linarith
          rcases lt_trichotomy x ((10:ℝ)^(1/3:ℝ)) with hlt' | heq | hgt
          · exfalso
            nlinarith [mul_pos (mul_pos (sub_pos.mpr hlt') h10pos) h10pos,
              mul_pos (mul_pos (sub_pos.mpr hlt') hx) h10pos,
              mul_pos (mul_pos (sub_pos.mpr hlt') hx) hx]
          · exact heq
          · exfalso
            nlinarith [mul_pos (mul_pos (sub_pos.mpr hgt) h10pos) h10pos,
              mul_pos (mul_pos (sub_pos.mpr hgt) hx) h10pos,
              mul_pos (mul_pos (sub_pos.mpr hgt) hx) hx]
      · exfalso
        have hk := key n hn3
        have hk1 : (n+1)^n < n^(n+1) := by exact_mod_cast hk
        have hk2 : (n+1)^n + 1 ≤ n^(n+1) := hk1
        have hk3 : ((n:ℝ)+1)^n + 1 ≤ (n:ℝ)^(n+1) := by exact_mod_cast hk2
        have hk4 : (n:ℝ)^(n+1) < x^(n+1) := by gcongr
        linarith
  · rintro (h | h)
    · subst h
      have hf : ⌊Real.sqrt 3⌋ = 1 := by
        rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have hc : ⌈Real.sqrt 3⌉ = 2 := by
        rw [Int.ceil_eq_iff]; constructor <;> push_cast <;> linarith
      rw [hf, hc, show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast, zpow_one, hs3]
      norm_num
    · subst h
      have hf : ⌊(10:ℝ)^(1/3:ℝ)⌋ = 2 := by
        rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
      have hc : ⌈(10:ℝ)^(1/3:ℝ)⌉ = 3 := by
        rw [Int.ceil_eq_iff]; constructor <;> push_cast <;> linarith
      rw [hf, hc, show (3:ℤ) = ((3:ℕ):ℤ) by norm_num, show (2:ℤ) = ((2:ℕ):ℤ) by norm_num,
        zpow_natCast, zpow_natCast, h10]
      norm_num
```
