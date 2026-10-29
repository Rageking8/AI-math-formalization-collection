# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `29 August 2026`\
Line count: `170`\
Turn count: `5`

## Solution

```lean4
import Mathlib

lemma nat_pow_succ_lt_pow (k : ℕ) (hk : 3 ≤ k) : (k + 1) ^ k < k ^ (k + 1) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have h_le : m * (m + 2) ≤ (m + 1) ^ 2 := by
      have : m * (m + 2) + 1 = (m + 1) ^ 2 := by ring
      omega
    have h_pow : (m * (m + 2)) ^ (m + 1) ≤ ((m + 1) ^ 2) ^ (m + 1) :=
      Nat.pow_le_pow_left h_le (m + 1)
    rw [Nat.mul_pow, ← pow_mul] at h_pow
    have h_pos : 0 < (m + 2) ^ (m + 1) := by positivity
    have h_lt : (m + 1) ^ m * (m + 2) ^ (m + 1) < m ^ (m + 1) * (m + 2) ^ (m + 1) :=
      Nat.mul_lt_mul_of_pos_right ih h_pos
    have h_comb : (m + 1) ^ m * (m + 2) ^ (m + 1) < (m + 1) ^ (2 * (m + 1)) :=
      lt_of_lt_of_le h_lt h_pow
    have h_decomp : (m + 1) ^ (2 * (m + 1)) = (m + 1) ^ m * (m + 1) ^ (m + 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h_decomp] at h_comb
    exact (mul_lt_mul_iff_of_pos_left (by positivity)).1 h_comb

lemma real_pow_lt_pow_succ (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (n : ℕ) :
    a ^ (n + 1) < b ^ (n + 1) := by
  induction n with
  | zero =>
    rw [pow_one, pow_one]
    exact hab
  | succ m ih =>
    rw [pow_succ a (m + 1), pow_succ b (m + 1)]
    have ha_pos : 0 ≤ a ^ (m + 1) := by positivity
    have hb_pos : 0 < b := by linarith
    have : 0 < b ^ (m + 1) := by positivity
    nlinarith

theorem ceil_floor_eq_solutions (x : ℝ) (hx : 0 < x) :
    x ^ ⌈x⌉ = (⌈x⌉ : ℝ) ^ ⌊x⌋ + 1 ↔ x = Real.sqrt 3 ∨ x = (10 : ℝ) ^ (1 / 3 : ℝ) := by
  constructor
  · intro h
    have h_cases : ⌈x⌉ = ⌊x⌋ ∨ ⌈x⌉ = ⌊x⌋ + 1 := by
      have h1 : ⌊x⌋ ≤ ⌈x⌉ := by
        have : (⌊x⌋ : ℝ) ≤ ⌈x⌉ := (Int.floor_le x).trans (Int.le_ceil x)
        exact_mod_cast this
      have h2 : ⌈x⌉ ≤ ⌊x⌋ + 1 := Int.ceil_le_floor_add_one x
      omega
    rcases h_cases with h_eq | h_succ
    · exfalso
      have h_x : x = (⌊x⌋ : ℝ) := by
        have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
        have h2 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
        rw [h_eq] at h2
        linarith
      have h_sub : x ^ ⌈x⌉ - (⌈x⌉ : ℝ) ^ ⌊x⌋ = 1 := by linarith [h]
      rw [h_eq, ← h_x] at h_sub
      linarith
    · have hfloor_nonneg : 0 ≤ ⌊x⌋ := Int.floor_nonneg.2 (le_of_lt hx)
      obtain ⟨k, hk⟩ : ∃ k : ℕ, ⌊x⌋ = (k : ℤ) := ⟨⌊x⌋.toNat, (Int.toNat_of_nonneg hfloor_nonneg).symm⟩
      have hceil_val : ⌈x⌉ = (k + 1 : ℤ) := by omega
      have hx_ge : (k : ℝ) ≤ x := by
        have : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
        rw [hk] at this
        exact this
      have hx_strict_low : (k : ℝ) < x := by
        apply lt_of_le_of_ne hx_ge
        rintro rfl
        have : ⌈(k : ℝ)⌉ = (k : ℤ) := Int.ceil_natCast k
        omega
      have hx_strict_up : x < (k : ℝ) + 1 := by
        have hlt := Int.lt_floor_add_one x
        rw [hk] at hlt
        push_cast at hlt ⊢
        exact hlt
      have h_eq : x ^ (k + 1) = (k + 1 : ℝ) ^ k + 1 := by
        have h_pow1 : x ^ ⌈x⌉ = x ^ (k + 1) := by
          rw [hceil_val]
          exact zpow_natCast x (k + 1)
        have h_pow2 : (⌈x⌉ : ℝ) ^ ⌊x⌋ = (k + 1 : ℝ) ^ k := by
          rw [hceil_val, hk]
          push_cast
          exact zpow_natCast (k + 1 : ℝ) k
        linarith [h, h_pow1, h_pow2]
      rcases lt_or_ge k 3 with hk_lt | hk_ge
      · interval_cases k
        · -- k = 0
          have h0 := h_eq
          norm_num at h0 hx_strict_up
          linarith [hx_strict_up, h0]
        · -- k = 1
          left
          have h1 := h_eq
          norm_num at h1
          have hx_pos : 0 ≤ x := le_of_lt hx
          rw [← Real.sqrt_sq hx_pos, h1]
        · -- k = 2
          right
          have h2 := h_eq
          norm_num at h2
          have h3 : (3 : ℝ) ≠ 0 := by norm_num
          have hx_rpow : (x ^ (3 : ℝ)) ^ (1 / 3 : ℝ) = x := by
            rw [← Real.rpow_mul (le_of_lt hx), mul_one_div_cancel h3, Real.rpow_one]
          have h_x3_rpow : x ^ (3 : ℝ) = 10 := by
            have : x ^ (3 : ℝ) = x ^ (3 : ℕ) := Real.rpow_natCast x 3
            rw [this, h2]
          rw [← hx_rpow, h_x3_rpow]
      · -- k ≥ 3
        exfalso
        have h_lower : (k : ℝ) ^ (k + 1) < x ^ (k + 1) :=
          real_pow_lt_pow_succ (k : ℝ) x (by positivity) hx_strict_low k
        have h_upper_nat : (k + 1) ^ k < k ^ (k + 1) := nat_pow_succ_lt_pow k hk_ge
        have h_upper : (k + 1 : ℝ) ^ k + 1 ≤ (k : ℝ) ^ (k + 1) := by
          exact_mod_cast h_upper_nat
        linarith [h_eq, h_lower, h_upper]
  · rintro (rfl | rfl)
    · -- x = Real.sqrt 3
      have h1 : (1 : ℝ) < Real.sqrt 3 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h2 : Real.sqrt 3 < 2 := by
        have : (2 : ℝ) = Real.sqrt 4 := by norm_num
        rw [this]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have hfloor : ⌊Real.sqrt 3⌋ = 1 := by
        rw [Int.floor_eq_iff]
        push_cast
        constructor <;> linarith
      have hceil : ⌈Real.sqrt 3⌉ = 2 := by
        rw [Int.ceil_eq_iff]
        push_cast
        constructor <;> linarith
      rw [hfloor, hceil]
      have hsq : (Real.sqrt 3) ^ (2 : ℤ) = 3 := by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, sq, Real.mul_self_sqrt (by norm_num)]
      rw [hsq]
      norm_num
    · -- x = 10 ^ (1/3)
      have h_pos : (0 : ℝ) < 10 := by norm_num
      have h2 : (2 : ℝ) < (10 : ℝ) ^ (1 / 3 : ℝ) := by
        have h_rpow : (8 : ℝ) ^ (1 / 3 : ℝ) < (10 : ℝ) ^ (1 / 3 : ℝ) :=
          Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
        have h8 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
          have : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
          rw [this, ← Real.rpow_mul (by norm_num)]
          norm_num
        linarith [h_rpow, h8]
      have h3 : (10 : ℝ) ^ (1 / 3 : ℝ) < 3 := by
        have h_rpow : (10 : ℝ) ^ (1 / 3 : ℝ) < (27 : ℝ) ^ (1 / 3 : ℝ) :=
          Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
        have h27 : (27 : ℝ) ^ (1 / 3 : ℝ) = 3 := by
          have : (27 : ℝ) = (3 : ℝ) ^ (3 : ℝ) := by norm_num
          rw [this, ← Real.rpow_mul (by norm_num)]
          norm_num
        linarith [h_rpow, h27]
      have hfloor : ⌊(10 : ℝ) ^ (1 / 3 : ℝ)⌋ = 2 := by
        rw [Int.floor_eq_iff]
        push_cast
        constructor <;> linarith
      have hceil : ⌈(10 : ℝ) ^ (1 / 3 : ℝ)⌉ = 3 := by
        rw [Int.ceil_eq_iff]
        push_cast
        constructor <;> linarith
      rw [hfloor, hceil]
      have hlhs : ((10 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℤ) = 10 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast]
        rw [show ((10 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = ((10 : ℝ) ^ (1 / 3 : ℝ)) ^ ((3 : ℕ) : ℝ) from (Real.rpow_natCast _ 3).symm]
        rw [← Real.rpow_mul (le_of_lt h_pos)]
        norm_num
      rw [hlhs]
      norm_num
```
