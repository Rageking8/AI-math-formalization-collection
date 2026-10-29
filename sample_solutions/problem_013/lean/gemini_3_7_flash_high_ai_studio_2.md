# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `29 August 2026`\
Line count: `179`\
Turn count: `3`

## Solution

```lean4
import Mathlib

lemma nat_pow_ineq : ∀ (n : ℕ), 3 ≤ n → (n + 1) ^ n < n ^ (n + 1) := by
  intro n hn
  induction' hn with k hk ih
  · decide
  · have h_base : k * (k + 2) < (k + 1) ^ 2 := by nlinarith
    have h_pow : (k * (k + 2)) ^ (k + 1) < ((k + 1) ^ 2) ^ (k + 1) :=
      Nat.pow_lt_pow_left h_base (by omega)
    have h_lhs : (k * (k + 2)) ^ (k + 1) = k ^ (k + 1) * (k + 2) ^ (k + 1) :=
      Nat.mul_pow k (k + 2) (k + 1)
    have h_rhs : ((k + 1) ^ 2) ^ (k + 1) = (k + 1) ^ (k + 2) * (k + 1) ^ k := by
      rw [← Nat.pow_mul]
      have : 2 * (k + 1) = (k + 2) + k := by omega
      rw [this, Nat.pow_add]
    have h_step : k ^ (k + 1) * (k + 2) ^ (k + 1) < (k + 1) ^ (k + 2) * (k + 1) ^ k := by
      rwa [h_lhs, h_rhs] at h_pow
    have h_ih_mul : (k + 1) ^ (k + 2) * (k + 1) ^ k < (k + 1) ^ (k + 2) * k ^ (k + 1) :=
      Nat.mul_lt_mul_of_pos_left ih (by positivity)
    have h_trans : k ^ (k + 1) * (k + 2) ^ (k + 1) < k ^ (k + 1) * (k + 1) ^ (k + 2) := by
      have : (k + 1) ^ (k + 2) * k ^ (k + 1) = k ^ (k + 1) * (k + 1) ^ (k + 2) := by ring
      rw [this] at h_ih_mul
      exact h_step.trans h_ih_mul
    by_contra! h_le
    have h_le_mul : k ^ (k + 1) * (k + 1) ^ (k + 2) ≤ k ^ (k + 1) * (k + 2) ^ (k + 1) :=
      Nat.mul_le_mul_left (k ^ (k + 1)) h_le
    omega

theorem ceil_floor_eq_solutions (x : ℝ) (hx : 0 < x) :
    x ^ ⌈x⌉ = (⌈x⌉ : ℝ) ^ ⌊x⌋ + 1 ↔ x = Real.sqrt 3 ∨ x = (10 : ℝ) ^ (1 / 3 : ℝ) := by
  constructor
  · intro H
    have h_floor_le : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have h_le_ceil : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
    have h_diff : ⌈x⌉ < ⌊x⌋ + 2 := by
      have : (⌈x⌉ : ℝ) < (⌊x⌋ : ℝ) + 2 := by
        linarith [Int.ceil_lt_add_one x, Int.lt_floor_add_one x]
      exact_mod_cast this
    have h_order : ⌊x⌋ ≤ ⌈x⌉ := by
      have : (⌊x⌋ : ℝ) ≤ (⌈x⌉ : ℝ) := by linarith
      exact_mod_cast this
    have h_cases : ⌈x⌉ = ⌊x⌋ ∨ ⌈x⌉ = ⌊x⌋ + 1 := by omega
    rcases h_cases with h_int | h_nint
    · have h_x_eq : x = (⌈x⌉ : ℝ) := by
        have : (⌈x⌉ : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast h_int
        linarith
      have h_lhs : x ^ ⌈x⌉ = (⌈x⌉ : ℝ) ^ ⌊x⌋ := by
        nth_rw 1 [h_x_eq]
        rw [h_int]
      linarith [H, h_lhs]
    · have h_fl_lt : (⌊x⌋ : ℝ) < x := by
        rcases lt_or_eq_of_le h_floor_le with hlt | heq
        · exact hlt
        · exfalso
          have : ⌈x⌉ ≤ ⌊x⌋ := by
            have : x ≤ (⌊x⌋ : ℝ) := by linarith
            exact Int.ceil_le.2 this
          omega
      have h_fl_nonneg : 0 ≤ ⌊x⌋ := by
        have : (-1 : ℝ) < (⌊x⌋ : ℝ) := by linarith [Int.lt_floor_add_one x]
        have : -1 < ⌊x⌋ := by exact_mod_cast this
        omega
      set n := ⌊x⌋.toNat with hn_def
      have hn_eq : ⌊x⌋ = (n : ℤ) := by omega
      have hc_eq : ⌈x⌉ = (n + 1 : ℤ) := by omega
      have hx_bounds : (n : ℝ) < x ∧ x < (n + 1 : ℝ) := by
        constructor
        · have : (⌊x⌋ : ℝ) = (n : ℝ) := by exact_mod_cast hn_eq
          linarith
        · have : (⌊x⌋ : ℝ) = (n : ℝ) := by exact_mod_cast hn_eq
          linarith [Int.lt_floor_add_one x]
      have H_pow : x ^ (n + 1) = (n + 1 : ℝ) ^ n + 1 := by
        have H' := H
        rw [hc_eq, hn_eq] at H'
        have h1 : x ^ (n + 1 : ℤ) = x ^ (n + 1) := zpow_natCast x (n + 1)
        have h2 : ((n + 1 : ℤ) : ℝ) ^ (n : ℤ) = (n + 1 : ℝ) ^ n := by
          push_cast
          exact zpow_natCast (n + 1 : ℝ) n
        rwa [h1, h2] at H'
      rcases n with _ | n
      · have H_0 : x = 2 := by
          have h_pow0 : x ^ (0 + 1) = (0 + 1 : ℝ) ^ 0 + 1 := H_pow
          norm_num at h_pow0
          exact h_pow0
        have hx_lt1 : x < 1 := by
          have : (⌊x⌋ : ℝ) = 0 := by exact_mod_cast hn_eq
          linarith [Int.lt_floor_add_one x]
        linarith
      · rcases n with _ | n
        · have H_1 : x ^ 2 = 3 := by
            have h_pow1 := H_pow
            norm_num at h_pow1
            exact h_pow1
          have h_sqrt : Real.sqrt (x ^ 2) = Real.sqrt 3 := by rw [H_1]
          rw [Real.sqrt_sq hx.le] at h_sqrt
          exact Or.inl h_sqrt
        · rcases n with _ | n
          · have H_2 : x ^ 3 = 10 := by
              have h_pow2 := H_pow
              norm_num at h_pow2
              exact h_pow2
            have hx_rpow : x ^ (3 : ℝ) = 10 := by
              have : x ^ (3 : ℝ) = x ^ 3 := Real.rpow_natCast x 3
              rw [this, H_2]
            have h_root : (x ^ (3 : ℝ)) ^ (1 / 3 : ℝ) = (10 : ℝ) ^ (1 / 3 : ℝ) := by
              rw [hx_rpow]
            rw [← Real.rpow_mul hx.le] at h_root
            have h_mul : (3 : ℝ) * (1 / 3 : ℝ) = 1 := by norm_num
            rw [h_mul, Real.rpow_one] at h_root
            exact Or.inr h_root
          · set k := n + 3
            have hk_le : 3 ≤ k := by omega
            have h_lt : (k : ℝ) < x := by
              have : (⌊x⌋ : ℝ) = (k : ℝ) := by exact_mod_cast hn_eq
              linarith [h_fl_lt]
            have h_pow_lt : (k : ℝ) ^ (k + 1) < x ^ (k + 1) := by
              have : (0 : ℝ) ≤ (k : ℝ) := by positivity
              gcongr
            have H_k : x ^ (k + 1) = (k + 1 : ℝ) ^ k + 1 := H_pow
            rw [H_k] at h_pow_lt
            have h_nat : k ^ (k + 1) < (k + 1) ^ k + 1 := by
              exact_mod_cast h_pow_lt
            have h_ineq := nat_pow_ineq k hk_le
            omega
  · rintro (rfl | rfl)
    · have h1 : (1 : ℝ) < Real.sqrt 3 := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      have h2 : Real.sqrt 3 < 2 := by
        rw [Real.sqrt_lt (by norm_num) (by norm_num)]
        norm_num
      have hfloor : ⌊Real.sqrt 3⌋ = 1 := by
        rw [Int.floor_eq_iff]
        constructor <;> { push_cast; linarith }
      have hceil : ⌈Real.sqrt 3⌉ = 2 := by
        rw [Int.ceil_eq_iff]
        constructor <;> { push_cast; linarith }
      rw [hfloor, hceil]
      have h_sq : (Real.sqrt 3) ^ (2 : ℤ) = 3 := by
        have : (Real.sqrt 3) ^ (2 : ℤ) = (Real.sqrt 3) ^ (2 : ℕ) := zpow_ofNat (Real.sqrt 3) 2
        rw [this, sq, Real.mul_self_sqrt (by norm_num)]
      rw [h_sq]
      norm_num
    · have h8 : (2 : ℝ) = (8 : ℝ) ^ (1 / 3 : ℝ) := by
        have : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
        rw [this, ← Real.rpow_mul (by norm_num)]
        have : (3 : ℝ) * (1 / 3 : ℝ) = 1 := by norm_num
        rw [this, Real.rpow_one]
      have h_low : (2 : ℝ) < (10 : ℝ) ^ (1 / 3 : ℝ) := by
        calc (2 : ℝ) = (8 : ℝ) ^ (1 / 3 : ℝ) := h8
        _ < (10 : ℝ) ^ (1 / 3 : ℝ) :=
          Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
      have h27 : (3 : ℝ) = (27 : ℝ) ^ (1 / 3 : ℝ) := by
        have : (27 : ℝ) = (3 : ℝ) ^ (3 : ℝ) := by norm_num
        rw [this, ← Real.rpow_mul (by norm_num)]
        have : (3 : ℝ) * (1 / 3 : ℝ) = 1 := by norm_num
        rw [this, Real.rpow_one]
      have h_high : (10 : ℝ) ^ (1 / 3 : ℝ) < 3 := by
        calc (10 : ℝ) ^ (1 / 3 : ℝ) < (27 : ℝ) ^ (1 / 3 : ℝ) :=
          Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
        _ = 3 := h27.symm
      have hfloor : ⌊(10 : ℝ) ^ (1 / 3 : ℝ)⌋ = 2 := by
        rw [Int.floor_eq_iff]
        constructor <;> { push_cast; linarith }
      have hceil : ⌈(10 : ℝ) ^ (1 / 3 : ℝ)⌉ = 3 := by
        rw [Int.ceil_eq_iff]
        constructor <;> { push_cast; linarith }
      rw [hfloor, hceil]
      have h_pow3 : ((10 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℤ) = 10 := by
        have : ((10 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℤ) = ((10 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) :=
          zpow_ofNat _ 3
        rw [this]
        have : ((10 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = ((10 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℝ) :=
          (Real.rpow_natCast _ 3).symm
        rw [this, ← Real.rpow_mul (by norm_num)]
        have : (1 / 3 : ℝ) * (3 : ℝ) = 1 := by norm_num
        rw [this, Real.rpow_one]
      rw [h_pow3]
      norm_num
```
