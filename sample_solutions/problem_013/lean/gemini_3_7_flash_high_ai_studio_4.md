# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `29 August 2026`\
Line count: `125`\
Turn count: `7`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

private lemma nat_pow_lt (n : ℕ) (h : 3 ≤ n) : (n + 1) ^ n < n ^ (n + 1) := by
  induction' n, h using Nat.le_induction with n hn ih
  · decide
  · have h1 : (n * (n + 2)) ^ (n + 1) < ((n + 1) ^ 2) ^ (n + 1) :=
      Nat.pow_lt_pow_left (by nlinarith) (by omega)
    rw [mul_pow] at h1
    have h2 : (n + 2) ^ (n + 1) * (n + 1) ^ n < (n + 1) ^ (n + 2) * (n + 1) ^ n := by
      calc (n + 2) ^ (n + 1) * (n + 1) ^ n
        _ < (n + 2) ^ (n + 1) * n ^ (n + 1) := Nat.mul_lt_mul_of_pos_left ih (by positivity)
        _ = n ^ (n + 1) * (n + 2) ^ (n + 1) := by ring
        _ < ((n + 1) ^ 2) ^ (n + 1) := h1
        _ = (n + 1) ^ (n + 2) * (n + 1) ^ n := by
          rw [← pow_mul, ← pow_add]
          congr 1; omega
    exact Nat.lt_of_mul_lt_mul_right h2

theorem ceil_floor_eq_solutions (x : ℝ) (hx : 0 < x) :
    x ^ ⌈x⌉ = (⌈x⌉ : ℝ) ^ ⌊x⌋ + 1 ↔ x = Real.sqrt 3 ∨ x = (10 : ℝ) ^ (1 / 3 : ℝ) := by
  constructor
  · intro h
    have h_ge : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr (le_of_lt hx)
    have h_cases : ⌈x⌉ = ⌊x⌋ ∨ ⌈x⌉ = ⌊x⌋ + 1 := by
      have : ⌊x⌋ ≤ ⌈x⌉ := Int.floor_le_ceil x
      have : ⌈x⌉ ≤ ⌊x⌋ + 1 := Int.ceil_le_floor_add_one x
      omega
    rcases h_cases with h_int | h_nint
    · have hx_eq : x = (⌈x⌉ : ℝ) := by
        have : (⌊x⌋ : ℝ) ≤ x ∧ x ≤ (⌈x⌉ : ℝ) := ⟨Int.floor_le x, Int.le_ceil x⟩
        have : (⌈x⌉ : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast h_int
        linarith
      have h_contra := h
      rw [hx_eq, Int.ceil_intCast, Int.floor_intCast] at h_contra
      linarith
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌊x⌋ = (n : ℤ) := ⟨⌊x⌋.toNat, (Int.toNat_of_nonneg h_ge).symm⟩
      have hc : ⌈x⌉ = (n + 1 : ℤ) := by omega
      have h_lt : (n : ℝ) < x := by
        have h1 : (n : ℝ) ≤ x := by
          have := Int.floor_le x
          rw [hn] at this
          exact this
        have h2 : x ≠ (n : ℝ) := by
          intro h_eq
          have : ⌈x⌉ = (n : ℤ) := by rw [h_eq, Int.ceil_natCast]
          omega
        exact lt_of_le_of_ne h1 h2.symm
      have h_gt : x < (n : ℝ) + 1 := by
        have := Int.lt_floor_add_one x
        rw [hn] at this
        exact this
      have h_eq : x ^ (n + 1) = (n + 1 : ℝ) ^ n + 1 := by
        have h1 : x ^ ⌈x⌉ = x ^ (n + 1) := by
          rw [hc, show (n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) by rfl, zpow_natCast]
        have h2 : (⌈x⌉ : ℝ) ^ ⌊x⌋ = (n + 1 : ℝ) ^ n := by
          rw [hc, hn, show (n : ℤ) = ((n : ℕ) : ℤ) by rfl, zpow_natCast]
          push_cast
          rfl
        rw [h1, h2] at h
        exact h
      rcases lt_or_ge n 3 with hn3 | hn3
      · interval_cases n
        · exfalso
          norm_num at h_eq h_gt
          linarith
        · left
          norm_num at h_eq
          rw [← Real.sqrt_sq (le_of_lt hx), h_eq]
        · right
          norm_num at h_eq
          rw [← h_eq, ← Real.rpow_natCast x 3, ← Real.rpow_mul (le_of_lt hx)]
          have : ((3 : ℕ) : ℝ) * (1 / 3 : ℝ) = 1 := by norm_num
          rw [this, Real.rpow_one]
      · exfalso
        have hpow : (n : ℝ) ^ (n + 1) < x ^ (n + 1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast]
          exact Real.rpow_lt_rpow (by positivity) h_lt (by positivity)
        have hnat : (n + 1 : ℝ) ^ n + 1 ≤ (n : ℝ) ^ (n + 1) := by
          have hlt := nat_pow_lt n hn3
          have : (n + 1) ^ n + 1 ≤ n ^ (n + 1) := hlt
          exact_mod_cast this
        linarith [h_eq]
  · rintro (rfl | rfl)
    · have hf : ⌊Real.sqrt 3⌋ = 1 := by
        rw [Int.floor_eq_iff]
        exact ⟨Real.le_sqrt (by norm_num) (by norm_num) |>.mpr (by norm_num),
               Real.sqrt_lt (by norm_num) (by norm_num) |>.mpr (by norm_num)⟩
      have hc : ⌈Real.sqrt 3⌉ = 2 := by
        rw [Int.ceil_eq_iff]
        exact ⟨Real.lt_sqrt (by norm_num) |>.mpr (by norm_num),
               Real.sqrt_le_left (by norm_num) |>.mpr (by norm_num)⟩
      rw [hf, hc]
      have hz2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
      have hz1 : (1 : ℤ) = ((1 : ℕ) : ℤ) := rfl
      rw [hz2, hz1, zpow_natCast, zpow_natCast]
      push_cast
      rw [sq, Real.mul_self_sqrt (by norm_num)]
      norm_num
    · have h8 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
        have : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
        rw [this, ← Real.rpow_mul (by norm_num)]
        norm_num
      have h27 : (27 : ℝ) ^ (1 / 3 : ℝ) = 3 := by
        have : (27 : ℝ) = (3 : ℝ) ^ (3 : ℝ) := by norm_num
        rw [this, ← Real.rpow_mul (by norm_num)]
        norm_num
      have h_lt : (2 : ℝ) < (10 : ℝ) ^ (1 / 3 : ℝ) := by
        have := Real.rpow_lt_rpow (by norm_num) (show (8 : ℝ) < 10 by norm_num) (show 0 < (1 / 3 : ℝ) by norm_num)
        rwa [h8] at this
      have h_gt : (10 : ℝ) ^ (1 / 3 : ℝ) < 3 := by
        have := Real.rpow_lt_rpow (by norm_num) (show (10 : ℝ) < 27 by norm_num) (show 0 < (1 / 3 : ℝ) by norm_num)
        rwa [h27] at this
      have hf : ⌊(10 : ℝ) ^ (1 / 3 : ℝ)⌋ = 2 := by
        rw [Int.floor_eq_iff]
        exact ⟨le_of_lt h_lt, by linarith⟩
      have hc : ⌈(10 : ℝ) ^ (1 / 3 : ℝ)⌉ = 3 := by
        rw [Int.ceil_eq_iff]
        exact ⟨by linarith, le_of_lt h_gt⟩
      rw [hf, hc]
      have hz3 : (3 : ℤ) = ((3 : ℕ) : ℤ) := rfl
      have hz2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
      rw [hz3, hz2, zpow_natCast, zpow_natCast]
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
```
