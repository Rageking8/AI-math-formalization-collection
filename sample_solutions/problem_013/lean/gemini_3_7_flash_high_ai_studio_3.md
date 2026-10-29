# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `29 August 2026`\
Line count: `109`\
Turn count: `6`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

lemma pow_succ_lt {k : ℕ} (hk : 3 ≤ k) : (k + 1) ^ k < k ^ (k + 1) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h1 : (n + 2) * n < (n + 1) ^ 2 := by nlinarith
    have h2 : ((n + 2) * n) ^ (n + 1) < ((n + 1) ^ 2) ^ (n + 1) :=
      Nat.pow_lt_pow_left h1 (by omega)
    rw [Nat.mul_pow, ← Nat.pow_mul, mul_comm 2, Nat.pow_mul, sq] at h2
    have h3 : (n + 1) ^ (n + 1) < (n + 1) * n ^ (n + 1) := by
      rw [Nat.pow_succ']; gcongr
    have h4 : (n + 2) ^ (n + 1) * n ^ (n + 1) < (n + 1) ^ (n + 2) * n ^ (n + 1) := by
      calc (n + 2) ^ (n + 1) * n ^ (n + 1)
        _ < (n + 1) ^ (n + 1) * (n + 1) ^ (n + 1) := h2
        _ < (n + 1) ^ (n + 1) * ((n + 1) * n ^ (n + 1)) := by gcongr
        _ = (n + 1) ^ (n + 2) * n ^ (n + 1) := by rw [← mul_assoc, ← Nat.pow_succ, Nat.pow_succ']
    exact Nat.lt_of_mul_lt_mul_right h4

theorem ceil_floor_eq_solutions (x : ℝ) (hx : 0 < x) :
    x ^ ⌈x⌉ = (⌈x⌉ : ℝ) ^ ⌊x⌋ + 1 ↔ x = Real.sqrt 3 ∨ x = (10 : ℝ) ^ (1 / 3 : ℝ) := by
  constructor
  · intro h
    have h_not_int : (⌊x⌋ : ℝ) ≠ x := by
      intro heq
      have hc : ⌈x⌉ = ⌊x⌋ := by rw [← heq, Int.ceil_intCast, Int.floor_intCast]
      have h' := h
      rw [hc, heq] at h'
      linarith
    have h_lt : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) h_not_int
    have h_ceil : ⌈x⌉ = ⌊x⌋ + 1 := by
      rw [Int.ceil_eq_iff]; push_cast
      exact ⟨by linarith [h_lt], by linarith [Int.lt_floor_add_one x]⟩
    have hk0 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr (le_of_lt hx)
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hk0
    have h_eq : x ^ (n + 1) = (n + 1 : ℝ) ^ n + 1 := by
      have h1 : x ^ ⌈x⌉ = x ^ (n + 1) := by
        rw [show ⌈x⌉ = ((n + 1 : ℕ) : ℤ) by omega, zpow_natCast]
      have h2 : (⌈x⌉ : ℝ) ^ ⌊x⌋ = (n + 1 : ℝ) ^ n := by
        rw [show ⌈x⌉ = ((n + 1 : ℕ) : ℤ) by omega, show ⌊x⌋ = (n : ℤ) by omega]
        push_cast; rw [zpow_natCast]
      linarith [h]
    have hx_lo : (n : ℝ) < x := by linarith [h_lt, show (⌊x⌋ : ℝ) = (n : ℝ) by exact_mod_cast hn]
    have hx_hi : x < (n + 1 : ℝ) := by
      linarith [Int.lt_floor_add_one x, show (⌊x⌋ : ℝ) = (n : ℝ) by exact_mod_cast hn]
    have hn_ge_1 : 1 ≤ n := by
      by_contra!
      have hn0 : n = 0 := by omega
      have h' := h_eq
      rw [hn0] at h' hx_hi
      norm_num at h' hx_hi
      linarith
    have hn_le_2 : n ≤ 2 := by
      by_contra! hn3
      have h_le : ((n + 1 : ℝ) ^ n + 1) ≤ (n : ℝ) ^ (n + 1) := by
        exact_mod_cast (Nat.succ_le_of_lt (pow_succ_lt hn3))
      have hx_pow_gt : (n : ℝ) ^ (n + 1) < x ^ (n + 1) := by gcongr
      linarith
    interval_cases n
    · left
      have hx2 : x ^ 2 = 3 := by
        have h' := h_eq
        norm_num at h'
        exact h'
      rw [← Real.sqrt_sq (le_of_lt hx), hx2]
    · right
      have hx3 : x ^ 3 = 10 := by
        have h' := h_eq
        norm_num at h'
        exact h'
      have h_rpow : x ^ ((3 : ℕ) : ℝ) = 10 := by rw [Real.rpow_natCast, hx3]
      have h_root : (x ^ ((3 : ℕ) : ℝ)) ^ (1 / 3 : ℝ) = (10 : ℝ) ^ (1 / 3 : ℝ) := by rw [h_rpow]
      rwa [← Real.rpow_mul (le_of_lt hx), show ((3 : ℕ) : ℝ) * (1 / 3 : ℝ) = 1 by norm_num,
        Real.rpow_one] at h_root
  · rintro (rfl | rfl)
    · have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h1 : 1 < Real.sqrt 3 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h2 : Real.sqrt 3 < 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have hf : ⌊Real.sqrt 3⌋ = 1 := by
        rw [Int.floor_eq_iff]; push_cast; exact ⟨by linarith, by linarith⟩
      have hc : ⌈Real.sqrt 3⌉ = 2 := by
        rw [Int.ceil_eq_iff]; push_cast; exact ⟨by linarith, by linarith⟩
      rw [hf, hc, show (Real.sqrt 3) ^ (2 : ℤ) = (Real.sqrt 3) ^ 2 by norm_cast, h3]
      norm_num
    · set y := (10 : ℝ) ^ (1 / 3 : ℝ)
      have hy3 : y ^ 3 = 10 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      have hy1 : 2 < y := by
        have : (2 : ℝ) = (8 : ℝ) ^ (1 / 3 : ℝ) := by
          rw [show (8 : ℝ) = (2 : ℝ) ^ ((3 : ℕ) : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [this]
        exact Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
      have hy2 : y < 3 := by
        have : (3 : ℝ) = (27 : ℝ) ^ (1 / 3 : ℝ) := by
          rw [show (27 : ℝ) = (3 : ℝ) ^ ((3 : ℕ) : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [this]
        exact Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
      have hf : ⌊y⌋ = 2 := by
        rw [Int.floor_eq_iff]; push_cast; exact ⟨by linarith, by linarith⟩
      have hc : ⌈y⌉ = 3 := by
        rw [Int.ceil_eq_iff]; push_cast; exact ⟨by linarith, by linarith⟩
      rw [hf, hc, show y ^ (3 : ℤ) = y ^ 3 by norm_cast, hy3]
      norm_num
```
