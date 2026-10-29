# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `11 August 2026`\
Line count: `75`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem ceil_floor_eq_solutions (x : ℝ) (hx : 0 < x) :
    x ^ ⌈x⌉ = (⌈x⌉ : ℝ) ^ ⌊x⌋ + 1 ↔ x = Real.sqrt 3 ∨ x = (10 : ℝ) ^ (1 / 3 : ℝ) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : ((10:ℝ) ^ (1/3 : ℝ)) ^ (3:ℕ) = 10 := by
    rw [← Real.rpow_natCast ((10:ℝ) ^ (1/3:ℝ)) 3, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)]
    norm_num
  have hq0 : (0:ℝ) < (10:ℝ) ^ (1/3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have key : ∀ k : ℕ, 3 ≤ k → (k+1) ^ k < k ^ (k+1) := by
    intro k
    induction k with
    | zero => exact fun hk => absurd hk (by omega)
    | succ n ih =>
      intro hk
      rcases Nat.lt_or_ge n 3 with hn | hn
      · obtain rfl : n = 2 := by omega
        norm_num
      · have hm : (n+1+1) ^ (n+1) * n ^ (n+1) < (n+1) ^ (n+1+1) * n ^ (n+1) :=
          calc (n+1+1) ^ (n+1) * n ^ (n+1) = ((n+1+1) * n) ^ (n+1) := (mul_pow _ _ _).symm
            _ < ((n+1) * (n+1)) ^ (n+1) := Nat.pow_lt_pow_left (by nlinarith) (by omega)
            _ = (n+1) ^ (n+1+1) * (n+1) ^ n := by
                rw [mul_pow, ← pow_add, ← pow_add, show n+1+(n+1) = n+1+1+n by omega]
            _ < (n+1) ^ (n+1+1) * n ^ (n+1) := mul_lt_mul_of_pos_left (ih hn) (by positivity)
        exact lt_of_mul_lt_mul_right hm (Nat.zero_le _)
  constructor
  · intro h
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ⌊x⌋ = (k : ℤ) :=
      ⟨⌊x⌋.toNat, (Int.toNat_of_nonneg (Int.floor_nonneg.2 hx.le)).symm⟩
    have hle : (k:ℝ) ≤ x := by have h' := Int.floor_le x; rw [hk] at h'; exact_mod_cast h'
    have hlt : x < (k:ℝ) + 1 := by
      have h' := Int.lt_floor_add_one x; rw [hk] at h'; exact_mod_cast h'
    rcases eq_or_lt_of_le hle with he | he
    · exfalso
      rw [show ⌈x⌉ = (k:ℤ) by rw [← he]; simp, hk, ← he] at h
      push_cast at h
      linarith
    · rw [show ⌈x⌉ = ((k+1 : ℕ) : ℤ) by
            rw [Int.ceil_eq_iff]; constructor <;> push_cast <;> linarith,
          hk, zpow_natCast, zpow_natCast] at h
      push_cast at h
      rcases Nat.lt_or_ge k 3 with h3 | h3
      · interval_cases k
        · exfalso; norm_num at h hlt; linarith
        · left
          norm_num at h
          rw [show (3:ℝ) = x ^ 2 by linarith, Real.sqrt_sq hx.le]
        · right
          norm_num at h
          rw [show (10:ℝ) = x ^ 3 by linarith, ← Real.rpow_natCast x 3, ← Real.rpow_mul hx.le]
          norm_num
      · exfalso
        have h1 : ((k:ℝ) + 1) ^ k + 1 ≤ (k:ℝ) ^ (k+1) := by
          have h2 : ((k+1) ^ k + 1 : ℕ) ≤ k ^ (k+1) := key k h3
          exact_mod_cast h2
        have h4 : (k:ℝ) ^ (k+1) < x ^ (k+1) := by gcongr
        linarith
  · have H : ∀ (y : ℝ) (b : ℕ), (b:ℝ) < y → y < b + 1 →
        y ^ (b+1) = ((b:ℝ) + 1) ^ b + 1 → y ^ ⌈y⌉ = (⌈y⌉ : ℝ) ^ ⌊y⌋ + 1 := by
      intro y b h1 h2 h3
      rw [show ⌊y⌋ = (b:ℤ) by rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith,
          show ⌈y⌉ = ((b+1 : ℕ) : ℤ) by
            rw [Int.ceil_eq_iff]; constructor <;> push_cast <;> linarith,
          zpow_natCast, zpow_natCast]
      push_cast
      linarith [h3]
    rintro (rfl | rfl)
    · refine H _ 1 ?_ ?_ ?_ <;> push_cast
      · nlinarith [hs, Real.sqrt_nonneg 3]
      · nlinarith [hs, Real.sqrt_nonneg 3]
      · linarith [hs]
    · refine H _ 2 ?_ ?_ ?_ <;> push_cast
      · nlinarith [hq, hq0, sq_nonneg ((10:ℝ) ^ (1/3:ℝ) - 2)]
      · nlinarith [hq, hq0, sq_nonneg ((10:ℝ) ^ (1/3:ℝ) - 3)]
      · linarith [hq]
```
