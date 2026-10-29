# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `29 July 2026`\
Line count: `125`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem ceil_floor_eq_solutions (x : ℝ) (hx : 0 < x) :
    x ^ ⌈x⌉ = (⌈x⌉ : ℝ) ^ ⌊x⌋ + 1 ↔ x = Real.sqrt 3 ∨ x = (10 : ℝ) ^ (1 / 3 : ℝ) := by
  -- strict monotonicity of `· ^ (k+1)` on nonnegatives
  have hpm : ∀ (a b : ℝ) (k : ℕ), 0 ≤ a → a < b → a ^ (k + 1) < b ^ (k + 1) := by
    intro a b k ha hab
    have hb : 0 < b := lt_of_le_of_lt ha hab
    induction k with
    | zero => simpa using hab
    | succ j ih =>
      calc a ^ (j + 1 + 1) = a ^ (j + 1) * a := by ring
        _ ≤ a ^ (j + 1) * b := mul_le_mul_of_nonneg_left hab.le (pow_nonneg ha _)
        _ < b ^ (j + 1) * b := mul_lt_mul_of_pos_right ih hb
        _ = b ^ (j + 1 + 1) := by ring
  -- key arithmetic inequality for m ≥ 3
  have key : ∀ m : ℕ, 3 ≤ m → (m + 1) ^ m + 1 ≤ m ^ (m + 1) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have hA : k ^ (k + 1) * (k + 2) ^ (k + 1) ≤ (k + 1) ^ (k + 1) * (k + 1) ^ (k + 1) := by
        rw [← mul_pow, ← mul_pow]
        exact Nat.pow_le_pow_left (by nlinarith) _
      have hpow : (k + 1) ^ k * (k + 1) ^ (k + 2) = (k + 1) ^ (k + 1) * (k + 1) ^ (k + 1) := by
        rw [← pow_add, ← pow_add, show k + (k + 2) = k + 1 + (k + 1) by omega]
      have hB : (k + 1) ^ (k + 1) * (k + 1) ^ (k + 1) + (k + 1) ^ (k + 2)
          ≤ k ^ (k + 1) * (k + 1) ^ (k + 2) := by
        calc (k + 1) ^ (k + 1) * (k + 1) ^ (k + 1) + (k + 1) ^ (k + 2)
            = ((k + 1) ^ k + 1) * (k + 1) ^ (k + 2) := by rw [← hpow]; ring
          _ ≤ k ^ (k + 1) * (k + 1) ^ (k + 2) := Nat.mul_le_mul ih (le_refl _)
      have hC : k ^ (k + 1) ≤ (k + 1) ^ (k + 2) :=
        le_trans (Nat.pow_le_pow_left (Nat.le_succ k) (k + 1))
          (Nat.pow_le_pow_right (by omega) (by omega))
      have hpos : 0 < k ^ (k + 1) := pow_pos (by omega) _
      have hfin : k ^ (k + 1) * ((k + 2) ^ (k + 1) + 1) ≤ k ^ (k + 1) * (k + 1) ^ (k + 2) := by
        calc k ^ (k + 1) * ((k + 2) ^ (k + 1) + 1)
            = k ^ (k + 1) * (k + 2) ^ (k + 1) + k ^ (k + 1) := by ring
          _ ≤ (k + 1) ^ (k + 1) * (k + 1) ^ (k + 1) + (k + 1) ^ (k + 2) := Nat.add_le_add hA hC
          _ ≤ k ^ (k + 1) * (k + 1) ^ (k + 2) := hB
      have hres := Nat.le_of_mul_le_mul_left hfin hpos
      rw [show k + 1 + 1 = k + 2 by omega]
      exact hres
  -- numeric facts
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs1 : (1 : ℝ) < Real.sqrt 3 := by nlinarith [h3, hs0]
  have hs2 : Real.sqrt 3 < 2 := by nlinarith [h3, hs0]
  have ht0 : (0 : ℝ) < (10 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have ht3 : ((10 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 10 := by
    rw [← Real.rpow_natCast ((10 : ℝ) ^ (1 / 3 : ℝ)) 3,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)]
    norm_num
  have ht1 : (2 : ℝ) < (10 : ℝ) ^ (1 / 3 : ℝ) := by
    nlinarith [ht3, ht0, sq_nonneg ((10 : ℝ) ^ (1 / 3 : ℝ))]
  have ht2 : (10 : ℝ) ^ (1 / 3 : ℝ) < 3 := by
    nlinarith [ht3, ht0, sq_nonneg ((10 : ℝ) ^ (1 / 3 : ℝ))]
  have hfs : ⌊Real.sqrt 3⌋ = 1 := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith
  have hcs : ⌈Real.sqrt 3⌉ = 2 := by
    refine Int.ceil_eq_iff.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith
  have hft : ⌊(10 : ℝ) ^ (1 / 3 : ℝ)⌋ = 2 := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith
  have hct : ⌈(10 : ℝ) ^ (1 / 3 : ℝ)⌉ = 3 := by
    refine Int.ceil_eq_iff.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith
  constructor
  · intro heq
    have hfl0 : 0 ≤ ⌊x⌋ := Int.le_floor.mpr (by exact_mod_cast hx.le)
    have hfl := Int.floor_le x
    have hfl2 := Int.lt_floor_add_one x
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌊x⌋ = (m : ℤ) := ⟨⌊x⌋.toNat, (Int.toNat_of_nonneg hfl0).symm⟩
    rw [hm] at heq hfl hfl2
    rcases eq_or_lt_of_le hfl with hxint | hxlt
    · exfalso
      have hc : ⌈x⌉ = (m : ℤ) := by rw [← hxint]; exact Int.ceil_intCast _
      rw [hc, ← hxint] at heq
      linarith
    · push_cast at hxlt hfl2
      have hc : ⌈x⌉ = (m : ℤ) + 1 := by
        refine Int.ceil_eq_iff.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith
      rw [hc] at heq
      rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by omega] at heq
      simp only [zpow_natCast] at heq
      push_cast at heq
      rcases Nat.lt_or_ge m 3 with hm3 | hm3
      · have hm012 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        rcases hm012 with rfl | rfl | rfl
        · exfalso
          norm_num at heq
          norm_num at hfl2
          linarith
        · left
          norm_num at heq
          have h7 : (x - Real.sqrt 3) * (x + Real.sqrt 3) = 0 := by
            linear_combination heq - h3
          rcases mul_eq_zero.mp h7 with h8 | h8
          · linarith
          · linarith
        · right
          norm_num at heq
          have h7 : (x - (10 : ℝ) ^ (1 / 3 : ℝ)) *
              (x ^ 2 + x * (10 : ℝ) ^ (1 / 3 : ℝ) + ((10 : ℝ) ^ (1 / 3 : ℝ)) ^ 2) = 0 := by
            linear_combination heq - ht3
          rcases mul_eq_zero.mp h7 with h8 | h8
          · linarith
          · exfalso
            nlinarith [mul_pos hx hx, mul_pos hx ht0, mul_pos ht0 ht0]
      · exfalso
        have hkey := key m hm3
        have h6 : ((m : ℝ) + 1) ^ m + 1 ≤ (m : ℝ) ^ (m + 1) := by exact_mod_cast hkey
        have hlt : (m : ℝ) ^ (m + 1) < x ^ (m + 1) := hpm (m : ℝ) x m (by positivity) hxlt
        linarith
  · rintro (rfl | rfl)
    · rw [hcs, hfs]
      have h1 : Real.sqrt 3 ^ (2 : ℤ) = 3 := by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
        exact h3
      rw [h1]
      norm_num
    · rw [hct, hft]
      have h1 : ((10 : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℤ) = 10 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
        exact ht3
      rw [h1]
      norm_num
```
