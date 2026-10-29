# Unknown (Arena AI)

Model: `Unknown` (via Arena AI)\
Date: `27 July 2026`\
Line count: `140`\
Turn count: `1`

## Note

The model's identity is unknown as the other assistant got stuck generating a response on Arena AI.

## Solution

```lean4
import Mathlib

theorem ceil_floor_eq_solutions (x : ℝ) (hx : 0 < x) :
    x ^ ⌈x⌉ = (⌈x⌉ : ℝ) ^ ⌊x⌋ + 1 ↔ x = Real.sqrt 3 ∨ x = (10 : ℝ) ^ (1 / 3 : ℝ) := by
  -- helpers converting `zpow` with numeral exponents to `pow`
  have e1 : ∀ a : ℝ, a ^ (1:ℤ) = a := fun a => zpow_one a
  have e2 : ∀ a : ℝ, a ^ (2:ℤ) = a ^ (2:ℕ) := by
    intro a; rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast]
  have e3 : ∀ a : ℝ, a ^ (3:ℤ) = a ^ (3:ℕ) := by
    intro a; rw [show (3:ℤ) = ((3:ℕ):ℤ) by norm_num, zpow_natCast]
  -- monotonicity of powers (proved by hand, to avoid lemma-name issues)
  have powle : ∀ (a b : ℝ), 0 ≤ a → a ≤ b → ∀ k : ℕ, a ^ k ≤ b ^ k := by
    intro a b ha hab k
    induction k with
    | zero => simp
    | succ p ih =>
        have hb : (0:ℝ) ≤ b := le_trans ha hab
        calc a ^ (p+1) = a ^ p * a := pow_succ a p
          _ ≤ b ^ p * b := mul_le_mul ih hab ha (pow_nonneg hb p)
          _ = b ^ (p+1) := (pow_succ b p).symm
  have powlt : ∀ (a b : ℝ), 0 ≤ a → a < b → ∀ k : ℕ, a ^ (k+1) < b ^ (k+1) := by
    intro a b ha hab k
    induction k with
    | zero => simpa using hab
    | succ p ih =>
        have hbp : (0:ℝ) < b ^ (p+1) := pow_pos (lt_of_le_of_lt ha hab) _
        calc a ^ (p+1+1) = a ^ (p+1) * a := pow_succ a (p+1)
          _ ≤ b ^ (p+1) * a := mul_le_mul_of_nonneg_right ih.le ha
          _ < b ^ (p+1) * b := mul_lt_mul_of_pos_left hab hbp
          _ = b ^ (p+1+1) := (pow_succ b (p+1)).symm
  -- facts about √3
  have hs3 : Real.sqrt 3 ^ (2:ℕ) = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : (1:ℝ) < Real.sqrt 3 := by nlinarith
  have hs2 : Real.sqrt 3 < 2 := by nlinarith
  -- facts about 10^(1/3)
  set c : ℝ := (10:ℝ) ^ (1/3 : ℝ) with hcdef
  have hc0 : (0:ℝ) < c := by
    rw [hcdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have ht3 : c ^ (3:ℕ) = 10 := by
    rw [hcdef, ← Real.rpow_natCast ((10:ℝ) ^ (1/3:ℝ)) 3,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10)]
    norm_num
  have hc1 : (2:ℝ) < c := by nlinarith [sq_nonneg (c - 2), sq_nonneg (c + 2)]
  have hc2 : c < 3 := by nlinarith [sq_nonneg (c - 3), sq_nonneg (c + 3)]
  -- key inequality : (m+1)^m < m^(m+1) for m ≥ 3
  have key : ∀ m : ℕ, 3 ≤ m → ((m:ℝ) + 1) ^ m < (m:ℝ) ^ (m + 1) := by
    intro m hm
    have hm3 : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hm0 : (0:ℝ) < (m:ℝ) := by linarith
    have hmne : (m:ℝ) ≠ 0 := ne_of_gt hm0
    have hle : 1 + 1/(m:ℝ) ≤ Real.exp (1/(m:ℝ)) := by
      have := Real.add_one_le_exp (1/(m:ℝ)); linarith
    have h1 : (1 + 1/(m:ℝ)) ^ m ≤ (Real.exp (1/(m:ℝ))) ^ m :=
      powle _ _ (by positivity) hle m
    have h2 : (Real.exp (1/(m:ℝ))) ^ m = Real.exp 1 := by
      have h2' : ∀ k : ℕ, (Real.exp (1/(m:ℝ))) ^ k = Real.exp ((k:ℝ) * (1/(m:ℝ))) := by
        intro k
        induction k with
        | zero => simp
        | succ p ih =>
            rw [pow_succ, ih, ← Real.exp_add]
            congr 1
            push_cast
            ring
      rw [h2' m, mul_one_div, div_self hmne]
    have hexp : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have hmm : (0:ℝ) < (m:ℝ) ^ m := pow_pos hm0 m
    have hbase : ((m:ℝ) + 1) = (m:ℝ) * (1 + 1/(m:ℝ)) := by
      rw [mul_add, mul_one, mul_one_div, div_self hmne]
    calc ((m:ℝ) + 1) ^ m = (m:ℝ) ^ m * (1 + 1/(m:ℝ)) ^ m := by rw [hbase, mul_pow]
      _ < (m:ℝ) ^ m * (m:ℝ) := by
          have hlt2 : (1 + 1/(m:ℝ)) ^ m < (m:ℝ) := by linarith
          exact mul_lt_mul_of_pos_left hlt2 hmm
      _ = (m:ℝ) ^ (m + 1) := (pow_succ _ _).symm
  constructor
  · intro h
    have hf0 : 0 ≤ ⌊x⌋ := Int.le_floor.mpr (by exact_mod_cast hx.le)
    rcases eq_or_lt_of_le (Int.floor_le x) with heq | hlt
    · exfalso
      have hce : ⌈x⌉ = ⌊x⌋ := Int.ceil_eq_iff.mpr ⟨by linarith, by linarith⟩
      rw [hce, heq] at h
      linarith
    · have hce : ⌈x⌉ = ⌊x⌋ + 1 := by
        refine Int.ceil_eq_iff.mpr ⟨?_, ?_⟩
        · push_cast; linarith
        · push_cast; linarith [Int.lt_floor_add_one x]
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌊x⌋ = (n:ℤ) :=
        ⟨⌊x⌋.toNat, (Int.toNat_of_nonneg hf0).symm⟩
      have hub : x < (n:ℝ) + 1 := by
        have := Int.lt_floor_add_one x
        rw [hn] at this; push_cast at this; exact this
      rw [hn] at hlt
      push_cast at hlt
      rw [hce, hn, show ((n:ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, zpow_natCast] at h
      push_cast at h
      by_cases h3 : 3 ≤ n
      · exfalso
        have hxpow : ((n:ℝ)) ^ (n+1) < x ^ (n+1) :=
          powlt _ _ (Nat.cast_nonneg n) hlt n
        have hnat : ((n+1) ^ n : ℕ) < (n ^ (n+1) : ℕ) := by
          have := key n h3
          exact_mod_cast this
        have hnat' : (((n+1) ^ n : ℕ) : ℝ) + 1 ≤ ((n ^ (n+1) : ℕ) : ℝ) := by
          have h' : ((n+1) ^ n : ℕ) + 1 ≤ (n ^ (n+1) : ℕ) := hnat
          exact_mod_cast h'
        push_cast at hnat'
        linarith
      · push_neg at h3
        interval_cases n
        · exfalso
          norm_num at h hub
          linarith
        · left
          have hx2 : x ^ 2 = 3 := by norm_num at h; linarith
          rw [← hx2, Real.sqrt_sq hx.le]
        · right
          have hx3 : x ^ 3 = 10 := by norm_num at h; linarith
          have hfac : (x - c) * (x^2 + x*c + c^2) = 0 := by
            linear_combination hx3 - ht3
          have hpos : 0 < x^2 + x*c + c^2 := by
            linarith [mul_pos hx hc0, sq_nonneg x, sq_nonneg c]
          rcases mul_eq_zero.mp hfac with h1 | h1
          · linarith
          · linarith
  · rintro (rfl | rfl)
    · have hf : ⌊Real.sqrt 3⌋ = 1 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      have hce : ⌈Real.sqrt 3⌉ = 2 :=
        Int.ceil_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [hf, hce, e2, e1, hs3]
      norm_num
    · have hf : ⌊c⌋ = 2 :=
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      have hce : ⌈c⌉ = 3 :=
        Int.ceil_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [hf, hce, e3, e2, ht3]
      norm_num
```
