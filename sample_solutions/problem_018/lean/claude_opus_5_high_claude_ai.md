# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `29 July 2026`\
Line count: `71`\
Turn count: `1`

## Note

This solution uses `native_decide`.

## Solution

```lean4
import Mathlib

theorem no_nat_sq_cube_digits_one_through_nine_twice :
    ¬ ∃ (n : ℕ), List.Perm (Nat.digits 10 (n ^ 2) ++ Nat.digits 10 (n ^ 3))
      (List.range' 1 9 ++ List.range' 1 9) := by
  rintro ⟨n, hp⟩
  -- Step 1: the two digit lists together have 18 entries.
  have hr : (List.range' 1 9 ++ List.range' 1 9).length = 18 := rfl
  have hlen : (Nat.digits 10 (n ^ 2)).length + (Nat.digits 10 (n ^ 3)).length = 18 := by
    have h := hp.length_eq
    rw [hr, List.length_append] at h
    exact h
  have hn : n ≠ 0 := by
    rintro rfl
    norm_num at hlen
  have hn2 : n ^ 2 ≠ 0 := pow_ne_zero _ hn
  have hn3 : n ^ 3 ≠ 0 := pow_ne_zero _ hn
  -- Step 2: rewrite lengths via `Nat.log`.
  have hL : (Nat.digits 10 (n ^ 2)).length = Nat.log 10 (n ^ 2) + 1 :=
    Nat.digits_len 10 (n ^ 2) (by norm_num) hn2
  have hM : (Nat.digits 10 (n ^ 3)).length = Nat.log 10 (n ^ 3) + 1 :=
    Nat.digits_len 10 (n ^ 3) (by norm_num) hn3
  have h1 : 10 ^ Nat.log 10 (n ^ 2) ≤ n ^ 2 := Nat.pow_log_le_self 10 hn2
  have h2 : n ^ 2 < 10 ^ (Nat.log 10 (n ^ 2) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : 10 ^ Nat.log 10 (n ^ 3) ≤ n ^ 3 := Nat.pow_log_le_self 10 hn3
  have h4 : n ^ 3 < 10 ^ (Nat.log 10 (n ^ 3) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  -- Step 3: compare `n ^ 6` in two ways.
  have e1 : (10:ℕ) ^ (Nat.log 10 (n ^ 2) * 3) < 10 ^ ((Nat.log 10 (n ^ 3) + 1) * 2) :=
    calc (10:ℕ) ^ (Nat.log 10 (n ^ 2) * 3) = (10 ^ Nat.log 10 (n ^ 2)) ^ 3 := pow_mul _ _ _
      _ ≤ (n ^ 2) ^ 3 := Nat.pow_le_pow_left h1 3
      _ = (n ^ 3) ^ 2 := by ring
      _ < (10 ^ (Nat.log 10 (n ^ 3) + 1)) ^ 2 := Nat.pow_lt_pow_left h4 (by norm_num)
      _ = 10 ^ ((Nat.log 10 (n ^ 3) + 1) * 2) := (pow_mul _ _ _).symm
  have e2 : (10:ℕ) ^ (Nat.log 10 (n ^ 3) * 2) < 10 ^ ((Nat.log 10 (n ^ 2) + 1) * 3) :=
    calc (10:ℕ) ^ (Nat.log 10 (n ^ 3) * 2) = (10 ^ Nat.log 10 (n ^ 3)) ^ 2 := pow_mul _ _ _
      _ ≤ (n ^ 3) ^ 2 := Nat.pow_le_pow_left h3 2
      _ = (n ^ 2) ^ 3 := by ring
      _ < (10 ^ (Nat.log 10 (n ^ 2) + 1)) ^ 3 := Nat.pow_lt_pow_left h2 (by norm_num)
      _ = 10 ^ ((Nat.log 10 (n ^ 2) + 1) * 3) := (pow_mul _ _ _).symm
  have f1 : Nat.log 10 (n ^ 2) * 3 < (Nat.log 10 (n ^ 3) + 1) * 2 := by
    by_contra hc
    push_neg at hc
    exact absurd e1 (not_lt.mpr (Nat.pow_le_pow_right (by norm_num) hc))
  have f2 : Nat.log 10 (n ^ 3) * 2 < (Nat.log 10 (n ^ 2) + 1) * 3 := by
    by_contra hc
    push_neg at hc
    exact absurd e2 (not_lt.mpr (Nat.pow_le_pow_right (by norm_num) hc))
  -- Step 4: `n ^ 2` has 7 digits, `n ^ 3` has 11 digits.
  have hL6 : Nat.log 10 (n ^ 2) = 6 := by omega
  have hM10 : Nat.log 10 (n ^ 3) = 10 := by omega
  rw [hL6] at h2
  rw [hM10] at h3
  -- Step 5: bound `n`.
  have hlow : 2155 ≤ n := by
    by_contra hc
    push_neg at hc
    have h5 : n ^ 3 ≤ 2154 ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h6 : (10:ℕ) ^ 10 ≤ 2154 ^ 3 := le_trans h3 h5
    norm_num at h6
  have hhigh : n ≤ 3162 := by
    by_contra hc
    push_neg at hc
    have h5 : (3163:ℕ) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h6 : (3163:ℕ) ^ 2 < 10 ^ (6 + 1) := lt_of_le_of_lt h5 h2
    norm_num at h6
  -- Step 6: exhaustive check of the remaining range.
  have key : ∀ m ∈ Finset.Icc 2155 3162,
      ¬ List.Perm (Nat.digits 10 (m ^ 2) ++ Nat.digits 10 (m ^ 3))
        (List.range' 1 9 ++ List.range' 1 9) := by
    native_decide
  exact key n (Finset.mem_Icc.mpr ⟨hlow, hhigh⟩) hp
```
