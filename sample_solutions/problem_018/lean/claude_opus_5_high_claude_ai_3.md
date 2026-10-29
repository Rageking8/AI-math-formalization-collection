# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `12 August 2026`\
Line count: `41`\
Turn count: `1`

## Note

This solution uses `native_decide`. The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem no_nat_sq_cube_digits_one_through_nine_twice :
    ¬ ∃ (n : ℕ), List.Perm (Nat.digits 10 (n ^ 2) ++ Nat.digits 10 (n ^ 3))
      (List.range' 1 9 ++ List.range' 1 9) := by
  rintro ⟨n, h⟩
  have hn : n ≠ 0 := by rintro rfl; simpa using h.length_eq
  have q2 : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have q3 : n ^ 3 ≠ 0 := pow_ne_zero 3 hn
  have hlen : Nat.log 10 (n ^ 2) + Nat.log 10 (n ^ 3) = 16 := by
    have hp := h.length_eq
    simp [Nat.digits_len 10 (n ^ 2) (by norm_num) q2,
      Nat.digits_len 10 (n ^ 3) (by norm_num) q3] at hp
    omega
  have f2 : n ^ 2 + 1 ≤ 10 ^ (Nat.log 10 (n ^ 2) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have f3 : n ^ 3 + 1 ≤ 10 ^ (Nat.log 10 (n ^ 3) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hlow : (10 : ℕ) ^ 16 ≤ n ^ 5 :=
    calc (10 : ℕ) ^ 16 = 10 ^ Nat.log 10 (n ^ 2) * 10 ^ Nat.log 10 (n ^ 3) := by
          rw [← pow_add, hlen]
      _ ≤ n ^ 2 * n ^ 3 :=
          Nat.mul_le_mul (Nat.pow_log_le_self 10 q2) (Nat.pow_log_le_self 10 q3)
      _ = n ^ 5 := by ring
  have hhigh : n ^ 5 < (10 : ℕ) ^ 18 :=
    calc n ^ 5 < n ^ 5 + n ^ 3 + n ^ 2 + 1 := by omega
      _ = (n ^ 2 + 1) * (n ^ 3 + 1) := by ring
      _ ≤ 10 ^ (Nat.log 10 (n ^ 2) + 1) * 10 ^ (Nat.log 10 (n ^ 3) + 1) := Nat.mul_le_mul f2 f3
      _ = 10 ^ 18 := by rw [← pow_add]; congr 1; omega
  have hA : 1585 ≤ n := by
    by_contra hc
    have := hlow.trans (Nat.pow_le_pow_left (show n ≤ 1584 by omega) 5)
    norm_num at this
  have hB : n ≤ 3981 := by
    by_contra hc
    have := (Nat.pow_le_pow_left (show 3982 ≤ n by omega) 5).trans_lt hhigh
    norm_num at this
  have H : ∀ m ∈ Finset.Icc 1585 3981,
      ¬ (Nat.digits 10 (m ^ 2) ++ Nat.digits 10 (m ^ 3)).Perm
        (List.range' 1 9 ++ List.range' 1 9) := by native_decide
  exact H n (Finset.mem_Icc.mpr ⟨hA, hB⟩) h
```
