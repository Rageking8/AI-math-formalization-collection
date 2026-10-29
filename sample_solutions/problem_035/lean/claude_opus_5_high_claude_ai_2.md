# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `20 August 2026`\
Line count: `23`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem unique_pos_int_digit_length_ineq (n : ℕ) (hn : 0 < n) :
    n * (Nat.digits 10 n).length ≤ (Nat.digits 10 n.factorial).length ↔ n = 1 := by
  have K : ∀ k, Nat.factorial (k + 1) ≤ (k + 1) ^ k := fun k => by
    induction k with
    | zero => simp
    | succ j ih =>
      calc Nat.factorial (j + 2) = (j + 2) * Nat.factorial (j + 1) := Nat.factorial_succ _
        _ ≤ (j + 2) * (j + 2) ^ j :=
            Nat.mul_le_mul le_rfl (ih.trans (Nat.pow_le_pow_left (by omega) j))
        _ = (j + 2) ^ (j + 1) := by ring
  refine ⟨fun h => ?_, fun h => by subst h; simp⟩
  by_contra hne
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Nat.digits_len 10 (m + 2) (by norm_num) (by omega),
      Nat.digits_len 10 _ (by norm_num) (Nat.factorial_pos (m + 2)).ne'] at h
  have := Nat.log_lt_of_lt_pow (Nat.factorial_pos (m + 2)).ne' <|
    calc Nat.factorial (m + 2) ≤ (m + 2) ^ (m + 1) := K (m + 1)
      _ < (10 ^ (Nat.log 10 (m + 2) + 1)) ^ (m + 1) :=
          Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by norm_num) _) (by omega)
      _ = 10 ^ ((Nat.log 10 (m + 2) + 1) * (m + 1)) := (pow_mul _ _ _).symm
  nlinarith
```
