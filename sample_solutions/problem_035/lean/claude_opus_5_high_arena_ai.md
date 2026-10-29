# Claude Opus 5 High (Arena AI)

Model: `claude-opus-5-high` (via Arena AI)\
Date: `5 September 2026`\
Line count: `48`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem unique_pos_int_digit_length_ineq (n : ℕ) (hn : 0 < n) :
    n * (Nat.digits 10 n).length ≤ (Nat.digits 10 n.factorial).length ↔ n = 1 := by
  -- Key bound: `(k+1)! ≤ (k+1)^k`
  have fact_le : ∀ k : ℕ, (k + 1).factorial ≤ (k + 1) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
      rw [Nat.factorial_succ]
      calc (j + 1 + 1) * (j + 1).factorial
          ≤ (j + 1 + 1) * ((j + 1 + 1) ^ j) :=
            Nat.mul_le_mul le_rfl (ih.trans (Nat.pow_le_pow_left (by omega) j))
        _ = (j + 1 + 1) ^ (j + 1) := by ring
  constructor
  · intro h
    by_contra hne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 1 ≤ m := by omega
    have hdlen : (Nat.digits 10 (m + 1)).length = Nat.log 10 (m + 1) + 1 := by
      rw [Nat.digits_len] <;> omega
    have hd1 : 1 ≤ (Nat.digits 10 (m + 1)).length := by omega
    have hnlt : m + 1 < 10 ^ (Nat.digits 10 (m + 1)).length := by
      rw [hdlen]
      exact Nat.lt_pow_succ_log_self (by norm_num) (m + 1)
    have hfact : (m + 1).factorial < 10 ^ ((Nat.digits 10 (m + 1)).length * m) := by
      calc (m + 1).factorial ≤ (m + 1) ^ m := fact_le m
        _ < (10 ^ (Nat.digits 10 (m + 1)).length) ^ m :=
            Nat.pow_lt_pow_left hnlt (by omega)
        _ = 10 ^ ((Nat.digits 10 (m + 1)).length * m) := by rw [← pow_mul]
    have hlog : Nat.log 10 ((m + 1).factorial) < (Nat.digits 10 (m + 1)).length * m :=
      Nat.log_lt_of_lt_pow (Nat.factorial_pos _).ne' hfact
    have hL : (Nat.digits 10 ((m + 1).factorial)).length
        = Nat.log 10 ((m + 1).factorial) + 1 := by
      rw [Nat.digits_len] <;> first | omega | exact (Nat.factorial_pos _).ne'
    rw [hL] at h
    have h5 : (Nat.digits 10 (m + 1)).length * m + (Nat.digits 10 (m + 1)).length
        ≤ (Nat.digits 10 (m + 1)).length * m + 0 := by
      rw [Nat.add_zero]
      calc (Nat.digits 10 (m + 1)).length * m + (Nat.digits 10 (m + 1)).length
          = (m + 1) * (Nat.digits 10 (m + 1)).length := by ring
        _ ≤ Nat.log 10 ((m + 1).factorial) + 1 := h
        _ ≤ (Nat.digits 10 (m + 1)).length * m := hlog
    have h6 := Nat.le_of_add_le_add_left h5
    omega
  · rintro rfl
    simp [Nat.factorial_one]
```
