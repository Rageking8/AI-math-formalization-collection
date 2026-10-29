# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `6 August 2026`\
Line count: `46`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem unique_pos_int_digit_length_ineq (n : ℕ) (hn : 0 < n) :
    n * (Nat.digits 10 n).length ≤ (Nat.digits 10 n.factorial).length ↔ n = 1 := by
  have key : ∀ m : ℕ, (m + 1).factorial ≤ (m + 1) ^ m := by
    intro m
    induction m with
    | zero => decide
    | succ k ih =>
      calc (k + 1 + 1).factorial = (k + 1 + 1) * (k + 1).factorial := Nat.factorial_succ _
        _ ≤ (k + 1 + 1) * (k + 1) ^ k := Nat.mul_le_mul (le_refl _) ih
        _ ≤ (k + 1 + 1) * (k + 1 + 1) ^ k :=
            Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_left (by omega) k)
        _ = (k + 1 + 1) ^ (k + 1) := by ring
  constructor
  · intro h
    by_contra hne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 1 ≤ m := by omega
    have hfne : (m + 1).factorial ≠ 0 := (Nat.factorial_pos _).ne'
    have hlen_n : (Nat.digits 10 (m + 1)).length = Nat.log 10 (m + 1) + 1 :=
      Nat.digits_len 10 (m + 1) (by norm_num) (by omega)
    have hlen_f : (Nat.digits 10 (m + 1).factorial).length
        = Nat.log 10 (m + 1).factorial + 1 :=
      Nat.digits_len 10 _ (by norm_num) hfne
    have hlt : m + 1 < 10 ^ (Nat.log 10 (m + 1) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) (m + 1)
    have hfl : (m + 1).factorial < 10 ^ ((Nat.log 10 (m + 1) + 1) * m) := by
      calc (m + 1).factorial ≤ (m + 1) ^ m := key m
        _ < (10 ^ (Nat.log 10 (m + 1) + 1)) ^ m := Nat.pow_lt_pow_left hlt (by omega)
        _ = 10 ^ ((Nat.log 10 (m + 1) + 1) * m) := by rw [← pow_mul]
    have hlog : Nat.log 10 (m + 1).factorial < (Nat.log 10 (m + 1) + 1) * m :=
      Nat.log_lt_of_lt_pow hfne hfl
    rw [hlen_n, hlen_f] at h
    have hchain : (Nat.log 10 (m + 1) + 1) * m + (Nat.log 10 (m + 1) + 1)
        ≤ (Nat.log 10 (m + 1) + 1) * m + 0 := by
      calc (Nat.log 10 (m + 1) + 1) * m + (Nat.log 10 (m + 1) + 1)
          = (m + 1) * (Nat.log 10 (m + 1) + 1) := by ring
        _ ≤ Nat.log 10 (m + 1).factorial + 1 := h
        _ ≤ (Nat.log 10 (m + 1) + 1) * m := hlog
        _ = (Nat.log 10 (m + 1) + 1) * m + 0 := by ring
    have hfin := Nat.le_of_add_le_add_left hchain
    omega
  · rintro rfl
    have h1 : Nat.factorial 1 = 1 := rfl
    simp [h1]
```
