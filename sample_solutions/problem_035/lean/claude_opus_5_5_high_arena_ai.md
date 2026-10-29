# Claude Opus 5.5 High (Arena AI)

Model: `claude-opus-5.5-high` (via Arena AI)\
Date: `10 October 2026`\
Line count: `39`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem unique_pos_int_digit_length_ineq (n : ℕ) (hn : 0 < n) :
    n * (Nat.digits 10 n).length ≤ (Nat.digits 10 n.factorial).length ↔ n = 1 := by
  have key : ∀ m : ℕ, (m+1).factorial ≤ (m+1)^m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Nat.factorial_succ, pow_succ]
      have h' : (k+1)^k ≤ (k+1+1)^k := Nat.pow_le_pow_left (by omega) k
      calc (k+1+1) * (k+1).factorial ≤ (k+1+1) * (k+1+1)^k :=
            Nat.mul_le_mul le_rfl (ih.trans h')
        _ = (k+1+1)^k * (k+1+1) := by ring
  constructor
  · intro h
    by_contra hne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n-2, by omega⟩
    have h1 : m + 2 < 10 ^ (Nat.digits 10 (m+2)).length :=
      Nat.lt_base_pow_length_digits (by norm_num)
    have h2 : 10 ^ (Nat.digits 10 (m+2).factorial).length ≤ 10 * (m+2).factorial :=
      Nat.base_pow_length_digits_le 10 _ (by norm_num) (Nat.factorial_ne_zero _)
    have h3 : (m+2).factorial ≤ (m+2)^(m+1) := key (m+1)
    set d := (Nat.digits 10 (m+2)).length with hdd
    set L := (Nat.digits 10 (m+2).factorial).length with hL
    have hd : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · rw [h0, pow_zero] at h1; omega
      · exact h0
    have h4 : (m+2)^(m+1) < (10^d)^(m+1) := Nat.pow_lt_pow_left h1 (by omega)
    have h5 : 10^((m+2)*d) ≤ 10^L := Nat.pow_le_pow_right (by norm_num) h
    have h6 : (10^d)^(m+1) * 10 ≤ 10^((m+2)*d) := by
      rw [← pow_mul, show (m+2)*d = d*(m+1) + d by ring, pow_add]
      have : 10^1 ≤ 10^d := Nat.pow_le_pow_right (by norm_num) hd
      exact Nat.mul_le_mul le_rfl (by simpa using this)
    omega
  · intro h
    subst h
    simp [Nat.factorial]
```
