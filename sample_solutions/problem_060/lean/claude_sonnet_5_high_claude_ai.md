# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `54`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem factorial_inequality (n : ℕ) (hn : 0 < n) :
    ((n.factorial.factorial : ℝ) / ((n ^ 2 - 1).factorial : ℝ) < (n : ℝ) ^ (n.factorial + n ^ 3)) ↔
      n = 2 ∨ n = 3 ∨ n = 4 := by
  have key : ∀ n : ℕ, 6 ≤ n → n ^ 3 + 2 * n ^ 2 ≤ n.factorial := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num [Nat.factorial]
    | succ n hn ih =>
      rw [Nat.factorial_succ]
      have h1 : (n + 1) * (n ^ 3 + 2 * n ^ 2) ≤ (n + 1) * n.factorial :=
        Nat.mul_le_mul_left _ ih
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
      nlinarith [h1, Nat.zero_le (m ^ 2), Nat.zero_le (m ^ 3), Nat.zero_le (m ^ 4),
        Nat.zero_le m]
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    obtain ⟨h2, h3, h4⟩ := hne
    have hcases : n = 1 ∨ 5 ≤ n := by omega
    rcases hcases with rfl | h5
    · norm_num [Nat.factorial] at h
    · rcases eq_or_lt_of_le h5 with rfl | h6
      · norm_num [Nat.factorial] at h
      · have hk := key n (by omega)
        have hn1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
        have hk1 : n ^ 2 - 1 + 1 = n ^ 2 := Nat.sub_add_cancel hn1
        have hkm : n ^ 2 - 1 ≤ n.factorial := by omega
        have h1 : (n ^ 2 - 1).factorial * (n ^ 2 - 1 + 1) ^ (n.factorial - (n ^ 2 - 1))
            ≤ n.factorial.factorial := by
          have := Nat.factorial_mul_pow_le_factorial (m := n ^ 2 - 1)
            (n := n.factorial - (n ^ 2 - 1))
          rwa [Nat.add_sub_of_le hkm] at this
        rw [hk1, ← pow_mul] at h1
        have hexp : n.factorial + n ^ 3 ≤ 2 * (n.factorial - (n ^ 2 - 1)) := by
          omega
        have hnat : n ^ (n.factorial + n ^ 3) * (n ^ 2 - 1).factorial
            ≤ n.factorial.factorial := by
          calc n ^ (n.factorial + n ^ 3) * (n ^ 2 - 1).factorial
              ≤ n ^ (2 * (n.factorial - (n ^ 2 - 1))) * (n ^ 2 - 1).factorial :=
                Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hn hexp)
            _ = (n ^ 2 - 1).factorial * n ^ (2 * (n.factorial - (n ^ 2 - 1))) :=
                mul_comm _ _
            _ ≤ n.factorial.factorial := h1
        have hreal : (n : ℝ) ^ (n.factorial + n ^ 3) * ((n ^ 2 - 1).factorial : ℝ)
            ≤ (n.factorial.factorial : ℝ) := by
          exact_mod_cast hnat
        have hB : (0 : ℝ) < ((n ^ 2 - 1).factorial : ℝ) := by
          exact_mod_cast Nat.factorial_pos _
        rw [div_lt_iff₀ hB] at h
        linarith
  · rintro (rfl | rfl | rfl) <;> norm_num [Nat.factorial]
```
