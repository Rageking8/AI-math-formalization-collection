# Claude Opus 5 Low (Arena AI)

Model: `claude-opus-5-low` (via Arena AI)\
Date: `8 August 2026`\
Line count: `23`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_nat_satisfies_congruence :
    ¬ ∃ n : ℕ, (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) % 65 = 5 := by
  rintro ⟨n, hn⟩
  have key : ∀ m : ℕ, 29 ^ m % 5 = 1 ∨ 29 ^ m % 5 = 4 := by
    intro m
    induction m with
    | zero => left; rfl
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> decide
  have h1 := key n
  have h2 : n ^ 4 % 5 = 0 ∨ n ^ 4 % 5 = 1 := by
    rw [Nat.pow_mod]
    have h : ∀ r, r < 5 → r ^ 4 % 5 = 0 ∨ r ^ 4 % 5 = 1 := by decide
    exact h (n % 5) (Nat.mod_lt _ (by norm_num))
  have h5 : (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) % 5 = 0 := by
    have h := Nat.mod_mod_of_dvd (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3)
      (by norm_num : (5:ℕ) ∣ 65)
    rw [hn] at h
    omega
  omega
```
