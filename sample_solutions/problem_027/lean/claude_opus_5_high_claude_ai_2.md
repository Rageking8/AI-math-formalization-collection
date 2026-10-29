# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `18 August 2026`\
Line count: `13`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem no_nat_satisfies_congruence :
    ¬ ∃ n : ℕ, (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) % 65 = 5 := by
  rintro ⟨n, h⟩
  have b := Nat.pow_mod n 4 5
  have c : ∀ m, 29 ^ m % 5 = 1 ∨ 29 ^ m % 5 = 4 := by
    intro m; induction m with
    | zero => simp
    | succ k ih => rw [pow_succ]; omega
  have := c n
  rcases (by omega : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4)
    with e | e | e | e | e <;> rw [e] at b <;> norm_num at b <;> omega
```
