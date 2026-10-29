# Claude Fable 5 (Arena AI)

Model: `claude-fable-5` (via Arena AI)\
Date: `8 August 2026`\
Line count: `18`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_nat_satisfies_congruence :
    ¬ ∃ n : ℕ, (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) % 65 = 5 := by
  rintro ⟨n, hn⟩
  have key : (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) % 5 = 0 := by omega
  have h1 : ((29 : ℕ) ^ 2) ^ (n / 2) % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hA : 29 ^ n % 5 = 29 ^ (n % 2) % 5 := by
    conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul]
    rw [Nat.mul_mod, h1, one_mul]
    omega
  have hB : n ^ 4 % 5 = (n % 5) ^ 4 % 5 := Nat.pow_mod n 4 5
  have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have h5 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases h2 with h2 | h2 <;> rcases h5 with h5 | h5 | h5 | h5 | h5 <;>
      rw [h2] at hA <;> rw [h5] at hB <;> norm_num at hA hB <;> omega
```
