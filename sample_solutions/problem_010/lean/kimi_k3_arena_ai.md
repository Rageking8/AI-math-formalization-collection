# Kimi K3 (Arena AI)

Model: `kimi-k3` (via Arena AI)\
Date: `31 July 2026`\
Line count: `19`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_nat_cube_sum_mod_eq (x y : ℕ) :
    (((x^3 + y^3) % 18) % 17) ≠ 15 := by
  -- Cubes mod 18 can only be 0, 1, 8, 9, 10 or 17
  have key : ∀ n : ℕ, n ^ 3 % 18 = 0 ∨ n ^ 3 % 18 = 1 ∨ n ^ 3 % 18 = 8 ∨
      n ^ 3 % 18 = 9 ∨ n ^ 3 % 18 = 10 ∨ n ^ 3 % 18 = 17 := by
    intro n
    rw [Nat.pow_mod]   -- reduce to (n % 18)^3 % 18
    obtain ⟨k, hk, hnk⟩ : ∃ k, k < 18 ∧ n % 18 = k :=
      ⟨n % 18, Nat.mod_lt n (show 0 < 18 by norm_num), rfl⟩
    rw [hnk]
    interval_cases k <;> decide
  -- Split (x^3 + y^3) % 18 into the residues of each cube
  rw [Nat.add_mod]
  -- 36 cases, each a concrete arithmetic fact
  rcases key x with hx|hx|hx|hx|hx|hx <;>
    rcases key y with hy|hy|hy|hy|hy|hy <;>
    rw [hx, hy] <;> decide
```
