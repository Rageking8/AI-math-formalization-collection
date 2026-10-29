# Claude Opus 5 Low (Claude AI)

Model: `Claude Opus 5 Low` (via Claude AI)\
Date: `30 July 2026`\
Line count: `9`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_nat_cube_sum_mod_eq (x y : ℕ) :
    (((x^3 + y^3) % 18) % 17) ≠ 15 := by
  have key : ∀ a < 18, ∀ b < 18, ((a ^ 3 + b ^ 3) % 18) % 17 ≠ 15 := by decide
  have h : (x ^ 3 + y ^ 3) % 18 = ((x % 18) ^ 3 + (y % 18) ^ 3) % 18 := by
    conv_lhs => rw [Nat.add_mod, Nat.pow_mod, Nat.pow_mod y, ← Nat.add_mod]
  rw [h]
  exact key _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))
```
