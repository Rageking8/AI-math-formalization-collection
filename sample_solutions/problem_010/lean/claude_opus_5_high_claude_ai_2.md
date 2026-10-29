# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `11 August 2026`\
Line count: `7`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem no_nat_cube_sum_mod_eq (x y : ℕ) :
    (((x^3 + y^3) % 18) % 17) ≠ 15 := by
  rw [Nat.add_mod, Nat.pow_mod, Nat.pow_mod y]
  exact (by decide : ∀ a < 18, ∀ b < 18, ((a ^ 3 % 18 + b ^ 3 % 18) % 18) % 17 ≠ 15)
    _ (x.mod_lt (by omega)) _ (y.mod_lt (by omega))
```
