# Claude Opus 5 Low (Arena AI)

Model: `claude-opus-5-low` (via Arena AI)\
Date: `31 July 2026`\
Line count: `15`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_nat_cube_sum_mod_eq (x y : ℕ) :
    (((x^3 + y^3) % 18) % 17) ≠ 15 := by
  have h : (x^3 + y^3) % 18 = ((x % 18)^3 + (y % 18)^3) % 18 := by
    conv_lhs => rw [Nat.add_mod, Nat.pow_mod, Nat.pow_mod y]
    rw [← Nat.add_mod]
  rw [h]
  have hx : x % 18 < 18 := Nat.mod_lt _ (by norm_num)
  have hy : y % 18 < 18 := Nat.mod_lt _ (by norm_num)
  revert hx hy
  generalize x % 18 = a
  generalize y % 18 = b
  intro hx hy
  interval_cases a <;> interval_cases b <;> decide
```
