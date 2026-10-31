# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `3 September 2026`\
Line count: `14`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem no_nat_cube_sum_mod_eq (x y : ℕ) :
    (((x^3 + y^3) % 18) % 17) ≠ 15 := by
  have h1 : x ^ 3 % 18 = (x % 18) ^ 3 % 18 := Nat.pow_mod x 3 18
  have h2 : y ^ 3 % 18 = (y % 18) ^ 3 % 18 := Nat.pow_mod y 3 18
  have key : (x ^ 3 + y ^ 3) % 18 = ((x % 18) ^ 3 + (y % 18) ^ 3) % 18 := by
    rw [Nat.add_mod, h1, h2, ← Nat.add_mod]
  rw [key]
  have hx : x % 18 < 18 := Nat.mod_lt x (by norm_num)
  have hy : y % 18 < 18 := Nat.mod_lt y (by norm_num)
  set a := x % 18 with ha_def
  set b := y % 18 with hb_def
  interval_cases a <;> interval_cases b <;> decide
```
