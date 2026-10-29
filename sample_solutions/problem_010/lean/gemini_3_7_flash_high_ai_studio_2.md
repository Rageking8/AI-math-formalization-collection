# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `28 August 2026`\
Line count: `14`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem no_nat_cube_sum_mod_eq (x y : ℕ) :
    (((x^3 + y^3) % 18) % 17) ≠ 15 := by
  have hx : x^3 % 18 = (x % 18)^3 % 18 := Nat.pow_mod x 3 18
  have hy : y^3 % 18 = (y % 18)^3 % 18 := Nat.pow_mod y 3 18
  have hx_lt : x % 18 < 18 := Nat.mod_lt x (by decide)
  have hy_lt : y % 18 < 18 := Nat.mod_lt y (by decide)
  rw [Nat.add_mod, hx, hy, ← Nat.add_mod]
  revert hx_lt hy_lt
  generalize x % 18 = a
  generalize y % 18 = b
  intro ha hb
  interval_cases a <;> interval_cases b <;> decide
```
