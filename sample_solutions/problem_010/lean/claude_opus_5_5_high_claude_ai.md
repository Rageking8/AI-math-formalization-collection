# Claude Opus 5.5 High (Claude AI)

Model: `Claude Opus 5.5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `17`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem no_nat_cube_sum_mod_eq (x y : ℕ) :
    (((x^3 + y^3) % 18) % 17) ≠ 15 := by
  have key : ∀ n : ℕ, n^3 % 18 = 0 ∨ n^3 % 18 = 1 ∨ n^3 % 18 = 8 ∨
      n^3 % 18 = 9 ∨ n^3 % 18 = 10 ∨ n^3 % 18 = 17 := by
    intro n
    rw [Nat.pow_mod]
    have h := Nat.mod_lt n (show 18 > 0 by norm_num)
    generalize n % 18 = r at h ⊢
    interval_cases r <;> first | decide | simp
  intro h
  have hx := key x
  have hy := key y
  generalize x^3 = a at hx h
  generalize y^3 = b at hy h
  omega
```
