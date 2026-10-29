# Gemini 3.1 Pro Preview (Arena AI)

Model: `gemini-3.1-pro-preview` (via Arena AI)\
Date: `26 July 2026`\
Line count: `13`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_nat_cube_sum_mod_eq (x y : ℕ) :
    (((x^3 + y^3) % 18) % 17) ≠ 15 := by
  have hx : Nat.ModEq 18 (x % 18) x := Nat.mod_mod x 18
  have hy : Nat.ModEq 18 (y % 18) y := Nat.mod_mod y 18
  have hxy : ((x % 18)^3 + (y % 18)^3) % 18 = (x^3 + y^3) % 18 :=
    (hx.pow 3).add (hy.pow 3)
  rw [← hxy]
  have ha : x % 18 < 18 := by omega
  have hb : y % 18 < 18 := by omega
  have h_all : ∀ (a b : Fin 18), (((a.val^3 + b.val^3) % 18) % 17) ≠ 15 := by decide
  exact h_all ⟨x % 18, ha⟩ ⟨y % 18, hb⟩
```
