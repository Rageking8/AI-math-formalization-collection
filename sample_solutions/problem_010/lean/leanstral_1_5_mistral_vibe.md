# Leanstral 1.5 (Mistral Vibe)

Model: `Leanstral 1.5` (via Mistral Vibe)\
Date: `31 July 2026`\
Line count: `17`\
Turn count: `Not applicable`

## Solution

```lean4
import Mathlib

theorem no_nat_cube_sum_mod_eq (x y : ℕ) :
    (((x^3 + y^3) % 18) % 17) ≠ 15 := by
  -- brute-force check all 18×18 residues modulo 18
  have h_cases : ∀ (a b : Fin 18), (((a.val ^ 3 + b.val ^ 3) % 18) % 17) ≠ 15 := by
    decide
  have hx : x ≡ x % 18 [MOD 18] := (Nat.mod_modEq x 18).symm
  have hy : y ≡ y % 18 [MOD 18] := (Nat.mod_modEq y 18).symm
  have hsum : x ^ 3 + y ^ 3 ≡ (x % 18) ^ 3 + (y % 18) ^ 3 [MOD 18] := (hx.pow 3).add (hy.pow 3)
  rw [Nat.ModEq] at hsum
  rw [hsum]
  have ha : x % 18 < 18 := Nat.mod_lt x (by norm_num)
  have hb : y % 18 < 18 := Nat.mod_lt y (by norm_num)
  let a : Fin 18 := ⟨x % 18, ha⟩
  let b : Fin 18 := ⟨y % 18, hb⟩
  simpa using h_cases a b
```
