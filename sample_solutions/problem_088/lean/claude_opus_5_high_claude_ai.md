# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `3 September 2026`\
Line count: `63`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem diophantine_set_eq :
    { x : ℤ | 0 < x ∧ ∃ (y z : ℤ), 0 < y ∧ 0 < z ∧ x ^ 2 + y ^ 2 + 6 = x * y * z } =
      { x : ℤ | 0 < x ∧ IsSquare (15 * x ^ 2 - 6) } := by
  have key : ∀ n : ℕ, ∀ x y z : ℤ, 0 < x → 0 < y → 0 < z →
      x + y ≤ (n : ℤ) → x ^ 2 + y ^ 2 + 6 = x * y * z → z = 8 := by
    intro n
    induction n with
    | zero =>
      intro x y z hx hy hz hsum heq
      exfalso
      clear heq hz
      omega
    | succ n ih =>
      intro x y z hx hy hz hsum heq
      have hsum' : x + y ≤ (n : ℤ) + 1 := by push_cast at hsum; linarith
      have main : ∀ a b : ℤ, 0 < a → 0 < b → a ≤ b → a + b ≤ (n : ℤ) + 1 →
          a ^ 2 + b ^ 2 + 6 = a * b * z → z = 8 := by
        intro a b ha hb hab hab1 heq'
        have hprod : b * (a * z - b) = a ^ 2 + 6 := by
          linear_combination (-1 : ℤ) * heq'
        have hcpos : 0 < a * z - b := by nlinarith [sq_nonneg a, hprod, hb]
        by_cases hcb : a * z - b < b
        · refine ih a (a * z - b) z ha hcpos hz (by linarith) ?_
          linear_combination heq'
        · push_neg at hcb
          have hb2 : b * b ≤ a * a + 6 := by nlinarith [hprod, hcb, hb]
          have hb1 : b ≤ a + 1 := by
            by_contra hcon
            push_neg at hcon
            have hge : a + 2 ≤ b := by linarith
            have hsq : (a + 2) * (a + 2) ≤ b * b :=
              mul_le_mul hge hge (by linarith) (by linarith)
            linarith
          have hz3 : 3 ≤ z := by
            nlinarith [mul_pos ha hb, sq_nonneg (a - b), heq']
          have h1 : a * a * z ≤ a * b * z :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab ha.le) hz.le
          have h2 : 3 * (a * a) ≤ a * a * z := by nlinarith [mul_pos ha ha, hz3]
          have haa : a * a ≤ 12 := by linarith [h1, h2, heq', hb2]
          have ha3 : a ≤ 3 := by nlinarith [haa, ha]
          have heq2 : a * a + b * b + 6 = a * (b * z) := by linear_combination heq'
          have hcases : (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 2) ∨
              (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 3) ∨ (a = 3 ∧ b = 4) := by omega
          rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
      rcases le_total x y with h | h
      · exact main x y hx hy h hsum' heq
      · exact main y x hy hx h (by linarith) (by linear_combination heq)
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, y, z, hy, hz, heq⟩
    have hcast : ((x + y).toNat : ℤ) = x + y := Int.toNat_of_nonneg (by linarith)
    have hz8 : z = 8 := key (x + y).toNat x y z hx hy hz (le_of_eq hcast.symm) heq
    subst hz8
    exact ⟨hx, y - 4 * x, by linear_combination (-1 : ℤ) * heq⟩
  · rintro ⟨hx, k, hk⟩
    have habs : |k| * |k| = k * k := abs_mul_abs_self k
    have hkn : (0 : ℤ) ≤ |k| := abs_nonneg k
    exact ⟨hx, 4 * x + |k|, 8, by linarith, by norm_num,
      by linear_combination habs - hk⟩
```
