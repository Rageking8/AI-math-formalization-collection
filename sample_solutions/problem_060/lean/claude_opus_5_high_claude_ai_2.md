# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `3 September 2026`\
Line count: `61`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

open Nat in
set_option maxRecDepth 100000 in
theorem factorial_inequality (n : ℕ) (hn : 0 < n) :
    ((n.factorial.factorial : ℝ) / ((n ^ 2 - 1).factorial : ℝ) < (n : ℝ) ^ (n.factorial + n ^ 3)) ↔
      n = 2 ∨ n = 3 ∨ n = 4 := by
  have key : ∀ a b : ℕ, a ≤ b → a ! * a ^ (b - a) ≤ b ! := by
    intro a b hb
    induction b, hb using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      calc a ! * a ^ (m + 1 - a) = a ! * a ^ (m - a) * a := by
            rw [show m + 1 - a = m - a + 1 by omega, pow_succ, mul_assoc]
        _ ≤ m ! * (m + 1) := Nat.mul_le_mul ih (by omega)
        _ = (m + 1)! := by rw [Nat.factorial_succ]; ring
  have arith : ∀ F A B : ℕ, A ≤ F → B + 2 * A ≤ F → F + B ≤ 2 + 2 * (F - A) := by
    intro F A B h1 h2; omega
  have lemB : ∀ m : ℕ, 6 ≤ m → m ^ 3 + 2 * m ^ 2 ≤ m ! := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num [Nat.factorial]
    | succ k hk ih =>
      calc (k + 1) ^ 3 + 2 * (k + 1) ^ 2 ≤ (k + 1) * (k ^ 3 + 2 * k ^ 2) := by
            nlinarith [Nat.mul_le_mul hk (le_refl k), Nat.mul_le_mul hk (le_refl (k * k)),
              Nat.mul_le_mul hk (le_refl (k * k * k))]
        _ ≤ (k + 1) * k ! := Nat.mul_le_mul le_rfl ih
        _ = (k + 1)! := (Nat.factorial_succ k).symm
  have bad : ∀ m : ℕ, 5 ≤ m → m ^ (m ! + m ^ 3) * (m ^ 2 - 1)! ≤ (m !)! := by
    intro m hm
    rcases Nat.lt_or_ge m 6 with h6 | h6
    · obtain rfl : m = 5 := by omega
      norm_num [Nat.factorial]
    · have hm0 : 0 < m := by omega
      have hB := lemB m h6
      have hA : m ^ 2 ≤ m ! :=
        le_trans (by linarith [Nat.zero_le (m ^ 3), Nat.zero_le (m ^ 2)]) hB
      have hsub : m ^ 2 - 1 + 1 = m ^ 2 := Nat.sub_add_cancel (Nat.one_le_pow 2 m hm0)
      have h2 : m ^ 2 * (m ^ 2 - 1)! = (m ^ 2)! := by
        conv_rhs => rw [← hsub]
        rw [Nat.factorial_succ, hsub]
      calc m ^ (m ! + m ^ 3) * (m ^ 2 - 1)!
          ≤ m ^ (2 + 2 * (Nat.factorial m - m ^ 2)) * (m ^ 2 - 1)! :=
            Nat.mul_le_mul (Nat.pow_le_pow_right hm0 (arith _ _ _ hA hB)) le_rfl
        _ = m ^ 2 * (m ^ 2 - 1)! * (m ^ 2) ^ (Nat.factorial m - m ^ 2) := by
            rw [pow_add, pow_mul]; ring
        _ = (m ^ 2)! * (m ^ 2) ^ (Nat.factorial m - m ^ 2) := by rw [h2]
        _ ≤ (m !)! := key _ _ hA
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨c2, c3, c4⟩ := hc
    rcases (by omega : n = 1 ∨ 5 ≤ n) with rfl | h5
    · norm_num [Nat.factorial] at h
    · have hp : (0:ℝ) < ((n ^ 2 - 1)! : ℝ) := by exact_mod_cast (n ^ 2 - 1).factorial_pos
      rw [div_lt_iff₀ hp] at h
      have : (n:ℝ) ^ (n ! + n ^ 3) * ((n ^ 2 - 1)! : ℝ) ≤ ((n !)! : ℝ) := by
        exact_mod_cast bad n h5
      linarith
  · rintro (rfl | rfl | rfl) <;> norm_num [Nat.factorial]
```
