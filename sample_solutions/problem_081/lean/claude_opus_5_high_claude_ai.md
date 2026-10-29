# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `26 August 2026`\
Line count: `22`\
Turn count: `1`

## Note

This solution uses `native_decide`.

## Solution

```lean4
import Mathlib

def O (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).filter (· % 2 == 1)).length

def E (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).filter (· % 2 == 0)).length

theorem is_least_pos_int_odd_even_digit_count_eq_1059 :
    IsLeast { n : ℕ | 0 < n ∧ (O (n ^ 2 + n)) ^ 2 =
      3 * O n ∧ E (n ^ 2 - n) = 5 * E n } 1059 := by
  have key : ∀ m ∈ Finset.range 1059,
      ¬(0 < m ∧ (O (m ^ 2 + m)) ^ 2 = 3 * O m ∧ E (m ^ 2 - m) = 5 * E m) := by
    native_decide
  constructor
  · simp only [Set.mem_setOf_eq]
    refine ⟨by norm_num, ?_, ?_⟩ <;> native_decide
  · rintro n hn
    simp only [Set.mem_setOf_eq] at hn
    by_contra hlt
    push_neg at hlt
    exact key n (Finset.mem_range.mpr hlt) hn
```
