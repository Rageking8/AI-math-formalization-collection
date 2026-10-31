# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `3 September 2026`\
Line count: `109`\
Turn count: `1`

## Solution

```lean4
import Mathlib

/- Auxiliary pair sequence: pellPair n = (a n, a (n+1)) where a 0 = 1, a 1 = 2,
   a (n+2) = 3 * a (n+1) - a n.  These satisfy a n ^ 2 - 3 * a n * a (n+1) + a (n+1) ^ 2 = -1,
   which (via z = x + y) gives infinitely many solutions of the original equation. -/
def pellPair : ℕ → ℤ × ℤ
  | 0 => (1, 2)
  | (n + 1) => ((pellPair n).2, 3 * (pellPair n).2 - (pellPair n).1)

def pellA (n : ℕ) : ℤ := (pellPair n).1

lemma pellA_rec (n : ℕ) : pellA (n + 1 + 1) = 3 * pellA (n + 1) - pellA n := rfl

lemma pellA_pos_lt (n : ℕ) : 0 < pellA n ∧ pellA n < pellA (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    obtain ⟨hpos, hlt⟩ := ih
    refine ⟨by linarith, ?_⟩
    rw [pellA_rec k]
    linarith

lemma pellA_pos (n : ℕ) : 0 < pellA n := (pellA_pos_lt n).1
lemma pellA_lt (n : ℕ) : pellA n < pellA (n + 1) := (pellA_pos_lt n).2

lemma pellA_invariant (n : ℕ) :
    pellA n ^ 2 + pellA (n + 1) ^ 2 + 1 = 3 * pellA n * pellA (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    rw [pellA_rec k]
    linear_combination ih

def pellX (n : ℕ) : ℕ := (pellA n).toNat

lemma pellX_cast (n : ℕ) : (pellX n : ℤ) = pellA n :=
  Int.toNat_of_nonneg (pellA_pos n).le

lemma pellX_pos (n : ℕ) : 0 < pellX n := by
  have h := pellA_pos n
  have hc := pellX_cast n
  have h2 : (0 : ℤ) < (pellX n : ℤ) := by rw [hc]; exact h
  exact_mod_cast h2

lemma pellX_lt (n : ℕ) : pellX n < pellX (n + 1) := by
  have h := pellA_lt n
  have hc1 := pellX_cast n
  have hc2 := pellX_cast (n + 1)
  have h2 : (pellX n : ℤ) < (pellX (n + 1) : ℤ) := by rw [hc1, hc2]; exact h
  exact_mod_cast h2

lemma pellX_strictMono : StrictMono pellX := strictMono_nat_of_lt_succ pellX_lt

lemma pellX_injective : Function.Injective pellX := pellX_strictMono.injective

lemma pellX_invariant_Q (n : ℕ) :
    (pellX n : ℚ) ^ 2 + (pellX (n + 1) : ℚ) ^ 2 + 1
      = 3 * (pellX n : ℚ) * (pellX (n + 1) : ℚ) := by
  have h := pellA_invariant n
  have e1 : (pellX n : ℚ) = (pellA n : ℚ) := by exact_mod_cast pellX_cast n
  have e2 : (pellX (n + 1) : ℚ) = (pellA (n + 1) : ℚ) := by exact_mod_cast pellX_cast (n + 1)
  rw [e1, e2]
  exact_mod_cast h

lemma pell_mem_solution_set (n : ℕ) :
    (pellX n, pellX (n + 1), pellX n + pellX (n + 1)) ∈
      { (x, y, z) : ℕ × ℕ × ℕ |
        0 < x ∧ 0 < y ∧ 0 < z ∧
        ((z : ℚ) ^ 2 / ((x : ℚ) + (y : ℚ))) + (z : ℚ) =
        (((x : ℚ) ^ 2 + 1) / (y : ℚ)) + (((y : ℚ) ^ 2 + 1) / (x : ℚ)) } := by
  have hxn : 0 < pellX n := pellX_pos n
  have hxn1 : 0 < pellX (n + 1) := pellX_pos (n + 1)
  refine ⟨hxn, hxn1, by omega, ?_⟩
  have hX0 : (pellX n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hxn.ne'
  have hY0 : (pellX (n + 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hxn1.ne'
  have hXpos : (0 : ℚ) < (pellX n : ℚ) := by exact_mod_cast hxn
  have hYpos : (0 : ℚ) < (pellX (n + 1) : ℚ) := by exact_mod_cast hxn1
  have hXYpos : (0 : ℚ) < (pellX n : ℚ) + (pellX (n + 1) : ℚ) := by linarith
  have hXY0 : (pellX n : ℚ) + (pellX (n + 1) : ℚ) ≠ 0 := hXYpos.ne'
  have hxyQ := pellX_invariant_Q n
  have step1a : ((pellX n : ℚ) + (pellX (n + 1) : ℚ)) ^ 2 / ((pellX n : ℚ) + (pellX (n + 1) : ℚ))
      = (pellX n : ℚ) + (pellX (n + 1) : ℚ) := by
    rw [div_eq_iff hXY0]; ring
  have step1 : ((pellX n : ℚ) + (pellX (n + 1) : ℚ)) ^ 2 / ((pellX n : ℚ) + (pellX (n + 1) : ℚ))
      + ((pellX n : ℚ) + (pellX (n + 1) : ℚ)) = 2 * ((pellX n : ℚ) + (pellX (n + 1) : ℚ)) := by
    rw [step1a]; ring
  have step2 : ((pellX n : ℚ) ^ 2 + 1) / (pellX (n + 1) : ℚ)
      + ((pellX (n + 1) : ℚ) ^ 2 + 1) / (pellX n : ℚ)
      = 2 * ((pellX n : ℚ) + (pellX (n + 1) : ℚ)) := by
    rw [div_add_div _ _ hY0 hX0, div_eq_iff (mul_ne_zero hY0 hX0)]
    linear_combination ((pellX n : ℚ) + (pellX (n + 1) : ℚ)) * hxyQ
  push_cast
  rw [step1, step2]

theorem infinite_solutions_z2_x_y_z :
    Set.Infinite { (x, y, z) : ℕ × ℕ × ℕ |
      0 < x ∧ 0 < y ∧ 0 < z ∧
      ((z : ℚ) ^ 2 / ((x : ℚ) + (y : ℚ))) + (z : ℚ) =
      (((x : ℚ) ^ 2 + 1) / (y : ℚ)) + (((y : ℚ) ^ 2 + 1) / (x : ℚ)) } := by
  have hinj : Function.Injective (fun n => (pellX n, pellX (n + 1), pellX n + pellX (n + 1))) := by
    intro n m h
    simp only [Prod.mk.injEq] at h
    exact pellX_injective h.1
  have hrange : (Set.range (fun n => (pellX n, pellX (n + 1), pellX n + pellX (n + 1)))).Infinite :=
    Set.infinite_range_of_injective hinj
  apply hrange.mono
  intro p hp
  obtain ⟨n, rfl⟩ := hp
  exact pell_mem_solution_set n
```
