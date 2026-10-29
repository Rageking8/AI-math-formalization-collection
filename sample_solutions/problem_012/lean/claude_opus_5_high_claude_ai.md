# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `29 July 2026`\
Line count: `65`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem infinite_solutions_z2_x_y_z :
    Set.Infinite { (x, y, z) : ℕ × ℕ × ℕ |
      0 < x ∧ 0 < y ∧ 0 < z ∧
      ((z : ℚ) ^ 2 / ((x : ℚ) + (y : ℚ))) + (z : ℚ) =
      (((x : ℚ) ^ 2 + 1) / (y : ℚ)) + (((y : ℚ) ^ 2 + 1) / (x : ℚ)) } := by
  obtain ⟨a, b, ha0, hb0, ha, hb⟩ :
      ∃ a b : ℕ → ℕ, a 0 = 1 ∧ b 0 = 1 ∧
        (∀ n, a (n + 1) = a n + b n) ∧ (∀ n, b (n + 1) = a n + 2 * b n) := by
    refine ⟨fun n => (@Nat.rec (fun _ => ℕ × ℕ) (1, 1)
        (fun _ p => (p.1 + p.2, p.1 + 2 * p.2)) n).1,
      fun n => (@Nat.rec (fun _ => ℕ × ℕ) (1, 1)
        (fun _ p => (p.1 + p.2, p.1 + 2 * p.2)) n).2, rfl, rfl, fun n => rfl, fun n => rfl⟩
  have hpos : ∀ n, 0 < a n ∧ 0 < b n := by
    intro n
    induction n with
    | zero => rw [ha0, hb0]; exact ⟨Nat.one_pos, Nat.one_pos⟩
    | succ k ih => rw [ha k, hb k]; omega
  have hinv : ∀ n, ((b n : ℚ)) ^ 2 + 1 = (a n : ℚ) * (b n : ℚ) + (a n : ℚ) ^ 2 := by
    intro n
    induction n with
    | zero => rw [ha0, hb0]; norm_num
    | succ k ih => rw [ha k, hb k]; push_cast; linear_combination ih
  have hmono : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hb' := (hpos n).2
    rw [ha n]
    omega
  have hinj : Function.Injective
      (fun n : ℕ => ((a n, a n + b n, 2 * a n + b n) : ℕ × ℕ × ℕ)) := by
    intro m n hmn
    have h : a m = a n := congrArg Prod.fst hmn
    exact hmono.injective h
  have key : ∀ A B : ℚ, 0 < A → 0 < B → B ^ 2 + 1 = A * B + A ^ 2 →
      (2 * A + B) ^ 2 / (A + (A + B)) + (2 * A + B) =
        (A ^ 2 + 1) / (A + B) + ((A + B) ^ 2 + 1) / A := by
    intro A B hA hB h
    have hA0 : A ≠ 0 := ne_of_gt hA
    have hAB0 : A + B ≠ 0 := ne_of_gt (by linarith : (0:ℚ) < A + B)
    have e1 : (2 * A + B) ^ 2 / (A + (A + B)) = 2 * A + B := by
      rw [show A + (A + B) = 2 * A + B by ring,
        div_eq_iff (ne_of_gt (by linarith : (0:ℚ) < 2 * A + B))]
      ring
    have e2 : (A ^ 2 + 1) / (A + B) + ((A + B) ^ 2 + 1) / A = 2 * (2 * A + B) := by
      rw [div_add_div _ _ hAB0 hA0, div_eq_iff (mul_ne_zero hAB0 hA0)]
      linear_combination (B + 2 * A) * h
    rw [e1, e2]
    ring
  have hsub : Set.range (fun n : ℕ => ((a n, a n + b n, 2 * a n + b n) : ℕ × ℕ × ℕ)) ⊆
      { (x, y, z) : ℕ × ℕ × ℕ |
        0 < x ∧ 0 < y ∧ 0 < z ∧
        ((z : ℚ) ^ 2 / ((x : ℚ) + (y : ℚ))) + (z : ℚ) =
        (((x : ℚ) ^ 2 + 1) / (y : ℚ)) + (((y : ℚ) ^ 2 + 1) / (x : ℚ)) } := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨hA, hB⟩ := hpos n
    have hA' : (0:ℚ) < (a n : ℚ) := by exact_mod_cast hA
    have hB' : (0:ℚ) < (b n : ℚ) := by exact_mod_cast hB
    have hk := key (a n : ℚ) (b n : ℚ) hA' hB' (hinv n)
    simp only [Set.mem_setOf_eq]
    refine ⟨hA, by omega, by omega, ?_⟩
    push_cast
    linear_combination hk
  exact (Set.infinite_range_of_injective hinj).mono hsub
```
