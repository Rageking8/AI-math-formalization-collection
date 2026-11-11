# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `11 November 2026`\
Line count: `49`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def S (n : ℕ) : ℕ :=
  Nat.ofDigits 10 ((Nat.digits 10 n).mergeSort (· ≤ ·))

theorem infinite_solutions_s_eq_two_n :
    Set.Infinite { n : ℕ | 0 < n ∧ S n = 2 * n } := by
  -- The family n = 10^k * 438271605 works: S n = 10^k * 876543210.
  have key : ∀ k : ℕ, S (10 ^ k * 438271605) = 2 * (10 ^ k * 438271605) := by
    intro k
    have hd : Nat.digits 10 (10 ^ k * 438271605)
        = List.replicate k 0 ++ [5, 0, 6, 1, 7, 2, 8, 3, 4] := by
      rw [Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
      norm_num
    have hsort : (List.replicate k 0 ++ [5, 0, 6, 1, 7, 2, 8, 3, 4]).mergeSort
          (fun a b : ℕ => decide (a ≤ b))
        = List.replicate k 0 ++ [0, 1, 2, 3, 4, 5, 6, 7, 8] := by
      apply List.Perm.eq_of_pairwise (le := fun a b : ℕ => decide (a ≤ b) = true)
      · intro a b _ _ hab hba
        simp only [decide_eq_true_eq] at hab hba
        exact le_antisymm hab hba
      · apply List.pairwise_mergeSort
        · intro a b c hab hbc
          simp only [decide_eq_true_eq] at hab hbc ⊢
          exact le_trans hab hbc
        · intro a b
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact le_total a b
      · rw [List.pairwise_append]
        refine ⟨?_, by decide, ?_⟩
        · rw [List.pairwise_replicate]
          right
          simp
        · intro a ha b _
          rw [List.eq_of_mem_replicate ha]
          simp
      · refine (List.mergeSort_perm _ _).trans ?_
        exact List.Perm.append_left _ (by decide)
    unfold S
    rw [hd, hsort, Nat.ofDigits_append, Nat.ofDigits_replicate_zero, List.length_replicate]
    norm_num [Nat.ofDigits]
    ring
  have hinj : Function.Injective (fun k : ℕ => 10 ^ k * 438271605) := by
    intro a b hab
    have h : (10 : ℕ) ^ a = 10 ^ b := Nat.eq_of_mul_eq_mul_right (by norm_num) hab
    exact Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num)) h
  refine Set.infinite_of_injective_forall_mem hinj ?_
  intro k
  exact ⟨by positivity, key k⟩
```
