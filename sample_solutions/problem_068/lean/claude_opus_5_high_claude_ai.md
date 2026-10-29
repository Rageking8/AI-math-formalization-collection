# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `20 August 2026`\
Line count: `162`\
Turn count: `5`

## Solution

```lean4
import Mathlib

def S (n : ℕ) : ℕ :=
  Nat.ofDigits 10 ((Nat.digits 10 n).mergeSort (· ≤ ·))

theorem infinite_solutions_s_eq_two_n :
    Set.Infinite { n : ℕ | 0 < n ∧ S n = 2 * n } := by
  classical
  -- `mergeSort` produces a sorted list
  have hsort : ∀ L : List ℕ, List.Pairwise (· ≤ ·) (L.mergeSort (· ≤ ·)) := by
    intro L
    first
      | exact List.pairwise_mergeSort ..
      | exact List.mergeSort_sorted ..
      | exact List.mergeSort_pairwise ..
      | exact List.sorted_mergeSort_le ..
      | exact List.mergeSort_sorted_le ..
      | exact List.pairwise_mergeSort_le ..
      | (apply List.pairwise_mergeSort <;> intros <;> simp_all <;> omega)
      | (apply List.mergeSort_sorted <;> intros <;> simp_all <;> omega)
      | (apply List.mergeSort_pairwise <;> intros <;> simp_all <;> omega)
      | simp
      | exact?
  -- `mergeSort` produces a permutation
  have hperm : ∀ L : List ℕ, (L.mergeSort (· ≤ ·)).Perm L := by
    intro L
    first
      | exact List.mergeSort_perm ..
      | exact List.mergeSort_perm L _
      | exact List.mergeSort_perm _ L
      | exact List.perm_mergeSort ..
  -- a sorted list is determined by its multiset of entries (proved by hand)
  have uniq : ∀ l₁ l₂ : List ℕ, l₁.Perm l₂ → l₁.Pairwise (· ≤ ·) → l₂.Pairwise (· ≤ ·) →
      l₁ = l₂ := by
    intro l₁
    induction l₁ with
    | nil =>
      intro l₂ hp _ _
      cases l₂ with
      | nil => rfl
      | cons b s => have hlen := hp.length_eq; simp at hlen
    | cons a t ih =>
      intro l₂ hp h1 h2
      cases l₂ with
      | nil => have hlen := hp.length_eq; simp at hlen
      | cons b s =>
        have hmem1 : a ∈ b :: s := hp.mem_iff.mp (by simp)
        have hmem2 : b ∈ a :: t := hp.mem_iff.mpr (by simp)
        rw [List.pairwise_cons] at h1 h2
        have hab : a ≤ b := by
          rcases List.mem_cons.mp hmem2 with h | h
          · exact le_of_eq h.symm
          · exact h1.1 b h
        have hba : b ≤ a := by
          rcases List.mem_cons.mp hmem1 with h | h
          · exact le_of_eq h.symm
          · exact h2.1 a h
        have hEq : a = b := le_antisymm hab hba
        subst hEq
        have hts : t.Perm s := by
          first
            | exact hp.cons_inv
            | exact List.Perm.cons_inv hp
            | exact (List.perm_cons a).mp hp
        rw [ih s hts h1.2 h2.2]
  -- digits of `4938271605 * 10 ^ j`
  have hdig : ∀ j : ℕ, Nat.digits 10 (4938271605 * 10 ^ j)
      = List.replicate j 0 ++ [5, 0, 6, 1, 7, 2, 8, 3, 9, 4] := by
    intro j
    induction j with
    | zero =>
      have h0 : (4938271605 : ℕ) * 10 ^ 0 = 4938271605 := by norm_num
      rw [h0]
      simp only [List.replicate_zero, List.nil_append]
      first
        | norm_num
        | decide
        | simp
    | succ k ih =>
      have hpos : 0 < 10 * (4938271605 * 10 ^ k) := by positivity
      have h1 : (4938271605 : ℕ) * 10 ^ (k + 1) = 10 * (4938271605 * 10 ^ k) := by ring
      have h2 : 10 * (4938271605 * 10 ^ k) % 10 = 0 := by
        first
          | omega
          | simp
          | exact Nat.mul_mod_right _ _
      have h3 : 10 * (4938271605 * 10 ^ k) / 10 = 4938271605 * 10 ^ k := by
        first
          | omega
          | simp
          | exact Nat.mul_div_cancel_left _ (by norm_num)
      rw [h1, Nat.digits_def' (by norm_num : (1 : ℕ) < 10) hpos, h2, h3, ih,
        List.replicate_succ, List.cons_append]
  -- `ofDigits` ignores the low zeros, up to a factor `10 ^ j`
  have hof : ∀ (j : ℕ) (L : List ℕ),
      Nat.ofDigits 10 (List.replicate j 0 ++ L) = 10 ^ j * Nat.ofDigits 10 L := by
    intro j
    induction j with
    | zero => intro L; simp
    | succ k ih =>
      intro L
      rw [List.replicate_succ, List.cons_append, Nat.ofDigits_cons, ih]
      first
        | (push_cast; ring)
        | ring
        | (simp; ring)
        | simp
  -- the target list is sorted
  have htarget : ∀ j : ℕ,
      List.Pairwise (· ≤ ·) ((List.replicate j 0 ++ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List ℕ)) := by
    intro j
    induction j with
    | zero =>
      simp only [List.replicate_zero, List.nil_append]
      first
        | decide
        | simp
        | norm_num [List.pairwise_cons]
    | succ k ih =>
      rw [List.replicate_succ, List.cons_append, List.pairwise_cons]
      exact ⟨fun b _ => Nat.zero_le b, ih⟩
  -- the main computation
  have key : ∀ j : ℕ, S (4938271605 * 10 ^ j) = 2 * (4938271605 * 10 ^ j) := by
    intro j
    have hSdef : S (4938271605 * 10 ^ j)
        = Nat.ofDigits 10 ((Nat.digits 10 (4938271605 * 10 ^ j)).mergeSort (· ≤ ·)) := rfl
    have hpd : ([5, 0, 6, 1, 7, 2, 8, 3, 9, 4] : List ℕ).Perm [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
      first
        | decide
        | (rw [← List.isPerm_iff]; decide)
        | simp [List.perm_iff_count, List.count_cons]
    have hp : (((List.replicate j 0 ++ [5, 0, 6, 1, 7, 2, 8, 3, 9, 4] : List ℕ)).mergeSort
        (· ≤ ·)).Perm (List.replicate j 0 ++ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]) :=
      (hperm _).trans (List.Perm.append_left _ hpd)
    have hms : (Nat.digits 10 (4938271605 * 10 ^ j)).mergeSort (· ≤ ·)
        = List.replicate j 0 ++ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
      rw [hdig j]
      exact uniq _ _ hp (hsort _) (htarget j)
    have hval : Nat.ofDigits 10 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] = 9876543210 := by
      first
        | norm_num [Nat.ofDigits_cons, Nat.ofDigits_nil]
        | norm_num [Nat.ofDigits]
        | simp [Nat.ofDigits]
        | rfl
        | decide
    rw [hSdef, hms, hof j, hval]
    ring
  -- the family is infinite
  have hinj : Function.Injective (fun j : ℕ => 4938271605 * 10 ^ j) := by
    intro a b hab
    have hab' : (4938271605 : ℕ) * 10 ^ a = 4938271605 * 10 ^ b := hab
    have h10 : (10 : ℕ) ^ a = 10 ^ b := Nat.eq_of_mul_eq_mul_left (by norm_num) hab'
    exact Nat.pow_right_injective (by norm_num) h10
  have hmem : ∀ j : ℕ, (4938271605 * 10 ^ j) ∈ { n : ℕ | 0 < n ∧ S n = 2 * n } := by
    intro j
    have hp : 0 < 4938271605 * 10 ^ j := by positivity
    exact ⟨hp, key j⟩
  first
    | exact Set.infinite_of_injective_forall_mem hinj hmem
    | exact (Set.infinite_range_of_injective hinj).mono (by rintro _ ⟨j, rfl⟩; exact hmem j)
    | exact Set.Infinite.mono (by rintro _ ⟨j, rfl⟩; exact hmem j)
        (Set.infinite_range_of_injective hinj)
```
