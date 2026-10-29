# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `22 August 2026`\
Line count: `128`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem ten_digit_median_distinct_digits_le_seven
    (n m : ℕ) (h_digits_len : (Nat.digits 10 n).length = 10)
      (h_no_zero : 0 ∉ Nat.digits 10 n)
      (h_median :
        let s := (Nat.digits 10 n).mergeSort (· ≤ ·)
        s[4]! + s[5]! = 2 * m)
      (h_distinct : (Nat.digits 10 n).toFinset.card = m) : m ≤ 7 := by
  -- `Pairwise (· ≤ ·)` gives monotone indexing.  Proved from scratch so that it
  -- does not depend on `List.Sorted` or on `List.pairwise_iff_getElem`.
  have mono : ∀ l : List ℕ, List.Pairwise (· ≤ ·) l →
      ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≤ j → l[i] ≤ l[j] := by
    intro l
    induction l with
    | nil =>
      intro _ i j hi
      first
        | simp at hi
        | exact absurd hi (by simp)
    | cons a t ih =>
      intro hp i j hi hj hij
      rw [List.pairwise_cons] at hp
      obtain ⟨ha, ht⟩ := hp
      cases i with
      | zero =>
        cases j with
        | zero => exact le_refl _
        | succ j =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ]
          first
            | exact ha _ (List.getElem_mem _)
            | exact ha _ (List.getElem_mem ..)
            | exact ha _ (by simp)
      | succ i =>
        cases j with
        | zero => exact absurd hij (by omega)
        | succ j =>
          simp only [List.getElem_cons_succ]
          have hi' : i < t.length := by simp only [List.length_cons] at hi; omega
          have hj' : j < t.length := by simp only [List.length_cons] at hj; omega
          exact ih ht i j hi' hj' (by omega)
  have main : ∀ s : List ℕ, s.Perm (Nat.digits 10 n) → List.Pairwise (· ≤ ·) s →
      s[4]! + s[5]! = 2 * m → m ≤ 7 := by
    intro s hperm hsorted hmed
    have hlen : s.length = 10 := by rw [hperm.length_eq]; exact h_digits_len
    have h4 : 4 < s.length := by omega
    have h5 : 5 < s.length := by omega
    have e4 : s[4]! = s[4]'h4 := by
      first
        | exact getElem!_pos s 4 h4
        | simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h4]
    have e5 : s[5]! = s[5]'h5 := by
      first
        | exact getElem!_pos s 5 h5
        | simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h5]
    rw [e4, e5] at hmed
    have hpairle : ∀ (i j : ℕ) (hi : i < s.length) (hj : j < s.length), i ≤ j → s[i] ≤ s[j] :=
      mono s hsorted
    have hle : s[4]'h4 ≤ s[5]'h5 := hpairle 4 5 h4 h5 (by omega)
    have hTF : s.toFinset = (Nat.digits 10 n).toFinset := by
      ext x
      simp only [List.mem_toFinset]
      exact hperm.mem_iff
    have hsplit : s.toFinset = (s.take 5).toFinset ∪ (s.drop 5).toFinset := by
      ext x
      simp only [Finset.mem_union, List.mem_toFinset]
      rw [← List.mem_append, List.take_append_drop]
    have hcard1 : (s.take 5).toFinset.card ≤ 5 := by
      have hA : (s.take 5).toFinset.card ≤ (s.take 5).length := by
        first
          | exact List.toFinset_card_le _
          | (rw [List.card_toFinset]; exact (List.dedup_sublist _).length_le)
      have hB : (s.take 5).length ≤ 5 := by
        first
          | (simp only [List.length_take]; omega)
          | (simp <;> omega)
          | omega
      omega
    have hdropge : ∀ x ∈ s.drop 5, s[5]'h5 ≤ x := by
      intro x hx
      have hlen2 : (s.drop 5).length = s.length - 5 := by simp
      obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.mp hx
      rw [← hxj]
      first
        | (simp only [List.getElem_drop]; apply hpairle <;> omega)
        | (simp; apply hpairle <;> omega)
        | (apply hpairle <;> omega)
    have hsub : (s.drop 5).toFinset ⊆ Finset.Icc (s[5]'h5) 9 := by
      intro x hx
      rw [List.mem_toFinset] at hx
      rw [Finset.mem_Icc]
      refine ⟨hdropge x hx, ?_⟩
      have hxs : x ∈ Nat.digits 10 n := by
        apply hperm.mem_iff.mp
        first
          | exact List.mem_of_mem_drop hx
          | exact List.drop_subset _ _ hx
          | exact List.drop_subset _ hx
      have hlt : x < 10 := Nat.digits_lt_base (by norm_num) hxs
      omega
    have hcard2 := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard2
    have hcard3 : s.toFinset.card ≤ (s.take 5).toFinset.card + (s.drop 5).toFinset.card := by
      rw [hsplit]
      exact Finset.card_union_le _ _
    rw [hTF, h_distinct] at hcard3
    omega
  refine main ((Nat.digits 10 n).mergeSort (· ≤ ·)) ?_ ?_ h_median
  · first
      | exact List.mergeSort_perm ..
      | exact (List.mergeSort_perm ..).symm
      | exact List.perm_mergeSort ..
      | exact (List.perm_mergeSort ..).symm
  · first
      | exact List.sorted_mergeSort' _
      | exact List.sorted_mergeSort' ..
      | exact List.pairwise_mergeSort' _
      | exact List.pairwise_mergeSort' ..
      | simpa using List.sorted_mergeSort' _
      | simpa using List.pairwise_mergeSort' _
      | exact List.pairwise_mergeSort
          (by intros; simp_all <;> omega) (by intros; simp_all <;> omega) _
      | simpa using List.pairwise_mergeSort
          (by intros; simp_all <;> omega) (by intros; simp_all <;> omega) _
      | exact List.mergeSort_sorted _
      | simpa using List.mergeSort_sorted _
      | exact?
```
