# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `15 November 2026`\
Line count: `38`\
Turn count: `1`

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
  obtain ⟨s, hs⟩ : ∃ s, s = (Nat.digits 10 n).mergeSort (· ≤ ·) := ⟨_, rfl⟩
  have hperm : s.Perm (Nat.digits 10 n) := hs ▸ List.mergeSort_perm _ _
  have hsorted : s.Pairwise (fun a b => decide (a ≤ b) = true) := by
    rw [hs]
    exact List.pairwise_mergeSort (by intro a b c; simp; omega) (by intro a b; simp; omega) _
  have hlen : s.length = 10 := by rw [hperm.length_eq]; exact h_digits_len
  have hlt : ∀ x ∈ s, 1 ≤ x ∧ x ≤ 9 := by
    intro x hx
    have hx' := hperm.mem_iff.mp hx
    have h1 : x < 10 := Nat.digits_lt_base (by norm_num) hx'
    have h2 : x ≠ 0 := fun h => h_no_zero (h ▸ hx')
    omega
  have hcard : s.toFinset.card = m := by
    rw [List.toFinset_eq_of_perm _ _ hperm]; exact h_distinct
  have hmed : s[4]! + s[5]! = 2 * m := hs ▸ h_median
  clear hs hperm h_median h_distinct h_no_zero h_digits_len
  match s, hlen with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9], _ =>
    simp at hmed hsorted hlt
    by_contra hm
    have hsub : [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].toFinset ⊆
        [a0, a1, a2, a3, a4, 8, 9].toFinset := by
      intro x hx
      simp at hx ⊢
      omega
    have h1 := Finset.card_le_card hsub
    have h2 := List.toFinset_card_le [a0, a1, a2, a3, a4, 8, 9]
    simp only [List.length_cons, List.length_nil] at h2
    omega
```
