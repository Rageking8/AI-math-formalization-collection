# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `16 September 2026`\
Line count: `188`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem primitive_set_arbitrarily_large :
    ∀ n : ℕ, ∃ S : Finset ℕ, S.Nonempty ∧
      (∀ a ∈ S, ∀ b ∈ S, a ∣ b → a = b) ∧
      (S.filter Odd).card = (S.filter Even).card ∧
      (S.filter Odd).sum id = (S.filter Even).sum id ∧
      S.card ≥ n := by
  have helper : ∀ m : ℕ, 1 ≤ m → ∃ S : Finset ℕ, S.Nonempty ∧
      (∀ a ∈ S, ∀ b ∈ S, a ∣ b → a = b) ∧
      (S.filter Odd).card = (S.filter Even).card ∧
      (S.filter Odd).sum id = (S.filter Even).sum id ∧
      S.card = 4 * m := by
    intro m hm
    set C := 8 * m with hCdef
    set O1 : Finset ℕ := (Finset.range m).image (fun i => C - (2 * i + 1)) with hO1def
    set O2 : Finset ℕ := (Finset.range m).image (fun i => C + (2 * i + 1)) with hO2def
    set E1 : Finset ℕ := (Finset.range m).image (fun i => C - (2 * i + 2)) with hE1def
    set E2 : Finset ℕ := (Finset.range m).image (fun i => C + (2 * i + 2)) with hE2def
    set O : Finset ℕ := O1 ∪ O2 with hOdef
    set E : Finset ℕ := E1 ∪ E2 with hEdef
    set S : Finset ℕ := O ∪ E with hSdef
    have genCard : ∀ (f : ℕ → ℕ), (∀ x < m, ∀ y < m, f x = f y → x = y) →
        ((Finset.range m).image f).card = m := by
      intro f hf
      have hinj : Set.InjOn f ↑(Finset.range m) := by
        intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_range] at hx hy
        exact hf x hx y hy hxy
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have genSum : ∀ (f : ℕ → ℕ), (∀ x < m, ∀ y < m, f x = f y → x = y) →
        ((Finset.range m).image f).sum id = ∑ i ∈ Finset.range m, f i := by
      intro f hf
      have hinj : ∀ x ∈ Finset.range m, ∀ y ∈ Finset.range m, f x = f y → x = y := by
        intro x hx y hy hxy
        simp only [Finset.mem_range] at hx hy
        exact hf x hx y hy hxy
      simp [Finset.sum_image hinj]
    have genMem : ∀ (f : ℕ → ℕ) (x : ℕ), x ∈ (Finset.range m).image f ↔ ∃ i < m, f i = x := by
      intro f x
      simp only [Finset.mem_image, Finset.mem_range]
    have hf1 : ∀ x < m, ∀ y < m, (C - (2 * x + 1)) = (C - (2 * y + 1)) → x = y := by
      intro x hx y hy hxy; omega
    have hf2 : ∀ x < m, ∀ y < m, (C + (2 * x + 1)) = (C + (2 * y + 1)) → x = y := by
      intro x hx y hy hxy; omega
    have hf3 : ∀ x < m, ∀ y < m, (C - (2 * x + 2)) = (C - (2 * y + 2)) → x = y := by
      intro x hx y hy hxy; omega
    have hf4 : ∀ x < m, ∀ y < m, (C + (2 * x + 2)) = (C + (2 * y + 2)) → x = y := by
      intro x hx y hy hxy; omega
    have hO1card : O1.card = m := genCard (fun i => C - (2 * i + 1)) hf1
    have hO2card : O2.card = m := genCard (fun i => C + (2 * i + 1)) hf2
    have hE1card : E1.card = m := genCard (fun i => C - (2 * i + 2)) hf3
    have hE2card : E2.card = m := genCard (fun i => C + (2 * i + 2)) hf4
    have hO1sum : O1.sum id = ∑ i ∈ Finset.range m, (C - (2 * i + 1)) :=
      genSum (fun i => C - (2 * i + 1)) hf1
    have hO2sum : O2.sum id = ∑ i ∈ Finset.range m, (C + (2 * i + 1)) :=
      genSum (fun i => C + (2 * i + 1)) hf2
    have hE1sum : E1.sum id = ∑ i ∈ Finset.range m, (C - (2 * i + 2)) :=
      genSum (fun i => C - (2 * i + 2)) hf3
    have hE2sum : E2.sum id = ∑ i ∈ Finset.range m, (C + (2 * i + 2)) :=
      genSum (fun i => C + (2 * i + 2)) hf4
    have hO1mem : ∀ x, x ∈ O1 ↔ ∃ i < m, C - (2 * i + 1) = x := genMem (fun i => C - (2 * i + 1))
    have hO2mem : ∀ x, x ∈ O2 ↔ ∃ i < m, C + (2 * i + 1) = x := genMem (fun i => C + (2 * i + 1))
    have hE1mem : ∀ x, x ∈ E1 ↔ ∃ i < m, C - (2 * i + 2) = x := genMem (fun i => C - (2 * i + 2))
    have hE2mem : ∀ x, x ∈ E2 ↔ ∃ i < m, C + (2 * i + 2) = x := genMem (fun i => C + (2 * i + 2))
    have hO1O2disj : Disjoint O1 O2 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨i, hi, hxi⟩ := (hO1mem x).mp hx1
      obtain ⟨j, hj, hxj⟩ := (hO2mem x).mp hx2
      omega
    have hE1E2disj : Disjoint E1 E2 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨i, hi, hxi⟩ := (hE1mem x).mp hx1
      obtain ⟨j, hj, hxj⟩ := (hE2mem x).mp hx2
      omega
    have hOodd : ∀ x ∈ O, Odd x := by
      intro x hx
      rw [hOdef, Finset.mem_union] at hx
      rcases hx with hx | hx
      · obtain ⟨i, hi, hxi⟩ := (hO1mem x).mp hx
        rw [Nat.odd_iff]; omega
      · obtain ⟨i, hi, hxi⟩ := (hO2mem x).mp hx
        rw [Nat.odd_iff]; omega
    have hEeven : ∀ x ∈ E, Even x := by
      intro x hx
      rw [hEdef, Finset.mem_union] at hx
      rcases hx with hx | hx
      · obtain ⟨i, hi, hxi⟩ := (hE1mem x).mp hx
        rw [Nat.even_iff]; omega
      · obtain ⟨i, hi, hxi⟩ := (hE2mem x).mp hx
        rw [Nat.even_iff]; omega
    have hOEdisj : Disjoint O E := by
      rw [Finset.disjoint_left]
      intro x hxO hxE
      have h1 := hOodd x hxO
      have h2 := hEeven x hxE
      rw [Nat.odd_iff] at h1
      rw [Nat.even_iff] at h2
      omega
    have hOcard : O.card = 2 * m := by
      rw [hOdef]
      have h := Finset.card_union_add_card_inter O1 O2
      rw [Finset.disjoint_iff_inter_eq_empty.mp hO1O2disj, Finset.card_empty] at h
      omega
    have hEcard : E.card = 2 * m := by
      rw [hEdef]
      have h := Finset.card_union_add_card_inter E1 E2
      rw [Finset.disjoint_iff_inter_eq_empty.mp hE1E2disj, Finset.card_empty] at h
      omega
    have hScard : S.card = 4 * m := by
      rw [hSdef]
      have h := Finset.card_union_add_card_inter O E
      rw [Finset.disjoint_iff_inter_eq_empty.mp hOEdisj, Finset.card_empty] at h
      omega
    have hsumO : O.sum id = 2 * C * m := by
      rw [hOdef, Finset.sum_union hO1O2disj, hO1sum, hO2sum, ← Finset.sum_add_distrib]
      have hpt : ∀ i ∈ Finset.range m, (C - (2 * i + 1)) + (C + (2 * i + 1)) = 2 * C := by
        intro i hi
        simp only [Finset.mem_range] at hi
        omega
      rw [Finset.sum_congr rfl hpt]
      simp [Finset.sum_const, Finset.card_range, mul_comm]
    have hsumE : E.sum id = 2 * C * m := by
      rw [hEdef, Finset.sum_union hE1E2disj, hE1sum, hE2sum, ← Finset.sum_add_distrib]
      have hpt : ∀ i ∈ Finset.range m, (C - (2 * i + 2)) + (C + (2 * i + 2)) = 2 * C := by
        intro i hi
        simp only [Finset.mem_range] at hi
        omega
      rw [Finset.sum_congr rfl hpt]
      simp [Finset.sum_const, Finset.card_range, mul_comm]
    have hOfilterOdd : O.filter Odd = O := Finset.filter_true_of_mem hOodd
    have hEfilterOdd : E.filter Odd = ∅ := Finset.filter_false_of_mem (by
      intro x hx
      have heven := hEeven x hx
      rw [Nat.even_iff] at heven
      rw [Nat.odd_iff]
      omega)
    have hOfilterEven : O.filter Even = ∅ := Finset.filter_false_of_mem (by
      intro x hx
      have hodd := hOodd x hx
      rw [Nat.odd_iff] at hodd
      rw [Nat.even_iff]
      omega)
    have hEfilterEven : E.filter Even = E := Finset.filter_true_of_mem hEeven
    have hSfilterOdd : S.filter Odd = O := by
      rw [hSdef, Finset.filter_union, hOfilterOdd, hEfilterOdd, Finset.union_empty]
    have hSfilterEven : S.filter Even = E := by
      rw [hSdef, Finset.filter_union, hOfilterEven, hEfilterEven, Finset.empty_union]
    have hSbound : ∀ x ∈ S, 6 * m ≤ x ∧ x ≤ 10 * m := by
      intro x hx
      simp only [hSdef, hOdef, hEdef, Finset.mem_union] at hx
      rcases hx with (hx | hx) | (hx | hx)
      · obtain ⟨i, hi, hxi⟩ := (hO1mem x).mp hx; omega
      · obtain ⟨i, hi, hxi⟩ := (hO2mem x).mp hx; omega
      · obtain ⟨i, hi, hxi⟩ := (hE1mem x).mp hx; omega
      · obtain ⟨i, hi, hxi⟩ := (hE2mem x).mp hx; omega
    have hSne : S.Nonempty := by
      obtain ⟨x, hx⟩ := Finset.nonempty_range_iff.mpr (show m ≠ 0 by omega)
      refine ⟨C - (2 * x + 1), ?_⟩
      rw [hSdef, hOdef]
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [hO1def]
      exact Finset.mem_image_of_mem _ hx
    have hanti : ∀ a ∈ S, ∀ b ∈ S, a ∣ b → a = b := by
      intro a ha b hb hdvd
      by_contra hne
      obtain ⟨ha1, ha2⟩ := hSbound a ha
      obtain ⟨hb1, hb2⟩ := hSbound b hb
      obtain ⟨k, hk⟩ := hdvd
      have hk0 : k ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hk; omega
      have hk1 : k ≠ 1 := by
        intro h1; rw [h1, mul_one] at hk; exact hne hk.symm
      have hk2 : 2 ≤ k := by omega
      have hk' : k = 2 + (k - 2) := by omega
      have hba : a * 2 ≤ b := by
        rw [hk, hk', mul_add]
        exact Nat.le_add_right _ _
      omega
    refine ⟨S, hSne, hanti, ?_, ?_, hScard⟩
    · rw [hSfilterOdd, hSfilterEven, hOcard, hEcard]
    · rw [hSfilterOdd, hSfilterEven, hsumO, hsumE]
  intro n
  obtain ⟨S, hSne, hanti, hcard, hsum, hScard⟩ := helper (n + 1) (by omega)
  exact ⟨S, hSne, hanti, hcard, hsum, by omega⟩
```
