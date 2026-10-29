# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `11 August 2026`\
Line count: `124`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem primitive_set_arbitrarily_large :
    ∀ n : ℕ, ∃ S : Finset ℕ, S.Nonempty ∧
      (∀ a ∈ S, ∀ b ∈ S, a ∣ b → a = b) ∧
      (S.filter Odd).card = (S.filter Even).card ∧
      (S.filter Odd).sum id = (S.filter Even).sum id ∧
      S.card ≥ n := by
  intro n
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ,
      A = ((Finset.range (n + 1)).image fun j => 8 * n + 8 * j + 11) ∪
          ((Finset.range (n + 1)).image fun j => 8 * n + 8 * j + 13) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset ℕ,
      B = ((Finset.range (n + 1)).image fun j => 8 * n + 8 * j + 10) ∪
          ((Finset.range (n + 1)).image fun j => 8 * n + 8 * j + 14) := ⟨_, rfl⟩
  -- generic facts about the four images
  have hcard_img : ∀ c : ℕ,
      ((Finset.range (n + 1)).image fun j => 8 * n + 8 * j + c).card = n + 1 := by
    intro c
    have hinj : Set.InjOn (fun j : ℕ => 8 * n + 8 * j + c) ↑(Finset.range (n + 1)) := by
      intro x _ y _ hxy
      have h2 : 8 * n + 8 * x + c = 8 * n + 8 * y + c := hxy
      omega
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsum_img : ∀ c : ℕ,
      ((Finset.range (n + 1)).image fun j => 8 * n + 8 * j + c).sum id
        = ∑ j ∈ Finset.range (n + 1), (8 * n + 8 * j + c) := by
    intro c
    have hinj : ∀ x ∈ Finset.range (n + 1), ∀ y ∈ Finset.range (n + 1),
        8 * n + 8 * x + c = 8 * n + 8 * y + c → x = y := by
      intro x _ y _ h
      omega
    exact Finset.sum_image hinj
  have hdisj : ∀ c d : ℕ, (∀ x y : ℕ, 8 * x + c ≠ 8 * y + d) →
      Disjoint ((Finset.range (n + 1)).image fun j => 8 * n + 8 * j + c)
        ((Finset.range (n + 1)).image fun j => 8 * n + 8 * j + d) := by
    intro c d hcd
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_image, Finset.mem_range] at ha ha'
    obtain ⟨x, -, hx⟩ := ha
    obtain ⟨y, -, hy⟩ := ha'
    exact hcd x y (by omega)
  -- parities
  have hAodd : ∀ x ∈ A, Odd x := by
    intro x hx
    rw [hA] at hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx
    rw [Nat.odd_iff]
    rcases hx with ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩ <;> omega
  have hAnotEven : ∀ x ∈ A, ¬ Even x := by
    intro x hx
    rw [hA] at hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx
    rw [Nat.even_iff]
    rcases hx with ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩ <;> omega
  have hBeven : ∀ x ∈ B, Even x := by
    intro x hx
    rw [hB] at hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx
    rw [Nat.even_iff]
    rcases hx with ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩ <;> omega
  have hBnotOdd : ∀ x ∈ B, ¬ Odd x := by
    intro x hx
    rw [hB] at hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx
    rw [Nat.odd_iff]
    rcases hx with ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩ <;> omega
  -- the two filters
  have hfO : (A ∪ B).filter Odd = A := by
    rw [Finset.filter_union, Finset.filter_true_of_mem hAodd,
      Finset.filter_false_of_mem hBnotOdd, Finset.union_empty]
  have hfE : (A ∪ B).filter Even = B := by
    rw [Finset.filter_union, Finset.filter_false_of_mem hAnotEven,
      Finset.filter_true_of_mem hBeven, Finset.empty_union]
  -- cardinalities
  have hcardA : A.card = n + 1 + (n + 1) := by
    rw [hA, Finset.card_union_of_disjoint (hdisj 11 13 (by intro x y; omega)),
      hcard_img, hcard_img]
  have hcardB : B.card = n + 1 + (n + 1) := by
    rw [hB, Finset.card_union_of_disjoint (hdisj 10 14 (by intro x y; omega)),
      hcard_img, hcard_img]
  -- sums
  have hsumA : A.sum id = ∑ j ∈ Finset.range (n + 1), (16 * n + 16 * j + 24) := by
    rw [hA, Finset.sum_union (hdisj 11 13 (by intro x y; omega)), hsum_img, hsum_img,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by omega
  have hsumB : B.sum id = ∑ j ∈ Finset.range (n + 1), (16 * n + 16 * j + 24) := by
    rw [hB, Finset.sum_union (hdisj 10 14 (by intro x y; omega)), hsum_img, hsum_img,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by omega
  -- everything sits in [8n+10, 16n+14]
  have hbound : ∀ x ∈ A ∪ B, 8 * n + 10 ≤ x ∧ x ≤ 16 * n + 14 := by
    intro x hx
    rw [hA, hB] at hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx
    rcases hx with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  have hsub : A ⊆ A ∪ B := by
    intro x hx
    exact Finset.mem_union_left _ hx
  refine ⟨A ∪ B, ?_, ?_, ?_, ?_, ?_⟩
  · have hAne : A.Nonempty := by
      rw [← Finset.card_pos, hcardA]
      omega
    obtain ⟨x, hx⟩ := hAne
    exact ⟨x, Finset.mem_union_left _ hx⟩
  · intro a ha b hb hdvd
    obtain ⟨ha1, ha2⟩ := hbound a ha
    obtain ⟨hb1, hb2⟩ := hbound b hb
    obtain ⟨c, rfl⟩ := hdvd
    have hc0 : c ≠ 0 := by
      rintro rfl
      omega
    have hc1 : c < 2 := by
      by_contra hcon
      push_neg at hcon
      have h1 : a * 2 ≤ a * c := Nat.mul_le_mul (le_refl a) hcon
      omega
    have hc : c = 1 := by omega
    rw [hc, Nat.mul_one]
  · rw [hfO, hfE, hcardA, hcardB]
  · rw [hfO, hfE, hsumA, hsumB]
  · have h1 : A.card ≤ (A ∪ B).card := Finset.card_le_card hsub
    omega
```
