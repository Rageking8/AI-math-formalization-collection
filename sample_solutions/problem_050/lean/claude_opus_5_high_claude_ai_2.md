# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `1 September 2026`\
Line count: `77`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

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
  have key : ∀ m c d : ℕ,
      ∑ i ∈ Finset.range m, (c + d * i) = m * c + d * ∑ i ∈ Finset.range m, i := by
    intro m c d
    induction m with
    | zero => simp
    | succ p ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; ring
  have hT : ∀ m : ℕ, ∑ i ∈ Finset.range (2 * m + 2), i = (2 * m + 1) * (m + 1) := by
    intro m
    induction m with
    | zero => first | rfl | decide | simp
    | succ p ih =>
      rw [show 2 * (p + 1) + 2 = 2 * p + 2 + 1 + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, ih]; ring
  have hiO : Function.Injective fun i : ℕ => 10 * n + 9 + 2 * i := by
    intro a b h; first | omega | (simp only [add_right_inj] at h; omega)
  have hiE : Function.Injective fun i : ℕ => 8 * n + 8 + 4 * i := by
    intro a b h; first | omega | (simp only [add_right_inj] at h; omega)
  obtain ⟨O, hO⟩ : ∃ O : Finset ℕ,
      O = (Finset.range (2 * n + 2)).image fun i => 10 * n + 9 + 2 * i := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Finset ℕ,
      E = (Finset.range (2 * n + 2)).image fun i => 8 * n + 8 + 4 * i := ⟨_, rfl⟩
  have hO1 : ∀ x ∈ O, x % 2 = 1 := by
    intro x hx
    simp only [hO, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, -, rfl⟩ := hx; omega
  have hE0 : ∀ x ∈ E, x % 2 = 0 := by
    intro x hx
    simp only [hE, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, -, rfl⟩ := hx; omega
  have hOy : ∀ x ∈ O, Odd x := fun x hx => Nat.odd_iff.mpr (hO1 x hx)
  have hEy : ∀ x ∈ E, Even x := fun x hx => Nat.even_iff.mpr (hE0 x hx)
  have hEno : ∀ x ∈ E, ¬ Odd x := fun x hx => by rw [Nat.odd_iff, hE0 x hx]; omega
  have hOne : ∀ x ∈ O, ¬ Even x := fun x hx => by rw [Nat.even_iff, hO1 x hx]; omega
  have hfO : (O ∪ E).filter Odd = O := by
    rw [Finset.filter_union, Finset.filter_true_of_mem hOy,
      Finset.filter_false_of_mem hEno, Finset.union_empty]
  have hfE : (O ∪ E).filter Even = E := by
    rw [Finset.filter_union, Finset.filter_false_of_mem hOne,
      Finset.filter_true_of_mem hEy, Finset.empty_union]
  have hOc : O.card = 2 * n + 2 := by
    rw [hO, Finset.card_image_of_injective _ hiO, Finset.card_range]
  have hEc : E.card = 2 * n + 2 := by
    rw [hE, Finset.card_image_of_injective _ hiE, Finset.card_range]
  have hsO : O.sum id = ∑ i ∈ Finset.range (2 * n + 2), (10 * n + 9 + 2 * i) := by
    rw [hO, Finset.sum_image fun a _ b _ h => hiO h]; try simp
  have hsE : E.sum id = ∑ i ∈ Finset.range (2 * n + 2), (8 * n + 8 + 4 * i) := by
    rw [hE, Finset.sum_image fun a _ b _ h => hiE h]; try simp
  have hle : O.card ≤ (O ∪ E).card :=
    Finset.card_le_card fun x hx => Finset.mem_union_left _ hx
  have hbd : ∀ x ∈ O ∪ E, 8 * n + 8 ≤ x ∧ x ≤ 16 * n + 12 := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · simp only [hO, Finset.mem_image, Finset.mem_range] at h
      obtain ⟨i, hi, rfl⟩ := h; omega
    · simp only [hE, Finset.mem_image, Finset.mem_range] at h
      obtain ⟨i, hi, rfl⟩ := h; omega
  refine ⟨O ∪ E, Finset.card_pos.mp (by omega), ?_,
    by rw [hfO, hfE, hOc, hEc], ?_, by omega⟩
  · intro a ha b hb hab
    obtain ⟨ha1, -⟩ := hbd a ha
    obtain ⟨hb1, hb2⟩ := hbd b hb
    obtain ⟨c, hc⟩ := hab
    rcases Nat.lt_or_ge c 2 with h2 | h2
    · have : c = 0 ∨ c = 1 := by omega
      rcases this with rfl | rfl <;> omega
    · have h3 : a * 2 ≤ a * c := Nat.mul_le_mul (le_refl a) h2
      rw [← hc] at h3; omega
  · rw [hfO, hfE, hsO, hsE, key, key, hT n]; ring
```
