# Claude Opus 5.5 High (Claude AI)

Model: `Claude Opus 5.5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `74`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem exists_polynomial_with_k_digit_sum_solutions (k : ℕ) :
    ∃ (P : Polynomial ℝ), ∃ (S : Finset ℕ), S.card = k ∧
      ∀ (n : ℕ), n ∈ S ↔ (n : ℝ) = P.eval ((Nat.digits 10 n).sum : ℝ) := by
  classical
  obtain ⟨f, hsf⟩ : ∃ f : ℕ → ℕ, ∀ a, (Nat.digits 10 (f a)).sum = a := by
    refine ⟨fun a => Nat.ofDigits 10 (List.replicate a 1), fun a => ?_⟩
    have h : Nat.digits 10 (Nat.ofDigits 10 (List.replicate a 1)) = List.replicate a 1 := by
      refine Nat.digits_ofDigits 10 (by norm_num) _ ?_ ?_
      · intro l hl
        rw [List.eq_of_mem_replicate hl]; norm_num
      · intro h
        rw [List.eq_of_mem_replicate (List.getLast_mem h)]; norm_num
    show (Nat.digits 10 (Nat.ofDigits 10 (List.replicate a 1))).sum = a
    rw [h]; simp
  have hfinj : Function.Injective f := fun a b h => by rw [← hsf a, ← hsf b, h]
  obtain ⟨R, hR⟩ : ∃ R : Polynomial ℚ, ∀ a ∈ Finset.range k, R.eval (a : ℚ) = (f a : ℚ) := by
    refine ⟨Lagrange.interpolate (Finset.range k) (fun a : ℕ => (a : ℚ)) (fun a => (f a : ℚ)), ?_⟩
    intro a ha
    have hinj : Set.InjOn (fun a : ℕ => (a : ℚ)) (Finset.range k : Set ℕ) := by
      intro x _ y _ h
      simpa using h
    exact Lagrange.eval_interpolate_at_node (fun a => (f a : ℚ)) hinj ha
  obtain ⟨N, hN⟩ : ∃ N : Polynomial ℚ, ∀ x : ℚ,
      N.eval x = ∏ a ∈ Finset.range k, (x - (a : ℚ)) :=
    ⟨∏ a ∈ Finset.range k, (Polynomial.X - Polynomial.C (a : ℚ)),
      fun x => by simp [Polynomial.eval_prod]⟩
  have key : ∀ (p : Polynomial ℚ) (x : ℚ),
      (p.map (algebraMap ℚ ℝ)).eval (x : ℝ) = ((p.eval x : ℚ) : ℝ) := by
    intro p x
    rw [Polynomial.eval_map]
    first
      | exact Polynomial.eval₂_at_apply (algebraMap ℚ ℝ) x
      | exact Polynomial.eval₂_hom (algebraMap ℚ ℝ) x
      | simp [Polynomial.eval₂_at_apply]
  refine ⟨R.map (algebraMap ℚ ℝ) + Polynomial.C (Real.sqrt 2) * N.map (algebraMap ℚ ℝ),
    (Finset.range k).image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hfinj, Finset.card_range]
  · intro n
    have hP : ∀ m : ℕ, (R.map (algebraMap ℚ ℝ) + Polynomial.C (Real.sqrt 2)
        * N.map (algebraMap ℚ ℝ)).eval (m : ℝ)
        = ((R.eval (m:ℚ) : ℚ) : ℝ) + Real.sqrt 2 * ((N.eval (m:ℚ) : ℚ) : ℝ) := by
      intro m
      have e : ((m : ℚ) : ℝ) = (m : ℝ) := by norm_num
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, ← e, key, key]
    rw [hP]
    constructor
    · intro hn
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
      rw [hsf a, hR a ha, hN]
      have : ∏ b ∈ Finset.range k, ((a:ℚ) - (b:ℚ)) = 0 := Finset.prod_eq_zero ha (by simp)
      rw [this]; simp
    · intro h
      set m := (Nat.digits 10 n).sum with hm
      by_cases hmA : m ∈ Finset.range k
      · have h0 : N.eval (m:ℚ) = 0 := by
          rw [hN]; exact Finset.prod_eq_zero hmA (by simp)
        rw [h0, hR m hmA] at h
        simp at h
        exact Finset.mem_image.mpr ⟨m, hmA, h.symm⟩
      · exfalso
        have hne : N.eval (m:ℚ) ≠ 0 := by
          rw [hN, Finset.prod_ne_zero_iff]
          intro b hb h'
          apply hmA
          have : m = b := by exact_mod_cast sub_eq_zero.mp h'
          rw [this]; exact hb
        have hne' : ((N.eval (m:ℚ) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hne
        have hq : ((((n:ℚ) - R.eval (m:ℚ)) / N.eval (m:ℚ) : ℚ) : ℝ) = Real.sqrt 2 := by
          push_cast
          rw [h, div_eq_iff hne']
          ring
        exact irrational_sqrt_two (Set.mem_range.mpr ⟨_, hq⟩)
```
