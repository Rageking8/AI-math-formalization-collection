# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `12 August 2026`\
Line count: `52`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

open Polynomial Finset

theorem exists_polynomial_with_k_digit_sum_solutions (k : ℕ) :
    ∃ (P : Polynomial ℝ), ∃ (S : Finset ℕ), S.card = k ∧
      ∀ (n : ℕ), n ∈ S ↔ (n : ℝ) = P.eval ((Nat.digits 10 n).sum : ℝ) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ j, (Nat.digits 10 (f j)).sum = j :=
    ⟨fun j => Nat.ofDigits 10 (List.replicate j 1), fun j => by
      rw [Nat.digits_ofDigits 10 (by norm_num) (List.replicate j 1)
        (fun l hl => by have := List.eq_of_mem_replicate hl; omega)
        (fun h => by have := List.eq_of_mem_replicate (List.getLast_mem h); omega)]
      simp⟩
  have hinj : Function.Injective f := fun a b h => by rw [← hf a, h, hf b]
  obtain ⟨Q, hQ⟩ : ∃ Q : ℚ[X], ∀ i ∈ range k, Q.eval (i : ℚ) = (f i : ℚ) :=
    ⟨Lagrange.interpolate (range k) (fun i : ℕ => (i : ℚ)) (fun i => (f i : ℚ)),
      fun i hi => Lagrange.eval_interpolate_at_node _ (fun a _ b _ h => Nat.cast_injective h) hi⟩
  obtain ⟨R, hR⟩ : ∃ R : ℚ[X], ∀ t : ℕ, R.eval (t : ℚ) = 0 ↔ t ∈ range k :=
    ⟨∏ i ∈ range k, (X - C (i : ℚ)), fun t => by
      rw [eval_prod, Finset.prod_eq_zero_iff]; simp [sub_eq_zero]⟩
  have cast_eval : ∀ (p : ℚ[X]) (x : ℚ),
      (p.map (Rat.castHom ℝ)).eval (x : ℝ) = ((p.eval x : ℚ) : ℝ) := fun p x => by
    simpa [eval_map] using Polynomial.eval₂_at_apply (p := p) (Rat.castHom ℝ) x
  refine ⟨Q.map (Rat.castHom ℝ) + C (Real.sqrt 2) * R.map (Rat.castHom ℝ), (range k).image f,
    by rw [Finset.card_image_of_injective _ hinj, card_range], fun n => ?_⟩
  have key : ∀ t : ℕ, eval ((t : ℕ) : ℝ)
      (Q.map (Rat.castHom ℝ) + C (Real.sqrt 2) * R.map (Rat.castHom ℝ))
      = ((Q.eval (t : ℚ) : ℚ) : ℝ) + Real.sqrt 2 * ((R.eval (t : ℚ) : ℚ) : ℝ) := fun t => by
    rw [eval_add, eval_mul, eval_C, show ((t : ℕ) : ℝ) = (((t : ℕ) : ℚ) : ℝ) by norm_cast,
      cast_eval, cast_eval]
  have main : ∀ t m : ℕ, ((m : ℝ) = ((Q.eval (t : ℚ) : ℚ) : ℝ)
      + Real.sqrt 2 * ((R.eval (t : ℚ) : ℚ) : ℝ)) ↔ (t ∈ range k ∧ m = f t) := by
    intro t m
    constructor
    · intro h
      by_cases ht : t ∈ range k
      · rw [(hR t).2 ht, hQ t ht] at h
        exact ⟨ht, by exact_mod_cast (by rw [h]; simp : (m : ℝ) = ((f t : ℕ) : ℝ))⟩
      · have h0 : ((R.eval (t : ℚ) : ℚ) : ℝ) ≠ 0 := by
          have : R.eval (t : ℚ) ≠ 0 := fun hc => ht ((hR t).1 hc)
          exact_mod_cast this
        exact absurd (irrational_sqrt_two ⟨((m : ℚ) - Q.eval (t : ℚ)) / R.eval (t : ℚ), by
          push_cast; rw [div_eq_iff h0]; linarith⟩) not_false
    · rintro ⟨ht, rfl⟩
      rw [(hR t).2 ht, hQ t ht]; simp
  rw [key, main, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [hf a]
    exact ⟨ha, rfl⟩
  · rintro ⟨ht, hn⟩
    exact ⟨_, ht, hn.symm⟩
```
