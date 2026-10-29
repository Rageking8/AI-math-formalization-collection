# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `28 July 2026`\
Line count: `120`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem exists_polynomial_with_k_digit_sum_solutions (k : ℕ) :
    ∃ (P : Polynomial ℝ), ∃ (S : Finset ℕ), S.card = k ∧
      ∀ (n : ℕ), n ∈ S ↔ (n : ℝ) = P.eval ((Nat.digits 10 n).sum : ℝ) := by
  classical
  obtain ⟨N, hdig⟩ : ∃ N : ℕ → ℕ, ∀ i, Nat.digits 10 (N i) = List.replicate i 9 := by
    refine ⟨fun i => Nat.ofDigits 10 (List.replicate i 9), fun i => ?_⟩
    show Nat.digits 10 (Nat.ofDigits 10 (List.replicate i 9)) = List.replicate i 9
    refine Nat.digits_ofDigits 10 (by norm_num) _ (fun l hl => ?_) (fun h => ?_)
    · rw [List.eq_of_mem_replicate hl]; norm_num
    · rw [List.eq_of_mem_replicate (List.getLast_mem h)]; norm_num
  have hsumrep : ∀ i : ℕ, (List.replicate i 9).sum = 9 * i := by
    intro i
    induction i with
    | zero => simp
    | succ j ih => rw [List.replicate_succ, List.sum_cons, ih]; ring
  have hsum : ∀ i, (Nat.digits 10 (N i)).sum = 9 * i := fun i => by
    rw [hdig i, hsumrep i]
  have hinj : Function.Injective N := by
    intro i j hij
    have h : List.replicate i 9 = List.replicate j 9 := by rw [← hdig i, ← hdig j, hij]
    simpa using congrArg List.length h
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℚ, ∀ i < k, Q.eval ((9 * i : ℕ) : ℚ) = (N i : ℚ) := by
    induction k with
    | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    | succ m ih =>
      obtain ⟨Q, hQ⟩ := ih
      have hWeval : ∀ x : ℚ,
          (∏ i ∈ Finset.range m, (Polynomial.X - Polynomial.C ((9 * i : ℕ) : ℚ))).eval x
            = ∏ i ∈ Finset.range m, (x - ((9 * i : ℕ) : ℚ)) := by
        intro x
        simp [Polynomial.eval_prod]
      have hWm : (∏ i ∈ Finset.range m,
          (Polynomial.X - Polynomial.C ((9 * i : ℕ) : ℚ))).eval ((9 * m : ℕ) : ℚ) ≠ 0 := by
        rw [hWeval]
        refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
        rw [Finset.mem_range] at hi
        have h2 : (9 * m : ℕ) ≠ (9 * i : ℕ) := by omega
        have h1 : ((9 * m : ℕ) : ℚ) ≠ ((9 * i : ℕ) : ℚ) := by exact_mod_cast h2
        exact sub_ne_zero_of_ne h1
      obtain ⟨c, hc⟩ : ∃ c : ℚ, c * (∏ i ∈ Finset.range m,
          (Polynomial.X - Polynomial.C ((9 * i : ℕ) : ℚ))).eval ((9 * m : ℕ) : ℚ)
            = (N m : ℚ) - Q.eval ((9 * m : ℕ) : ℚ) := by
        refine ⟨((N m : ℚ) - Q.eval ((9 * m : ℕ) : ℚ)) /
          (∏ i ∈ Finset.range m,
            (Polynomial.X - Polynomial.C ((9 * i : ℕ) : ℚ))).eval ((9 * m : ℕ) : ℚ), ?_⟩
        rw [div_mul_eq_mul_div, mul_div_assoc, div_self hWm, mul_one]
      refine ⟨Q + Polynomial.C c *
        ∏ i ∈ Finset.range m, (Polynomial.X - Polynomial.C ((9 * i : ℕ) : ℚ)), ?_⟩
      intro i hi
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
      · have hz : (∏ j ∈ Finset.range m,
            (Polynomial.X - Polynomial.C ((9 * j : ℕ) : ℚ))).eval ((9 * i : ℕ) : ℚ) = 0 := by
          rw [hWeval]
          exact Finset.prod_eq_zero (Finset.mem_range.mpr h) (sub_self _)
        rw [Polynomial.eval_add, Polynomial.eval_mul, hz, mul_zero, add_zero, hQ i h]
      · subst h
        rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hc]
        ring
  obtain ⟨P, hPdef⟩ : ∃ P : Polynomial ℝ, P = Q.map (Rat.castHom ℝ)
      + Polynomial.C (Real.sqrt 2) *
        ∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C ((9 * i : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hmapeval : ∀ d : ℕ,
      (Q.map (Rat.castHom ℝ)).eval (d : ℝ) = ((Q.eval (d : ℚ) : ℚ) : ℝ) := by
    intro d
    have h1 : (d : ℝ) = (Rat.castHom ℝ) ((d : ℚ)) := by simp
    rw [h1, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    simp
  have hPeval : ∀ d : ℕ, P.eval (d : ℝ)
      = ((Q.eval (d : ℚ) : ℚ) : ℝ)
        + Real.sqrt 2 * ∏ i ∈ Finset.range k, ((d : ℝ) - ((9 * i : ℕ) : ℝ)) := by
    intro d
    rw [hPdef]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, hmapeval d]
  refine ⟨P, (Finset.range k).image N, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  · intro n
    constructor
    · intro hn
      rw [Finset.mem_image] at hn
      obtain ⟨i, hi, rfl⟩ := hn
      rw [Finset.mem_range] at hi
      rw [hsum i, hPeval (9 * i)]
      have hzero : ∏ j ∈ Finset.range k, (((9 * i : ℕ) : ℝ) - ((9 * j : ℕ) : ℝ)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr hi) (sub_self _)
      rw [hzero, mul_zero, add_zero, hQ i hi]
      norm_cast
    · intro hn
      obtain ⟨d, hd⟩ : ∃ d : ℕ, (Nat.digits 10 n).sum = d := ⟨_, rfl⟩
      rw [hd, hPeval d] at hn
      by_cases hprod : ∏ i ∈ Finset.range k, ((d : ℝ) - ((9 * i : ℕ) : ℝ)) = 0
      · rw [hprod, mul_zero, add_zero] at hn
        rw [Finset.prod_eq_zero_iff] at hprod
        obtain ⟨i, hi, hzi⟩ := hprod
        rw [Finset.mem_range] at hi
        have hdi : d = 9 * i := by
          have h2 : (d : ℝ) = ((9 * i : ℕ) : ℝ) := by linarith
          exact_mod_cast h2
        subst hdi
        rw [hQ i hi] at hn
        have hni : n = N i := by exact_mod_cast hn
        rw [Finset.mem_image]
        exact ⟨i, Finset.mem_range.mpr hi, hni.symm⟩
      · exfalso
        obtain ⟨M, hM⟩ : ∃ M : ℤ, ((M : ℤ) : ℝ)
            = ∏ i ∈ Finset.range k, ((d : ℝ) - ((9 * i : ℕ) : ℝ)) := by
          refine ⟨∏ i ∈ Finset.range k, ((d : ℤ) - ((9 * i : ℕ) : ℤ)), ?_⟩
          rw [Int.cast_prod]
          exact Finset.prod_congr rfl fun i _ => by
            rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
        have hM0 : ((M : ℤ) : ℝ) ≠ 0 := by rw [hM]; exact hprod
        rw [← hM] at hn
        have hmem : Real.sqrt 2 ∈ Set.range ((↑) : ℚ → ℝ) := by
          refine ⟨((n : ℚ) - Q.eval (d : ℚ)) / (M : ℚ), ?_⟩
          push_cast
          rw [div_eq_iff hM0, hn]
          ring
        exact irrational_sqrt_two hmem
```
