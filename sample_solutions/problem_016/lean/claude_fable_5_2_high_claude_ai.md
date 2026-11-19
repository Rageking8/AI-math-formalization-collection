# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `15 November 2026`\
Line count: `88`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem exists_polynomial_with_k_digit_sum_solutions (k : ℕ) :
    ∃ (P : Polynomial ℝ), ∃ (S : Finset ℕ), S.card = k ∧
      ∀ (n : ℕ), n ∈ S ↔ (n : ℝ) = P.eval ((Nat.digits 10 n).sum : ℝ) := by
  classical
  -- every i is the digit sum of some number (the repunit 11…1)
  have hex : ∀ i : ℕ, ∃ m : ℕ, (Nat.digits 10 m).sum = i := by
    intro i
    induction i with
    | zero => exact ⟨0, by simp⟩
    | succ j ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨10 * m + 1, ?_⟩
      have h1 : (10 * m + 1) % 10 = 1 := by omega
      have h2 : (10 * m + 1) / 10 = m := by omega
      rw [Nat.digits_def' (b := 10) (n := 10 * m + 1) (by norm_num) (by omega),
        h1, h2, List.sum_cons, hm]
      omega
  choose f hf using hex
  have hinj : Function.Injective f := fun a b h => by
    rw [← hf a, ← hf b, h]
  -- rational interpolation: Q(i) = f i for i < k
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℚ, ∀ i, i < k → Q.eval (i : ℚ) = (f i : ℚ) := by
    refine ⟨Lagrange.interpolate (Finset.range k) (fun i : ℕ => (i : ℚ))
      (fun i => (f i : ℚ)), fun i hi => ?_⟩
    exact Lagrange.eval_interpolate_at_node (v := fun i : ℕ => (i : ℚ))
      (r := fun i => (f i : ℚ))
      (fun a _ b _ h => Nat.cast_injective h) (Finset.mem_range.mpr hi)
  -- P = Q + √2 · ∏_{i<k} (X - i)
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℝ, ∀ s : ℕ, P.eval (s : ℝ) =
      ((Q.eval (s : ℚ) : ℚ) : ℝ) +
        Real.sqrt 2 * ((∏ i ∈ Finset.range k, ((s : ℚ) - (i : ℚ)) : ℚ) : ℝ) := by
    refine ⟨Q.map (algebraMap ℚ ℝ) + Polynomial.C (Real.sqrt 2) *
      ∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C (i : ℝ)), fun s => ?_⟩
    have key : (Q.map (algebraMap ℚ ℝ)).eval (s : ℝ) = ((Q.eval (s : ℚ) : ℚ) : ℝ) := by
      have hc : (s : ℝ) = algebraMap ℚ ℝ (s : ℚ) :=
        (map_natCast (algebraMap ℚ ℝ) s).symm
      rw [hc, Polynomial.eval_map, Polynomial.eval₂_at_apply]
      simp
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, key]
    simp [Polynomial.eval_prod]
  -- a natural number is never rational + √2 · (nonzero rational)
  have hirr : ∀ (a b : ℚ) (m : ℕ), b ≠ 0 →
      (m : ℝ) ≠ (a : ℝ) + Real.sqrt 2 * (b : ℝ) := by
    intro a b m hb h
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    refine irrational_sqrt_two ⟨((m : ℚ) - a) / b, ?_⟩
    push_cast
    rw [div_eq_iff hb']
    linarith
  refine ⟨P, (Finset.range k).image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  · intro n
    obtain ⟨s, hs⟩ : ∃ s, s = (Nat.digits 10 n).sum := ⟨_, rfl⟩
    rw [← hs]
    by_cases hsk : s < k
    · have hz : (∏ i ∈ Finset.range k, ((s : ℚ) - (i : ℚ))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr hsk) (sub_self _)
      have hval : P.eval (s : ℝ) = (f s : ℝ) := by
        rw [hP, hz, hQ s hsk]
        simp
      rw [hval, Nat.cast_inj]
      constructor
      · intro hn
        obtain ⟨i, hi, hin⟩ := Finset.mem_image.mp hn
        have h1 : s = i := by rw [hs, ← hin, hf]
        rw [h1]
        exact hin.symm
      · intro hn
        exact Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hsk, hn.symm⟩
    · have hk : k ≤ s := Nat.le_of_not_lt hsk
      have hnz : (∏ i ∈ Finset.range k, ((s : ℚ) - (i : ℚ))) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i hi
        have h1 : i < s := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
        have h2 : (i : ℚ) < (s : ℚ) := by exact_mod_cast h1
        exact sub_ne_zero.mpr h2.ne'
      constructor
      · intro hn
        exfalso
        obtain ⟨i, hi, hin⟩ := Finset.mem_image.mp hn
        have h1 : s = i := by rw [hs, ← hin, hf]
        have h2 := Finset.mem_range.mp hi
        omega
      · intro hn
        rw [hP] at hn
        exact absurd hn (hirr _ _ n hnz)
```
