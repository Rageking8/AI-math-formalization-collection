# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `11 August 2026`\
Line count: `27`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem no_distinct_irreducible_two_over_n_sum :
    ¬ ∃ (S : Finset ℕ), (∀ n ∈ S, n > 0 ∧ Nat.Coprime 2 n) ∧
      (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) = 5 / 121 := by
  have K : ∀ T : Finset ℕ, (∀ n ∈ T, ¬2 ∣ n) →
      ∃ k m : ℕ, ¬2 ∣ m ∧ ∑ n ∈ T, (2:ℚ)/(n:ℚ) = 2 * k / m := by
    intro T; induction T using Finset.induction with
    | empty => exact fun _ => ⟨0, 1, by omega, by simp⟩
    | @insert a T ha ih =>
      intro h
      obtain ⟨k, m, hm, hq⟩ := ih fun n hn => h n (Finset.mem_insert_of_mem hn)
      have hA := h a (Finset.mem_insert_self a T)
      have h1 : (a:ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have h2 : (m:ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      refine ⟨m + k * a, a * m, fun d => (Nat.prime_two.dvd_mul.1 d).elim hA hm, ?_⟩
      rw [Finset.sum_insert ha, hq]
      push_cast
      field_simp
      all_goals ring
  rintro ⟨S, hS, h⟩
  obtain ⟨k, m, hm, hq⟩ := K S fun n hn => Nat.prime_two.coprime_iff_not_dvd.1 (hS n hn).2
  rw [h] at hq
  have h2 : (m:ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have e : (5:ℚ) * m = 242 * k := by field_simp at hq; linarith
  have : 5 * m = 242 * k := by exact_mod_cast e
  omega
```
