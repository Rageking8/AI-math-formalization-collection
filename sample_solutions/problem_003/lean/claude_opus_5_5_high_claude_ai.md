# Claude Opus 5.5 High (Claude AI)

Model: `Claude Opus 5.5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `30`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_distinct_irreducible_two_over_n_sum :
    ¬ ∃ (S : Finset ℕ), (∀ n ∈ S, n > 0 ∧ Nat.Coprime 2 n) ∧
      (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) = 5 / 121 := by
  rintro ⟨S, hS, hsum⟩
  obtain ⟨P, hP⟩ : ∃ P, P = ∏ n ∈ S, n := ⟨_, rfl⟩
  have hcop : Nat.Coprime 2 P := by
    rw [hP]
    exact Nat.Coprime.prod_right fun i hi => (hS i hi).2
  have hodd : P % 2 = 1 := Nat.odd_iff.mp (Nat.coprime_two_left.mp hcop)
  have key : (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) * (P : ℚ)
      = 2 * ((∑ n ∈ S, P / n : ℕ) : ℚ) := by
    rw [Finset.sum_mul, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hpos : (n : ℚ) ≠ 0 := by
      have := (hS n hn).1
      exact Nat.cast_ne_zero.mpr (by omega)
    have hdvd : n ∣ P := by
      rw [hP]
      exact Finset.dvd_prod_of_mem (fun m : ℕ => m) hn
    rw [Nat.cast_div hdvd hpos]
    ring
  rw [hsum] at key
  have h2 : (5 * P : ℕ) = 2 * 121 * (∑ n ∈ S, P / n) := by
    have : (5 : ℚ) * P = 2 * 121 * ((∑ n ∈ S, P / n : ℕ) : ℚ) := by
      linarith [key]
    exact_mod_cast this
  omega
```
