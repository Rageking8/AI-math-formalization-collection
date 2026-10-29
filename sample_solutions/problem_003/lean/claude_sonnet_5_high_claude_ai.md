# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `30 July 2026`\
Line count: `56`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem no_distinct_irreducible_two_over_n_sum :
    ¬ ∃ (S : Finset ℕ), (∀ n ∈ S, n > 0 ∧ Nat.Coprime 2 n) ∧
      (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) = 5 / 121 := by
  rintro ⟨S, hS, hsum⟩
  have hnpos : ∀ n ∈ S, (n : ℚ) ≠ 0 := by
    intro n hn
    have h0 := (hS n hn).1
    exact_mod_cast h0.ne'
  have hDodd : Nat.Coprime 2 (∏ n ∈ S, n) := by
    apply Finset.prod_induction (s := S) (fun n => n) (Nat.Coprime 2)
    · intro a b ha hb
      exact ha.mul_right hb
    · exact Nat.coprime_one_right 2
    · intro x hx
      exact (hS x hx).2
  have term_eq : ∀ n ∈ S, (2 : ℚ) / n * (∏ m ∈ S, (m : ℚ)) = 2 * ∏ m ∈ S.erase n, (m : ℚ) := by
    intro n hn
    have h : (n : ℚ) * ∏ m ∈ S.erase n, (m : ℚ) = ∏ m ∈ S, (m : ℚ) :=
      Finset.mul_prod_erase S (fun m => (m : ℚ)) hn
    have hn0 : (n : ℚ) ≠ 0 := hnpos n hn
    have step : (2 : ℚ) / n * n = 2 := by
      rw [div_mul_eq_mul_div, mul_div_assoc, div_self hn0, mul_one]
    calc (2 : ℚ) / n * (∏ m ∈ S, (m : ℚ))
        = (2 : ℚ) / n * ((n : ℚ) * ∏ m ∈ S.erase n, (m : ℚ)) := by rw [← h]
      _ = ((2 : ℚ) / n * n) * ∏ m ∈ S.erase n, (m : ℚ) := by ring
      _ = 2 * ∏ m ∈ S.erase n, (m : ℚ) := by rw [step]
  have hsum2 : (∑ n ∈ S, (2 : ℚ) / n) * (∏ m ∈ S, (m : ℚ))
      = 2 * ∑ n ∈ S, ∏ m ∈ S.erase n, (m : ℚ) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl term_eq
  rw [hsum] at hsum2
  set D : ℕ := ∏ n ∈ S, n with hDdef
  set K : ℕ := ∑ n ∈ S, ∏ m ∈ S.erase n, m with hKdef
  have hDcast : (D : ℚ) = ∏ m ∈ S, (m : ℚ) := by
    rw [hDdef]; push_cast; try ring
  have hKcast : (K : ℚ) = ∑ n ∈ S, ∏ m ∈ S.erase n, (m : ℚ) := by
    rw [hKdef]; push_cast; try ring
  rw [← hDcast, ← hKcast] at hsum2
  have h121 : (121 : ℚ) ≠ 0 := by norm_num
  rw [div_mul_eq_mul_div, div_eq_iff h121] at hsum2
  have keyQ : (5 * D : ℕ) = (242 * K : ℕ) := by
    have hcast : ((5 * D : ℕ) : ℚ) = ((242 * K : ℕ) : ℚ) := by
      push_cast
      linear_combination hsum2
    exact_mod_cast hcast
  have h2dvd : (2 : ℕ) ∣ 5 * D := by
    rw [keyQ]
    exact ⟨121 * K, by ring⟩
  have h2dvd' : (2 : ℕ) ∣ D := by
    rcases (Nat.prime_two.dvd_mul).mp h2dvd with h | h
    · exact absurd h (by decide)
    · exact h
  have hcop : ¬ (2 : ℕ) ∣ D := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hDodd
  exact hcop h2dvd'
```
