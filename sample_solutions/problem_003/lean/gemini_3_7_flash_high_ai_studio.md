# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `23 August 2026`\
Line count: `61`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem no_distinct_irreducible_two_over_n_sum :
    ¬ ∃ (S : Finset ℕ), (∀ n ∈ S, n > 0 ∧ Nat.Coprime 2 n) ∧
      (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) = 5 / 121 := by
  rintro ⟨S, hS, hsum⟩
  have h_term (n : ℕ) (hn : n ∈ S) :
      (∏ m ∈ S, (m : ℚ)) * ((2 : ℚ) / (n : ℚ)) = 2 * ∏ m ∈ S.erase n, (m : ℚ) := by
    have hnz : (n : ℚ) ≠ 0 := by
      have : n ≠ 0 := ne_of_gt (hS n hn).1
      exact Nat.cast_ne_zero.mpr this
    have h_cancel : ((2 : ℚ) / (n : ℚ)) * (n : ℚ) = 2 := div_mul_cancel₀ (2 : ℚ) hnz
    rw [← Finset.mul_prod_erase S (fun m => (m : ℚ)) hn]
    calc ((n : ℚ) * ∏ m ∈ S.erase n, (m : ℚ)) * ((2 : ℚ) / (n : ℚ))
      _ = (((2 : ℚ) / (n : ℚ)) * (n : ℚ)) * ∏ m ∈ S.erase n, (m : ℚ) := by ring
      _ = 2 * ∏ m ∈ S.erase n, (m : ℚ) := by rw [h_cancel]
  have h_sum_terms : (∑ n ∈ S, (∏ m ∈ S, (m : ℚ)) * ((2 : ℚ) / (n : ℚ))) =
      ∑ n ∈ S, (2 * ∏ m ∈ S.erase n, (m : ℚ)) :=
    Finset.sum_congr rfl (fun n hn => h_term n hn)
  have h_cleared : (121 : ℚ) * (∏ m ∈ S, (m : ℚ)) * (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) =
      (121 : ℚ) * (∏ m ∈ S, (m : ℚ)) * (5 / 121) := by
    rw [hsum]
  have h_lhs : (121 : ℚ) * (∏ m ∈ S, (m : ℚ)) * (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) =
      2 * (121 * ∑ n ∈ S, ∏ m ∈ S.erase n, (m : ℚ)) := by
    rw [mul_assoc (121 : ℚ), Finset.mul_sum, h_sum_terms, ← Finset.mul_sum]
    ring
  have h_rhs : (121 : ℚ) * (∏ m ∈ S, (m : ℚ)) * (5 / 121) = 5 * (∏ m ∈ S, (m : ℚ)) := by
    ring
  have h_rat_eq : 5 * (∏ m ∈ S, (m : ℚ)) = 2 * (121 * ∑ n ∈ S, ∏ m ∈ S.erase n, (m : ℚ)) :=
    h_rhs.symm.trans (h_cleared.symm.trans h_lhs)
  have h_nat_eq : 5 * (∏ m ∈ S, m) = 2 * (121 * ∑ n ∈ S, ∏ m ∈ S.erase n, m) := by
    apply Nat.cast_injective (R := ℚ)
    push_cast
    exact h_rat_eq
  have h_dvd : 2 ∣ 5 * (∏ m ∈ S, m) := ⟨121 * ∑ n ∈ S, ∏ m ∈ S.erase n, m, h_nat_eq⟩
  have hprime : Nat.Prime 2 := Nat.prime_two
  rw [hprime.dvd_mul] at h_dvd
  rcases h_dvd with h5 | hP
  · revert h5
    decide
  · have h_dvd_mem : ∀ (s : Finset ℕ), 2 ∣ ∏ m ∈ s, m → ∃ m ∈ s, 2 ∣ m := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro h
        rw [Finset.prod_empty] at h
        have : 2 ≤ 1 := Nat.le_of_dvd (by decide) h
        omega
      | @insert a s ha ih =>
        intro h
        rw [Finset.prod_insert ha] at h
        rcases hprime.dvd_mul.mp h with h1 | h2
        · exact ⟨a, Finset.mem_insert_self a s, h1⟩
        · rcases ih h2 with ⟨m, hm, hdiv⟩
          exact ⟨m, Finset.mem_insert_of_mem hm, hdiv⟩
    rcases h_dvd_mem S hP with ⟨m, hm, hm_dvd⟩
    have hcop := (hS m hm).2
    have hgcd : 2 ∣ Nat.gcd 2 m := Nat.dvd_gcd (dvd_refl 2) hm_dvd
    rw [hcop] at hgcd
    have : 2 ≤ 1 := Nat.le_of_dvd (by decide) hgcd
    omega
```
