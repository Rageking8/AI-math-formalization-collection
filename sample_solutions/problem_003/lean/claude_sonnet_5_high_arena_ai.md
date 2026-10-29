# Claude Sonnet 5 High (Arena AI)

Model: `claude-sonnet-5-high` (via Arena AI)\
Date: `2 August 2026`\
Line count: `57`\
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
  set N : ℕ := ∏ n ∈ S, n with hNdef
  set M : ℕ → ℕ := fun n => ∏ x ∈ S.erase n, x with hMdef
  set T : ℕ := ∑ n ∈ S, M n with hTdef
  have hNpos : 0 < N := by
    rw [hNdef]
    exact Finset.prod_pos (fun n hn => (hS n hn).1)
  have hNodd : Nat.Coprime 2 N := by
    rw [hNdef]
    exact Finset.prod_induction (fun n => n) (fun m => Nat.Coprime 2 m)
      (fun a b ha hb => Nat.Coprime.mul_right ha hb) (Nat.coprime_one_right 2)
      (fun n hn => (hS n hn).2)
  have hMnpos : ∀ n ∈ S, 0 < M n := by
    intro n hn
    simp only [hMdef]
    exact Finset.prod_pos (fun x hx => (hS x (Finset.mem_of_mem_erase hx)).1)
  have hmul : ∀ n ∈ S, n * M n = N := by
    intro n hn
    simp only [hMdef, hNdef]
    exact Finset.mul_prod_erase S (fun x => x) hn
  have hterm : ∀ n ∈ S, (2 : ℚ) / (n : ℚ) = 2 * (M n : ℚ) / (N : ℚ) := by
    intro n hn
    have hn0 : (n : ℚ) ≠ 0 := by
      have h := (hS n hn).1
      exact_mod_cast h.ne'
    have hMn0 : (M n : ℚ) ≠ 0 := by
      have h := hMnpos n hn
      exact_mod_cast h.ne'
    have heqN : (N : ℚ) = (n : ℚ) * (M n : ℚ) := by
      have h := hmul n hn
      exact_mod_cast h.symm
    rw [heqN, div_eq_div_iff hn0 (mul_ne_zero hn0 hMn0)]
    ring
  have hTcast : (T : ℚ) = ∑ n ∈ S, (M n : ℚ) := by
    rw [hTdef]
    norm_cast
  have hsum2 : (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) = 2 * (T : ℚ) / (N : ℚ) := by
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Finset.mul_sum, ← hTcast]
  have heq2 : 2 * (T : ℚ) / (N : ℚ) = 5 / 121 := by
    rw [← hsum2]; exact hsum
  have hN0 : (N : ℚ) ≠ 0 := by
    have h := hNpos.ne'
    exact_mod_cast h
  have h121 : (121 : ℚ) ≠ 0 := by norm_num
  have hcross : 2 * (T : ℚ) * 121 = 5 * (N : ℚ) := (div_eq_div_iff hN0 h121).mp heq2
  have hcrossN' : (242 : ℚ) * (T : ℚ) = 5 * (N : ℚ) := by linear_combination hcross
  have hcrossN : 242 * T = 5 * N := by exact_mod_cast hcrossN'
  have hdvd : (2 : ℕ) ∣ 5 * N := ⟨121 * T, by rw [← hcrossN]; ring⟩
  have hNodd' : ¬ (2 : ℕ) ∣ N := (Nat.prime_two.coprime_iff_not_dvd).mp hNodd
  rcases (Nat.prime_two.dvd_mul).mp hdvd with h5 | hN2
  · exact absurd h5 (by norm_num)
  · exact hNodd' hN2
```
