# Claude Opus 4.7 (Arena AI)

Model: `claude-opus-4-7` (via Arena AI)\
Date: `18 July 2026`\
Line count: `55`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_distinct_irreducible_two_over_n_sum :
    ¬ ∃ (S : Finset ℕ), (∀ n ∈ S, n > 0 ∧ Nat.Coprime 2 n) ∧
      (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) = 5 / 121 := by
  rintro ⟨S, hS, hsum⟩
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => (hS n hn).1
  have hodd : ∀ n ∈ S, Odd n := by
    intro n hn
    have h : Nat.gcd 2 n = 1 := (hS n hn).2
    have hn2 : ¬ (2 ∣ n) := by
      intro hd
      have h2 : (2 : ℕ) ∣ Nat.gcd 2 n := Nat.dvd_gcd (dvd_refl 2) hd
      rw [h] at h2
      omega
    rw [Nat.odd_iff]
    omega
  set N := ∏ n ∈ S, n with hNdef
  have hNpos : 0 < N := Finset.prod_pos hpos
  have hNodd : Odd N := by
    rw [hNdef]
    exact Finset.prod_induction (fun n => n) Odd 
      (fun a b ha hb => ha.mul hb) odd_one hodd
  have hdvd : ∀ n ∈ S, n ∣ N := fun n hn => Finset.dvd_prod_of_mem _ hn
  set M := ∑ n ∈ S, N / n with hMdef
  have hkey : 242 * M = 5 * N := by
    have hNne : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
    have h1 : (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) * (121 * (N : ℚ)) = 
              5 / 121 * (121 * (N : ℚ)) := by rw [hsum]
    rw [Finset.sum_mul] at h1
    have h3 : ∀ n ∈ S, (2 : ℚ) / (n : ℚ) * (121 * (N : ℚ)) = 
              242 * ((N / n : ℕ) : ℚ) := by
      intro n hn
      have hnpos := hpos n hn
      have hndvd := hdvd n hn
      have hnne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
      rw [Nat.cast_div hndvd hnne]
      field_simp
      ring
    rw [Finset.sum_congr rfl h3] at h1
    have h4 : (5 : ℚ) / 121 * (121 * (N : ℚ)) = 5 * (N : ℚ) := by
      field_simp
    rw [h4] at h1
    have h5 : (∑ n ∈ S, (242 : ℚ) * ((N / n : ℕ) : ℚ)) = 242 * (M : ℚ) := by
      rw [← Finset.mul_sum, hMdef]
      push_cast
      rfl
    rw [h5] at h1
    exact_mod_cast h1
  have h5Nodd : Odd (5 * N) := (by decide : Odd 5).mul hNodd
  have h242Meven : Even (242 * M) := ⟨121 * M, by ring⟩
  rw [hkey] at h242Meven
  have he : (5 * N) % 2 = 0 := Nat.even_iff.mp h242Meven
  have ho : (5 * N) % 2 = 1 := Nat.odd_iff.mp h5Nodd
  omega
```
