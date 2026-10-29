# Gemini 3.6 Flash High (AI Studio)

Model: `Gemini 3.6 Flash High` (via AI Studio)\
Date: `2 August 2026`\
Line count: `66`\
Turn count: `7`

## Solution

```lean4
import Mathlib

theorem no_distinct_irreducible_two_over_n_sum :
    ¬ ∃ (S : Finset ℕ), (∀ n ∈ S, n > 0 ∧ Nat.Coprime 2 n) ∧
      (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) = 5 / 121 := by
  rintro ⟨S, hS1, hS2⟩
  have hn_odd : ∀ n ∈ S, n % 2 = 1 := by
    intro n hn
    have hcop := (hS1 n hn).2
    have hmod : n % 2 < 2 := Nat.mod_lt n (by decide)
    have hne : n % 2 ≠ 0 := by
      intro h0
      have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero h0
      have hgcd : 2 ∣ Nat.gcd 2 n := Nat.dvd_gcd dvd_rfl hdvd
      rw [hcop] at hgcd
      revert hgcd
      decide
    omega
  have hD_odd_gen : ∀ (s : Finset ℕ), (∀ n ∈ s, n % 2 = 1) → (s.prod id) % 2 = 1 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      rfl
    · intro a s' ha ih h_all
      rw [Finset.prod_insert ha]
      dsimp [id]
      have ha_odd : a % 2 = 1 := h_all a (by simp)
      have ih' : (s'.prod id) % 2 = 1 := ih (fun n hn => h_all n (by simp [hn]))
      change (∏ x ∈ s', x) % 2 = 1 at ih'
      rw [Nat.mul_mod, ha_odd, ih']
  set D := S.prod id
  have hD_odd : D % 2 = 1 := hD_odd_gen S hn_odd
  set M := ∑ n ∈ S, D / n
  have h_term : ∀ n ∈ S, (2 : ℚ) / (n : ℚ) * (D : ℚ) = 2 * ↑(D / n) := by
    intro n hn
    have hn_pos : n > 0 := (hS1 n hn).1
    have hn_ne : (n : ℚ) ≠ 0 := by positivity
    have hn_dvd : n ∣ D := Finset.dvd_prod_of_mem id hn
    have hD_eq : (D : ℚ) = (n : ℚ) * ↑(D / n) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hn_dvd]
    rw [hD_eq]
    calc (2 : ℚ) / (n : ℚ) * ((n : ℚ) * ↑(D / n))
      _ = ((2 : ℚ) / (n : ℚ) * (n : ℚ)) * ↑(D / n) := by ring
      _ = 2 * ↑(D / n) := by rw [div_mul_cancel₀ 2 hn_ne]
  have h_sum : (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) * (D : ℚ) = (2 * M : ℚ) := by
    rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl h_term]
    rw [← Finset.mul_sum]
    rw [← Nat.cast_sum]
  have h_eq_q : (5 * D : ℚ) = (2 * (121 * M) : ℚ) := by
    have h_tmp : 121 * ((∑ n ∈ S, (2 : ℚ) / (n : ℚ)) * (D : ℚ)) = (2 * (121 * M) : ℚ) := by
      rw [h_sum]
      push_cast
      ring
    rw [hS2] at h_tmp
    have h_tmp2 : 121 * ((5 / 121) * (D : ℚ)) = (5 * D : ℚ) := by
      field_simp
    rw [h_tmp2] at h_tmp
    exact h_tmp
  have h_eq_nat : 5 * D = 2 * (121 * M) := by exact_mod_cast h_eq_q
  have hD_even : D % 2 = 0 := by
    have h1 : (5 * D) % 2 = (2 * (121 * M)) % 2 := by rw [h_eq_nat]
    have h2 : (2 * (121 * M)) % 2 = 0 := by omega
    have h3 : (5 * D) % 2 = D % 2 := by omega
    omega
  omega
```
