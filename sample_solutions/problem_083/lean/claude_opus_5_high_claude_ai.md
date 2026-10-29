# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `27 August 2026`\
Line count: `73`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem six_digit_triangular_digit_sum (a b : ℕ)
    (ha_digits : 10 ^ 5 ≤ a ∧ a < 10 ^ 6) (hb_digits : 10 ^ 5 ≤ b ∧ b < 10 ^ 6)
      (ha_tri : ∃ k : ℕ, a = k * (k + 1) / 2) (hb_tri : ∃ k : ℕ, b = k * (k + 1) / 2)
      (h_diff : b - a = 13761) (h_sum : (Nat.digits 10 (a * b)).sum = 54) :
      b = 299151 := by
  obtain ⟨ha1, ha2⟩ := ha_digits
  obtain ⟨hb1, hb2⟩ := hb_digits
  have ha1' : 100000 ≤ a := le_trans (by norm_num) ha1
  have ha2' : a < 1000000 := lt_of_lt_of_le ha2 (by norm_num)
  have hb1' : 100000 ≤ b := le_trans (by norm_num) hb1
  have hb2' : b < 1000000 := lt_of_lt_of_le hb2 (by norm_num)
  have hdvd : ∀ k : ℕ, 2 ∣ k * (k + 1) := by
    intro k
    rcases Nat.even_or_odd k with ⟨c, hc⟩ | ⟨c, hc⟩
    · subst hc
      exact ⟨c * (c + c + 1), by ring⟩
    · subst hc
      exact ⟨(2 * c + 1) * (c + 1), by ring⟩
  obtain ⟨m, hm⟩ := ha_tri
  obtain ⟨n, hn⟩ := hb_tri
  have h2a : 2 * a = m * (m + 1) := by rw [hm]; exact Nat.mul_div_cancel' (hdvd m)
  have h2b : 2 * b = n * (n + 1) := by rw [hn]; exact Nat.mul_div_cancel' (hdvd n)
  have hba : b = a + 13761 := by omega
  clear hm hn h_diff
  have hm_lo : 447 ≤ m := by
    by_contra hc
    push_neg at hc
    have h1 : m * (m + 1) ≤ 446 * 447 := Nat.mul_le_mul (by omega) (by omega)
    linarith
  have hm_hi : m ≤ 1413 := by
    by_contra hc
    push_neg at hc
    have h1 : 1414 * 1415 ≤ m * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
    linarith
  have hmn : m < n := by
    by_contra hc
    push_neg at hc
    have h1 : n * (n + 1) ≤ m * (m + 1) := Nat.mul_le_mul hc (by omega)
    linarith
  obtain ⟨D, hD1, hD⟩ : ∃ D, 1 ≤ D ∧ n = m + D := ⟨n - m, by omega, by omega⟩
  subst hD
  have expand : (m + D) * (m + D + 1) = m * (m + 1) + (m * D * 2 + D * D + D) := by ring
  have key : m * (m + 1) + (m * D * 2 + D * D + D) = m * (m + 1) + 27522 := by
    rw [← expand]; linarith
  have key2 : m * D * 2 + D * D + D = 27522 := Nat.add_left_cancel key
  have hfact : D * (2 * m + D + 1) = 27522 := by rw [← key2]; ring
  have hD30 : D ≤ 30 := by
    by_contra hc
    push_neg at hc
    have h1 : 31 * (2 * 447 + 31 + 1) ≤ D * (2 * m + D + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [hfact] at h1
    norm_num at h1
  have hcases : (m = 1245 ∧ D = 11) ∨ (m = 755 ∧ D = 18) ∨ (m = 614 ∧ D = 22) := by
    interval_cases D <;> omega
  rcases hcases with ⟨hm', -⟩ | ⟨hm', -⟩ | ⟨hm', -⟩
  · subst hm'
    have e1 : (1245 : ℕ) * (1245 + 1) = 1551270 := by norm_num
    have hav : a = 775635 := by omega
    have hbv : b = 789396 := by omega
    rw [hav, hbv] at h_sum
    norm_num at h_sum
  · subst hm'
    have e1 : (755 : ℕ) * (755 + 1) = 570780 := by norm_num
    omega
  · subst hm'
    have e1 : (614 : ℕ) * (614 + 1) = 377610 := by norm_num
    have hav : a = 188805 := by omega
    have hbv : b = 202566 := by omega
    rw [hav, hbv] at h_sum
    norm_num at h_sum
```
