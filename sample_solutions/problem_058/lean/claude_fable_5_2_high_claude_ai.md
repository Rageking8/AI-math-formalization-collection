# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `14 November 2026`\
Line count: `125`\
Turn count: `1`

## Solution

```lean4
import Mathlib

open BigOperators

theorem no_pos_int_satisfies_digit_sum_eq :
    ¬ ∃ (n : ℕ), 1 < n ∧
      (1 / (n : ℝ)) * (∑ k ∈ Finset.Icc 1 n, ((Nat.digits 10 k).length : ℝ)) =
      ((Nat.digits 10 n).length : ℝ) - 1 / ((n : ℝ) ^ (1 / 4 : ℝ) - 1) := by
  -- Closed form: 9 * ∑_{k=1}^n len(k) + 10^len(n) = 9 * len(n) * (n+1) + 1.
  have key : ∀ n : ℕ, 9 * (∑ k ∈ Finset.Icc 1 n, (Nat.digits 10 k).length)
      + 10 ^ (Nat.digits 10 n).length = 9 * ((Nat.digits 10 n).length * (n + 1)) + 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      have h1 : n < 10 ^ (Nat.digits 10 n).length :=
        Nat.lt_base_pow_length_digits (by norm_num)
      have h2 : 10 ^ (Nat.digits 10 n).length ≤ 10 * n :=
        Nat.base_pow_length_digits_le 10 n (by norm_num) (by omega)
      have h3 : n + 1 < 10 ^ (Nat.digits 10 (n + 1)).length :=
        Nat.lt_base_pow_length_digits (by norm_num)
      have h4 : 10 ^ (Nat.digits 10 (n + 1)).length ≤ 10 * (n + 1) :=
        Nat.base_pow_length_digits_le 10 (n + 1) (by norm_num) (by omega)
      generalize (Nat.digits 10 n).length = a at *
      generalize (Nat.digits 10 (n + 1)).length = b at *
      generalize ∑ k ∈ Finset.Icc 1 n, (Nat.digits 10 k).length = S at *
      have hab : a ≤ b := by
        by_contra hlt
        have h5 := Nat.pow_le_pow_right (show 0 < 10 by norm_num) (show b + 1 ≤ a by omega)
        rw [pow_succ] at h5
        omega
      have hba : b ≤ a + 1 := by
        by_contra hlt
        have h5 := Nat.pow_le_pow_right (show 0 < 10 by norm_num) (show a + 1 + 1 ≤ b by omega)
        rw [pow_succ, pow_succ] at h5
        omega
      rcases (show b = a ∨ b = a + 1 by omega) with rfl | rfl
      · linarith
      · rw [pow_succ] at h4 ⊢
        have hn1 : n + 1 = 10 ^ a := by omega
        linarith
  have hA : ∀ d : ℕ, 1 + 9 * d ≤ 10 ^ d := by
    intro d
    induction d with
    | zero => simp
    | succ d ih => rw [pow_succ]; omega
  have hB : ∀ d : ℕ, 2 ≤ d → 2 + 18 * d ≤ 10 ^ d := by
    intro d hd
    induction d, hd using Nat.le_induction with
    | base => norm_num
    | succ d hd ih => rw [pow_succ]; omega
  rintro ⟨n, hn, h⟩
  have hk := key n
  have h1 : n < 10 ^ (Nat.digits 10 n).length :=
    Nat.lt_base_pow_length_digits (by norm_num)
  have h2 : 10 ^ (Nat.digits 10 n).length ≤ 10 * n :=
    Nat.base_pow_length_digits_le 10 n (by norm_num) (by omega)
  have hSr : (∑ k ∈ Finset.Icc 1 n, ((Nat.digits 10 k).length : ℝ))
      = ((∑ k ∈ Finset.Icc 1 n, (Nat.digits 10 k).length : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
  rw [hSr] at h
  generalize (Nat.digits 10 n).length = d at h hk h1 h2
  generalize ∑ k ∈ Finset.Icc 1 n, (Nat.digits 10 k).length = S at h hk
  obtain ⟨R, hR⟩ : ∃ R : ℕ, 10 ^ d = R + (1 + 9 * d) :=
    ⟨10 ^ d - (1 + 9 * d), by have := hA d; omega⟩
  -- the real fourth root
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have ht1 : 1 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_lt_rpow hn1 (by norm_num)
  have ht4 : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  generalize (n : ℝ) ^ (1 / 4 : ℝ) = t at h ht1 ht4
  have hkr : 9 * (S : ℝ) + 10 ^ d = 9 * (d * (n + 1)) + 1 := by exact_mod_cast hk
  have hRr : (10 : ℝ) ^ d = R + (1 + 9 * d) := by exact_mod_cast hR
  have ht0 : t - 1 ≠ 0 := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have h' : (S : ℝ) * (t - 1) = n * (d * (t - 1) - 1) := by
    field_simp at h
    linarith
  have hE : (R : ℝ) * (t - 1) = 9 * n := by
    linear_combination (t - 1) * hkr - (t - 1) * hRr - 9 * h'
  -- an identity in ℕ
  have hN : (R + 9 * n) ^ 4 = R ^ 4 * n := by
    have h5 : ((R : ℝ) + 9 * n) ^ 4 = R ^ 4 * n := by
      have h6 : (R : ℝ) + 9 * n = R * t := by linarith
      rw [h6, mul_pow, ht4]
    exact_mod_cast h5
  clear h h' hE hkr hRr ht0 hn0 ht1 ht4 hn1 hSr t key hA
  have hRpos : 0 < R := by
    rcases Nat.eq_zero_or_pos R with rfl | h0
    · have h5 : 0 < (0 + 9 * n) ^ 4 := pow_pos (by omega) 4
      rw [hN] at h5
      norm_num at h5
    · exact h0
  have hdvd : R ∣ 9 * n := by
    have h5 : R ^ 4 ∣ (R + 9 * n) ^ 4 := Dvd.intro _ hN.symm
    have h6 : R ∣ R + 9 * n := (Nat.pow_dvd_pow_iff (by norm_num)).mp h5
    exact (Nat.dvd_add_right (dvd_refl R)).mp h6
  obtain ⟨m, hm⟩ := hdvd
  have hn4 : n = (1 + m) ^ 4 := by
    have h5 : R ^ 4 * (1 + m) ^ 4 = R ^ 4 * n := by
      rw [← hN, hm]
      ring
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos hRpos 4) h5).symm
  have hd2 : 2 ≤ d := by
    by_contra hlt
    have h5 : d = 0 ∨ d = 1 := by omega
    rcases h5 with rfl | rfl
    · omega
    · omega
  have hB' := hB d hd2
  have hm18 : m < 18 := by
    by_contra hge
    have h5 := Nat.mul_le_mul_left R (show 18 ≤ m by omega)
    omega
  clear hB hB' hk
  interval_cases m <;> norm_num at hn4 <;> subst hn4 <;>
    (have hd7 : d < 7 := by
      by_contra hge
      have h5 := Nat.pow_le_pow_right (show 0 < 10 by norm_num) (show 7 ≤ d by omega)
      omega) <;>
    interval_cases d <;> omega
```
