# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `11 August 2026`\
Line count: `123`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem not_exists_pos_sol_quad_modeq_pow :
    ¬ ∃ (x y : ℕ), 0 < x ∧ 0 < y ∧ (x ^ 2 + 4 * x * y + 2 * y ^ 2 ≡ 5 * 2 ^ x [MOD 2 ^ (2 * x + 3)]) := by
  have decomp : ∀ (N n : ℕ), n ≤ N → 0 < n → ∃ j m : ℕ, n = 2 ^ j * m ∧ m % 2 = 1 := by
    intro N
    induction N with
    | zero => intro n h1 h2; exfalso; omega
    | succ M ih =>
      intro n h1 h2
      rcases Nat.even_or_odd n with ⟨t, ht⟩ | ⟨t, ht⟩
      · obtain ⟨j, m, hm1, hm2⟩ := ih t (by omega) (by omega)
        exact ⟨j + 1, m, by rw [ht, hm1]; ring, hm2⟩
      · exact ⟨0, n, by rw [pow_zero, one_mul], by omega⟩
  have pow_ge : ∀ i : ℕ, i + 1 ≤ 2 ^ i := by
    intro i
    induction i with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  have sqrt_dvd : ∀ (i : ℕ) (t : ℤ), (2 : ℤ) ^ (2 * i) ∣ t ^ 2 → (2 : ℤ) ^ i ∣ t := by
    intro i
    induction i with
    | zero => intro t _; simpa using one_dvd t
    | succ n ih =>
      intro t ht
      have hdvd2 : (2 : ℤ) ∣ (2 : ℤ) ^ (2 * (n + 1)) := ⟨(2 : ℤ) ^ (2 * n + 1), by ring⟩
      have h2t : (2 : ℤ) ∣ t := Int.prime_two.dvd_of_dvd_pow (hdvd2.trans ht)
      obtain ⟨s, rfl⟩ := h2t
      obtain ⟨w, hw⟩ := ht
      have h4 : (4 : ℤ) * s ^ 2 = 4 * ((2 : ℤ) ^ (2 * n) * w) := by linear_combination hw
      have h5 : s ^ 2 = (2 : ℤ) ^ (2 * n) * w := mul_left_cancel₀ (by norm_num) h4
      obtain ⟨v, hv⟩ := ih s ⟨w, h5⟩
      exact ⟨v, by rw [hv]; ring⟩
  have no3mod4 : ∀ T e : ℤ, T ^ 2 ≠ 3 + 4 * e := by
    intro T e hT
    rcases Int.even_or_odd T with ⟨w, hw⟩ | ⟨w, hw⟩
    · subst hw
      obtain ⟨B, hB⟩ : ∃ B : ℤ, w ^ 2 = B := ⟨_, rfl⟩
      have hh : 4 * B - 4 * e = 3 := by linear_combination hT - 4 * hB
      omega
    · subst hw
      obtain ⟨B, hB⟩ : ∃ B : ℤ, w ^ 2 = B := ⟨_, rfl⟩
      have hh : 4 * B + 4 * w - 4 * e = 2 := by linear_combination hT - 4 * hB
      omega
  rintro ⟨x, y, hx, hy, h⟩
  obtain ⟨c, hc⟩ := h.dvd
  push_cast at hc
  rcases Nat.even_or_odd x with ⟨r, rfl⟩ | ⟨t, rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    push_cast at hc
    have hM : 5 * (2 : ℤ) ^ (2 * k + 1) + 2 * ((k : ℤ) + 1) ^ 2
        - ((y : ℤ) + 2 * (k : ℤ) + 2) ^ 2 = 2 ^ (4 * k + 6) * c := by
      have h2 : (2 : ℤ) * (5 * (2 : ℤ) ^ (2 * k + 1) + 2 * ((k : ℤ) + 1) ^ 2
          - ((y : ℤ) + 2 * (k : ℤ) + 2) ^ 2) = 2 * ((2 : ℤ) ^ (4 * k + 6) * c) := by
        linear_combination hc
      exact mul_left_cancel₀ (by norm_num) h2
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · push_cast at hM
        have hclean : ((y : ℤ) + 2) ^ 2 = 12 - 64 * c := by linear_combination -hM
        have hS4 : (2 : ℤ) ^ (2 * 1) ∣ ((y : ℤ) + 2) ^ 2 :=
          ⟨3 - 16 * c, by linear_combination hclean⟩
        obtain ⟨T, hT⟩ := sqrt_dvd 1 ((y : ℤ) + 2) hS4
        have h1 : (4 : ℤ) * T ^ 2 = 4 * (3 + 4 * (-4 * c)) := by
          linear_combination hclean - ((y : ℤ) + 2 + 2 * T) * hT
        exact no3mod4 T (-4 * c) (mul_left_cancel₀ (by norm_num) h1)
      · push_cast at hM
        have hclean : ((y : ℤ) + 4) ^ 2 = 48 - 1024 * c := by linear_combination -hM
        have hS16 : (2 : ℤ) ^ (2 * 2) ∣ ((y : ℤ) + 4) ^ 2 :=
          ⟨3 - 64 * c, by linear_combination hclean⟩
        obtain ⟨T, hT⟩ := sqrt_dvd 2 ((y : ℤ) + 4) hS16
        have h1 : (16 : ℤ) * T ^ 2 = 16 * (3 + 4 * (-16 * c)) := by
          linear_combination hclean - ((y : ℤ) + 4 + 4 * T) * hT
        exact no3mod4 T (-16 * c) (mul_left_cancel₀ (by norm_num) h1)
    · obtain ⟨j, m, hkm, hmodd⟩ := decomp (k + 1) (k + 1) le_rfl (by omega)
      have hle : 2 ^ j ≤ k + 1 := Nat.le_of_dvd (by omega) ⟨m, hkm⟩
      have hj2 : j + 2 ≤ k + 1 := by
        rcases Nat.lt_or_ge j 2 with h1 | h1
        · omega
        · obtain ⟨i, hi⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
          subst hi
          have hp := pow_ge i
          have hq : (2 : ℕ) ^ (i + 2) = 2 ^ i * 4 := by ring
          omega
      obtain ⟨d, rfl⟩ : ∃ d, k = j + d + 1 := ⟨k - j - 1, by omega⟩
      have hK : ((j : ℤ) + (d : ℤ) + 2) = 2 ^ j * (m : ℤ) := by
        have h' : ((j + d + 1 + 1 : ℕ) : ℤ) = ((2 ^ j * m : ℕ) : ℤ) := by rw [hkm]
        push_cast at h'
        linarith
      have hN : (2 : ℤ) ^ (2 * j + 1) * (5 * 2 ^ (2 * d + 2) + (m : ℤ) ^ 2)
          - ((y : ℤ) + 2 * (j : ℤ) + 2 * (d : ℤ) + 4) ^ 2 = 2 ^ (4 * j + 4 * d + 10) * c := by
        push_cast at hM
        linear_combination hM - 2 * (2 ^ j * (m : ℤ) + (j : ℤ) + (d : ℤ) + 2) * hK
      have hA : (2 : ℤ) ^ (2 * j) ∣ ((y : ℤ) + 2 * (j : ℤ) + 2 * (d : ℤ) + 4) ^ 2 :=
        ⟨2 * (5 * 2 ^ (2 * d + 2) + (m : ℤ) ^ 2) - 2 ^ (2 * j + 4 * d + 10) * c, by
          linear_combination -hN⟩
      obtain ⟨R, hR⟩ := sqrt_dvd j ((y : ℤ) + 2 * (j : ℤ) + 2 * (d : ℤ) + 4) hA
      rw [hR] at hN
      have hR2 : R ^ 2 = 2 * (5 * (2 : ℤ) ^ (2 * d + 2) + (m : ℤ) ^ 2
          - 2 ^ (2 * j + 4 * d + 9) * c) := by
        have h1 : (2 : ℤ) ^ (2 * j) * R ^ 2 = (2 : ℤ) ^ (2 * j) * (2 * (5 * (2 : ℤ) ^ (2 * d + 2)
            + (m : ℤ) ^ 2 - 2 ^ (2 * j + 4 * d + 9) * c)) := by
          linear_combination -hN
        exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h1
      have h2R : (2 : ℤ) ∣ R := Int.prime_two.dvd_of_dvd_pow (⟨_, hR2⟩ : (2 : ℤ) ∣ R ^ 2)
      obtain ⟨R1, rfl⟩ := h2R
      have hU : 5 * (2 : ℤ) ^ (2 * d + 2) + (m : ℤ) ^ 2
          = 2 * R1 ^ 2 + 2 ^ (2 * j + 4 * d + 9) * c := by
        have h2 : (2 : ℤ) * (5 * (2 : ℤ) ^ (2 * d + 2) + (m : ℤ) ^ 2)
            = 2 * (2 * R1 ^ 2 + 2 ^ (2 * j + 4 * d + 9) * c) := by linear_combination -hR2
        exact mul_left_cancel₀ (by norm_num) h2
      have hmm : (2 : ℤ) ∣ (m : ℤ) ^ 2 :=
        ⟨R1 ^ 2 + 2 ^ (2 * j + 4 * d + 8) * c - 5 * 2 ^ (2 * d + 1), by linear_combination hU⟩
      have hm2 : (2 : ℤ) ∣ (m : ℤ) := Int.prime_two.dvd_of_dvd_pow hmm
      have hm2' : (2 : ℕ) ∣ m := by exact_mod_cast hm2
      omega
  · push_cast at hc
    have habs : (2 : ℤ) ∣ 1 :=
      ⟨5 * 2 ^ (2 * t) - 2 * (t : ℤ) ^ 2 - 2 * (t : ℤ) - 4 * (t : ℤ) * (y : ℤ) - 2 * (y : ℤ)
        - (y : ℤ) ^ 2 - 16 * 2 ^ (4 * t) * c, by linear_combination -hc⟩
    have hle1 := Int.le_of_dvd (by norm_num) habs
    linarith
```
