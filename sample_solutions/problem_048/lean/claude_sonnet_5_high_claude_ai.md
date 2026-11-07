# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `15 September 2026`\
Line count: `90`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem odd_of_prime_quadratic_and_quintic (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h1 : Nat.Prime (x ^ 2 + 3 * y ^ 2 - 17))
      (h2 : Nat.Prime ((x ^ 5 + y ^ 5) / (x + y))) :
      Odd x ∧ Odd y := by
  have hdvd_general : ∀ m n : ℕ, (m + n) ∣ (m ^ 5 + n ^ 5) := by
    intro m n
    have h : (m : ℤ) + n ∣ (m : ℤ) ^ 5 + n ^ 5 :=
      ⟨(m : ℤ) ^ 4 - m ^ 3 * n + m ^ 2 * n ^ 2 - m * n ^ 3 + n ^ 4, by ring⟩
    exact_mod_cast h
  have hxy_pos : 0 < x + y := by omega
  have hp_ge2 : 2 ≤ x ^ 2 + 3 * y ^ 2 - 17 := h1.two_le
  have hb19 : 19 ≤ x ^ 2 + 3 * y ^ 2 := by omega
  rcases Nat.even_or_odd x with hex | hox <;> rcases Nat.even_or_odd y with hey | hoy
  · -- both x, y even : contradiction from h2
    exfalso
    obtain ⟨a, ha⟩ := hex
    obtain ⟨b, hb⟩ := hey
    have hxa : x = 2 * a := by omega
    have hyb : y = 2 * b := by omega
    obtain ⟨q, hqe⟩ := hdvd_general x y
    obtain ⟨q', hq'e⟩ := hdvd_general a b
    have hdvdxy : (x + y) ∣ (x ^ 5 + y ^ 5) := ⟨q, hqe⟩
    have hA : (x ^ 5 + y ^ 5) / (x + y) * (x + y) = x ^ 5 + y ^ 5 :=
      Nat.div_mul_cancel hdvdxy
    have hqe' : q * (x + y) = x ^ 5 + y ^ 5 := by
      rw [mul_comm q (x + y)]; exact hqe.symm
    have hval : (x ^ 5 + y ^ 5) / (x + y) = q :=
      Nat.eq_of_mul_eq_mul_right hxy_pos (hA.trans hqe'.symm)
    rw [hval] at h2
    have hq16 : q = 16 * q' := by
      have expand : (2 * a) ^ 5 + (2 * b) ^ 5 = 32 * (a ^ 5 + b ^ 5) := by ring
      have e1 : (x + y) * q = 16 * (x + y) * q' := by
        rw [← hqe, hxa, hyb, expand, hq'e]; ring
      have e2 : (x + y) * q = (x + y) * (16 * q') := by rw [e1]; ring
      exact Nat.eq_of_mul_eq_mul_left hxy_pos e2
    rw [hq16] at h2
    rcases Nat.eq_zero_or_pos q' with hq'0 | hq'pos
    · rw [hq'0, mul_zero] at h2
      exact Nat.not_prime_zero h2
    · have h2dvd : (2 : ℕ) ∣ 16 * q' := ⟨8 * q', by ring⟩
      rcases h2.eq_one_or_self_of_dvd 2 h2dvd with h | h
      · omega
      · omega
  · -- x even, y odd
    exfalso
    obtain ⟨a, ha⟩ := hex
    obtain ⟨m, hm⟩ := hoy
    have hxa : x = 2 * a := by omega
    have hN : x ^ 2 + 3 * y ^ 2 = 4 * (a ^ 2 + 3 * m ^ 2 + 3 * m) + 3 := by
      rw [hxa, hm]; ring
    have hp2 : x ^ 2 + 3 * y ^ 2 - 17 = 2 * (2 * (a ^ 2 + 3 * m ^ 2 + 3 * m) - 7) := by
      omega
    have hp2dvd : (2 : ℕ) ∣ (x ^ 2 + 3 * y ^ 2 - 17) := ⟨_, hp2⟩
    rcases h1.eq_one_or_self_of_dvd 2 hp2dvd with h | h
    · omega
    · have heq19 : x ^ 2 + 3 * y ^ 2 = 19 := by omega
      have hxle : x ≤ 4 := by
        by_contra hc
        push_neg at hc
        have hc5 : 5 ≤ x := by omega
        have h25 : (5 : ℕ) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hc5 2
        omega
      have hyle : y ≤ 4 := by
        by_contra hc
        push_neg at hc
        have hc5 : 5 ≤ y := by omega
        have h25 : (5 : ℕ) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hc5 2
        omega
      interval_cases x <;> interval_cases y <;>
        first
          | omega
          | norm_num at h2
  · -- x odd, y even : contradiction from h1
    exfalso
    obtain ⟨k, hk⟩ := hox
    obtain ⟨b, hb⟩ := hey
    have hyb : y = 2 * b := by omega
    have hN : x ^ 2 + 3 * y ^ 2 = 4 * (k ^ 2 + k + 3 * b ^ 2) + 1 := by
      rw [hk, hyb]; ring
    have hp4 : x ^ 2 + 3 * y ^ 2 - 17 = 4 * ((k ^ 2 + k + 3 * b ^ 2) - 4) := by
      omega
    have hp4dvd : (4 : ℕ) ∣ (x ^ 2 + 3 * y ^ 2 - 17) := ⟨_, hp4⟩
    rcases h1.eq_one_or_self_of_dvd 4 hp4dvd with h | h
    · omega
    · rw [← h] at h1
      norm_num at h1
  · -- both odd
    exact ⟨hox, hoy⟩
```
