# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `27 August 2026`\
Line count: `102`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem eq_one_of_dvd_pow_add_one (n : ℕ) (hn : 0 < n) (h2 : n ∣ 2^n + 1) (h3 : n ∣ 3^n + 1) :
    n = 1 := by
  have h_not_dvd (k : ℕ) (hk : 2 ≤ k) (h : k ∣ k ^ n + 1) : False := by
    have hpow : k ∣ k ^ n := dvd_pow_self k (ne_of_gt hn)
    have hdvd1 : k ∣ 1 := (Nat.dvd_add_right hpow).mp h
    have : k ≤ 1 := Nat.le_of_dvd (by omega) hdvd1
    omega

  by_contra hn1
  have hn_gt_one : 1 < n := by omega
  let p := n.minFac
  have hp : Nat.Prime p := Nat.minFac_prime hn1
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp_dvd : p ∣ n := Nat.minFac_dvd n
  have h2p : p ∣ 2 ^ n + 1 := dvd_trans hp_dvd h2

  have hp_ne_2 : p ≠ 2 := by
    intro hp2
    have : 2 ∣ 2 ^ n + 1 := hp2 ▸ h2p
    exact h_not_dvd 2 (by decide) this

  have hp_ge_3 : 3 ≤ p := by
    have := hp.two_le
    omega

  have h2_ne_zero : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h0
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hp2
    omega

  have h_cast : ((2 ^ n + 1 : ℕ) : ZMod p) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p (2 ^ n + 1)).mpr h2p
  have h_pow_neg : (2 : ZMod p) ^ n = -1 := by
    have h_cast2 : (2 : ZMod p) ^ n + 1 = 0 := by
      push_cast at h_cast
      exact h_cast
    linear_combination h_cast2

  have h_pow_2n : (2 : ZMod p) ^ (2 * n) = 1 := by
    have h_split : 2 * n = n + n := by omega
    rw [h_split, pow_add, h_pow_neg]
    ring

  have hdvd2n : orderOf (2 : ZMod p) ∣ 2 * n :=
    orderOf_dvd_iff_pow_eq_one.mpr h_pow_2n

  have hnot_dvd_n : ¬ orderOf (2 : ZMod p) ∣ n := by
    intro hdvd
    have h1 : (2 : ZMod p) ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    have h2zero : (2 : ZMod p) = 0 := by
      calc (2 : ZMod p) = 1 - (-1) := by ring
      _ = 1 - (2 : ZMod p) ^ n := by rw [h_pow_neg]
      _ = 1 - 1 := by rw [h1]
      _ = 0 := by ring
    exact h2_ne_zero h2zero

  have h_dvd_p_sub_one : orderOf (2 : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one h2_ne_zero

  have h_cop : n.Coprime (p - 1) :=
    Nat.coprime_of_lt_minFac (by omega) (by omega)

  have h_cop_d : n.Coprime (orderOf (2 : ZMod p)) :=
    Nat.Coprime.of_dvd_right h_dvd_p_sub_one h_cop

  have hdvd2 : orderOf (2 : ZMod p) ∣ 2 :=
    (Nat.Coprime.dvd_mul_right h_cop_d.symm).mp hdvd2n

  have hdvd2_cases : orderOf (2 : ZMod p) = 1 ∨ orderOf (2 : ZMod p) = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hdvd2

  have h_ord2 : orderOf (2 : ZMod p) = 2 := by
    rcases hdvd2_cases with h1 | h2
    · exfalso
      have : orderOf (2 : ZMod p) ∣ n := by rw [h1]; exact one_dvd n
      exact hnot_dvd_n this
    · exact h2

  have h2_sq : (2 : ZMod p) ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [h_ord2])

  have h3_zero : (3 : ZMod p) = 0 := by
    calc (3 : ZMod p) = (2 : ZMod p) ^ 2 - 1 := by ring
    _ = 1 - 1 := by rw [h2_sq]
    _ = 0 := by ring

  have hp_dvd_3 : p ∣ 3 :=
    (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h3_zero

  have hp_eq_3 : p = 3 := by
    have := (Nat.dvd_prime Nat.prime_three).mp hp_dvd_3
    rcases this with h1 | h3
    · omega
    · exact h3

  have h3_dvd_n : 3 ∣ n := hp_eq_3 ▸ hp_dvd

  have h3n : 3 ∣ 3 ^ n + 1 := dvd_trans h3_dvd_n h3
  exact h_not_dvd 3 (by decide) h3n
```
