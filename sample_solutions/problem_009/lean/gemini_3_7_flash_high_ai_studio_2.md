# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `27 August 2026`\
Line count: `93`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem eq_one_of_dvd_pow_add_one (n : ℕ) (hn : 0 < n) (h2 : n ∣ 2^n + 1) (h3 : n ∣ 3^n + 1) :
    n = 1 := by
  by_contra hn1
  have hn_gt1 : 1 < n := by omega
  set p := n.minFac
  have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
  have hp_ge_2 : 2 ≤ p := hp_prime.two_le
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hp2 : p ∣ 2^n + 1 := dvd_trans hpn h2
  have hp3 : p ∣ 3^n + 1 := dvd_trans hpn h3
  have hp_ne_2 : p ≠ 2 := by
    intro hp_eq_2
    have h2_dvd : 2 ∣ 2^n + 1 := hp_eq_2 ▸ hp2
    have h2_pow : 2 ∣ 2^n := dvd_pow_self 2 (by omega)
    have h2_one : 2 ∣ 1 := (Nat.dvd_add_right h2_pow).mp h2_dvd
    have : 2 ≤ 1 := Nat.le_of_dvd zero_lt_one h2_one
    omega
  have h2_ne_zero : (2 : ZMod p) ≠ 0 := by
    intro hp2_eq
    have hp2_dvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (hp2_eq : ((2 : ℕ) : ZMod p) = 0)
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hp2_dvd
    have : p = 2 := by omega
    exact hp_ne_2 this
  have hd_dvd_p_sub_one : orderOf (2 : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one h2_ne_zero
  have h_pow_2n : (2 : ZMod p) ^ (2 * n) = 1 := by
    have h_plus_one : (((2^n + 1 : ℕ) : ZMod p)) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p (2^n + 1)).mpr hp2
    have h_pow_n : (2 : ZMod p)^n = -1 := by
      push_cast at h_plus_one
      linear_combination h_plus_one
    calc (2 : ZMod p) ^ (2 * n) = ((2 : ZMod p) ^ n) ^ 2 := by rw [mul_comm 2 n, pow_mul]
    _ = (-1 : ZMod p) ^ 2 := by rw [h_pow_n]
    _ = 1 := by ring
  have hd_dvd_2n : orderOf (2 : ZMod p) ∣ 2 * n :=
    orderOf_dvd_of_pow_eq_one h_pow_2n
  have h_coprime : Nat.Coprime n (p - 1) := by
    by_contra hc
    have hg_pos : 0 < Nat.gcd n (p - 1) := Nat.gcd_pos_of_pos_right n (by omega)
    have hg_gt_one : 1 < Nat.gcd n (p - 1) := by
      have hg_ne_one : Nat.gcd n (p - 1) ≠ 1 := hc
      omega
    set q := (Nat.gcd n (p - 1)).minFac
    have hq_prime : q.Prime := Nat.minFac_prime (by omega)
    have hq_dvd_g : q ∣ Nat.gcd n (p - 1) := Nat.minFac_dvd (Nat.gcd n (p - 1))
    have hq_dvd_n : q ∣ n := dvd_trans hq_dvd_g (Nat.gcd_dvd_left n (p - 1))
    have hq_dvd_p_sub_one : q ∣ p - 1 := dvd_trans hq_dvd_g (Nat.gcd_dvd_right n (p - 1))
    have hp_le_q : p ≤ q := Nat.minFac_le_of_dvd hq_prime.two_le hq_dvd_n
    have hq_le_p_sub_one : q ≤ p - 1 := Nat.le_of_dvd (by omega) hq_dvd_p_sub_one
    omega
  have hd_dvd_gcd : orderOf (2 : ZMod p) ∣ Nat.gcd (2 * n) (p - 1) :=
    Nat.dvd_gcd hd_dvd_2n hd_dvd_p_sub_one
  have h_gcd_eq : Nat.gcd (2 * n) (p - 1) = Nat.gcd 2 (p - 1) :=
    h_coprime.gcd_mul_right_cancel 2
  have hd_dvd_2 : orderOf (2 : ZMod p) ∣ 2 :=
    dvd_trans (h_gcd_eq ▸ hd_dvd_gcd) (Nat.gcd_dvd_left 2 (p - 1))
  have hd_le : orderOf (2 : ZMod p) ≤ 2 := Nat.le_of_dvd (by decide) hd_dvd_2
  have hd_ne_zero : orderOf (2 : ZMod p) ≠ 0 := by
    intro h0
    have hz : 0 ∣ 2 := h0 ▸ hd_dvd_2
    rcases hz with ⟨c, hc⟩
    omega
  have hd_cases : orderOf (2 : ZMod p) = 1 ∨ orderOf (2 : ZMod p) = 2 := by omega
  rcases hd_cases with hd1 | hd2
  · have h2_eq_1 : (2 : ZMod p) = 1 := by
      have : orderOf (2 : ZMod p) = 1 := hd1
      exact orderOf_eq_one_iff.mp this
    have h1_eq_0 : ((1 : ℕ) : ZMod p) = 0 := by
      calc ((1 : ℕ) : ZMod p) = (2 : ZMod p) - 1 := by ring
      _ = 1 - 1 := by rw [h2_eq_1]
      _ = 0 := by ring
    have hp_dvd_1 : p ∣ 1 := (CharP.cast_eq_zero_iff (ZMod p) p 1).mp h1_eq_0
    have : p ≤ 1 := Nat.le_of_dvd zero_lt_one hp_dvd_1
    omega
  · have h4_eq_1 : (2 : ZMod p) ^ 2 = 1 := by
      have : (2 : ZMod p) ^ (orderOf (2 : ZMod p)) = 1 := pow_orderOf_eq_one (2 : ZMod p)
      rwa [hd2] at this
    have h3_eq_0 : ((3 : ℕ) : ZMod p) = 0 := by
      calc ((3 : ℕ) : ZMod p) = (2 : ZMod p) ^ 2 - 1 := by ring
      _ = 1 - 1 := by rw [h4_eq_1]
      _ = 0 := by ring
    have hp_dvd_3 : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h3_eq_0
    have hp_le_3 : p ≤ 3 := Nat.le_of_dvd (by decide) hp_dvd_3
    have hp_eq_3 : p = 3 := by omega
    have h3_dvd_n : 3 ∣ n := hp_eq_3 ▸ hpn
    have h3_dvd_3n_add_1 : 3 ∣ 3^n + 1 := dvd_trans h3_dvd_n h3
    have h3_dvd_3n : 3 ∣ 3^n := dvd_pow_self 3 (by omega)
    have h3_dvd_1 : 3 ∣ 1 := (Nat.dvd_add_right h3_dvd_3n).mp h3_dvd_3n_add_1
    have : 3 ≤ 1 := Nat.le_of_dvd zero_lt_one h3_dvd_1
    omega
```
