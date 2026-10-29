# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `1 August 2026`\
Line count: `76`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem eq_one_of_dvd_pow_add_one (n : ℕ) (hn : 0 < n) (h2 : n ∣ 2^n + 1) (h3 : n ∣ 3^n + 1) :
    n = 1 := by
  by_contra hne
  have h2n : ¬ (2 ∣ n) := by
    intro hdvd
    have hd2 : (2:ℕ) ∣ 2^n + 1 := hdvd.trans h2
    have hpow : (2:ℕ) ∣ 2^n := dvd_pow_self 2 hn.ne'
    obtain ⟨a, ha⟩ := hpow
    obtain ⟨b, hb⟩ := hd2
    omega
  have h3n : ¬ (3 ∣ n) := by
    intro hdvd
    have hd3 : (3:ℕ) ∣ 3^n + 1 := hdvd.trans h3
    have hpow : (3:ℕ) ∣ 3^n := dvd_pow_self 3 hn.ne'
    obtain ⟨a, ha⟩ := hpow
    obtain ⟨b, hb⟩ := hd3
    omega
  set p := n.minFac with hp_def
  have hp_prime : p.Prime := Nat.minFac_prime hne
  have hp_dvd : p ∣ n := Nat.minFac_dvd n
  have hp_ne2 : p ≠ 2 := by
    intro h
    apply h2n
    rw [← h]
    exact hp_dvd
  have hpdvd2 : p ∣ 2^n + 1 := hp_dvd.trans h2
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have key2 : (2 : ZMod p)^n = -1 := by
    have h := (CharP.cast_eq_zero_iff (ZMod p) p (2^n+1)).mpr hpdvd2
    push_cast at h
    linear_combination h
  have key2' : (2 : ZMod p)^(2*n) = 1 := by
    have heq2 : (2:ZMod p)^(2*n) = (2:ZMod p)^n * (2:ZMod p)^n := by
      rw [two_mul, pow_add]
    rw [heq2, key2]
    ring
  have h2ne0 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h2cast : ((2:ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2cast
    have heqp : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp hp2
    exact hp_ne2 heqp
  have hfermat : (2 : ZMod p)^(p-1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne0
  have hd_dvd_p1 : orderOf (2 : ZMod p) ∣ p - 1 := orderOf_dvd_of_pow_eq_one hfermat
  have hd_dvd_2n : orderOf (2 : ZMod p) ∣ 2*n := orderOf_dvd_of_pow_eq_one key2'
  have hp2le : 2 ≤ p := hp_prime.two_le
  have hcop : Nat.Coprime (orderOf (2:ZMod p)) n := by
    by_contra hg
    have hg' : Nat.gcd (orderOf (2:ZMod p)) n ≠ 1 := hg
    obtain ⟨q, hqp, hqdvd⟩ := Nat.exists_prime_and_dvd hg'
    have hqd : q ∣ orderOf (2:ZMod p) := hqdvd.trans (Nat.gcd_dvd_left _ _)
    have hqn : q ∣ n := hqdvd.trans (Nat.gcd_dvd_right _ _)
    have hqp1 : q ∣ p - 1 := hqd.trans hd_dvd_p1
    have hp1pos : 0 < p - 1 := by omega
    have hq_le : q ≤ p - 1 := Nat.le_of_dvd hp1pos hqp1
    have hp_le : p ≤ q := Nat.minFac_le_of_dvd hqp.two_le hqn
    omega
  have hd_dvd_2 : orderOf (2:ZMod p) ∣ 2 := hcop.dvd_of_dvd_mul_right hd_dvd_2n
  rcases (Nat.dvd_prime Nat.prime_two).mp hd_dvd_2 with hd1 | hd2
  · exfalso
    have h21 : (2:ZMod p) = 1 := orderOf_eq_one_iff.mp hd1
    have h10 : (1:ZMod p) = 0 := by linear_combination h21
    have hcast : ((1:ℕ):ZMod p) = 0 := by exact_mod_cast h10
    have hp1 : p ∣ 1 := (CharP.cast_eq_zero_iff (ZMod p) p 1).mp hcast
    exact hp_prime.one_lt.ne' (Nat.dvd_one.mp hp1)
  · have h22 : (2:ZMod p)^2 = 1 := by
      have hh := pow_orderOf_eq_one (2:ZMod p)
      rwa [hd2] at hh
    have h30 : (3:ZMod p) = 0 := by linear_combination h22
    have hcast3 : ((3:ℕ):ZMod p) = 0 := by exact_mod_cast h30
    have hp3 : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp hcast3
    have hpeq3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_three).mp hp3
    rw [hpeq3] at hp_dvd
    exact h3n hp_dvd
```
