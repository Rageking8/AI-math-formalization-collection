# Claude Opus 5 High (Arena AI)

Model: `claude-opus-5-high` (via Arena AI)\
Date: `25 July 2026`\
Line count: `78`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem eq_one_of_dvd_pow_add_one (n : ℕ) (hn : 0 < n) (h2 : n ∣ 2^n + 1) (h3 : n ∣ 3^n + 1) : n = 1 := by
  by_contra hne
  -- n is odd
  have hodd : n % 2 = 1 := by
    rcases Nat.even_or_odd n with he | ho
    · exfalso
      obtain ⟨k, hk⟩ := he
      have hdvd2 : (2:ℕ) ∣ n := ⟨k, by omega⟩
      obtain ⟨a, ha⟩ := hdvd2.trans h2
      obtain ⟨b, hb⟩ := dvd_pow_self (2:ℕ) hn.ne'
      rw [hb] at ha
      omega
    · exact Nat.odd_iff.mp ho
  obtain ⟨p, hpdef⟩ : ∃ p, p = n.minFac := ⟨n.minFac, rfl⟩
  have hp : p.Prime := by rw [hpdef]; exact Nat.minFac_prime hne
  have hpn : p ∣ n := by rw [hpdef]; exact Nat.minFac_dvd n
  have hmin : ∀ q : ℕ, 2 ≤ q → q ∣ n → p ≤ q := by
    intro q hq hqn
    rw [hpdef]
    exact Nat.minFac_le_of_dvd hq hqn
  haveI : Fact p.Prime := ⟨hp⟩
  have hone : (1 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((1:ℕ) : ZMod p) = 0 := by rw [Nat.cast_one]; exact h
    have hle := Nat.le_of_dvd Nat.one_pos ((CharP.cast_eq_zero_iff (ZMod p) p 1).mp h')
    have := hp.two_le
    omega
  have h2z : (2 : ZMod p) ^ n = -1 := by
    have hc : ((2 ^ n + 1 : ℕ) : ZMod p) = 0 := by
      rw [CharP.cast_eq_zero_iff (ZMod p) p]
      exact hpn.trans h2
    push_cast at hc
    linear_combination hc
  have h3z : (3 : ZMod p) ^ n = -1 := by
    have hc : ((3 ^ n + 1 : ℕ) : ZMod p) = 0 := by
      rw [CharP.cast_eq_zero_iff (ZMod p) p]
      exact hpn.trans h3
    push_cast at hc
    linear_combination hc
  have h6 : (6 : ZMod p) ^ n = 1 := by
    have h63 : (6 : ZMod p) = 2 * 3 := by norm_num
    rw [h63, mul_pow, h2z, h3z]
    norm_num
  have h6ne : (6 : ZMod p) ≠ 0 := by
    intro h
    have hzp : (0 : ZMod p) ^ n = 0 := by
      apply zero_pow
      omega
    rw [h, hzp] at h6
    exact hone h6.symm
  have hdn : orderOf (6 : ZMod p) ∣ n := orderOf_dvd_of_pow_eq_one h6
  have hdp : orderOf (6 : ZMod p) ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h6ne)
  have hord1 : orderOf (6 : ZMod p) = 1 := by
    by_contra hd1
    have hq : (orderOf (6 : ZMod p)).minFac.Prime := Nat.minFac_prime hd1
    have hqn : (orderOf (6 : ZMod p)).minFac ∣ n := (Nat.minFac_dvd _).trans hdn
    have hle : p ≤ (orderOf (6 : ZMod p)).minFac := hmin _ hq.two_le hqn
    have hqp : (orderOf (6 : ZMod p)).minFac ∣ p - 1 := (Nat.minFac_dvd _).trans hdp
    have hp2 := hp.two_le
    have hle2 : (orderOf (6 : ZMod p)).minFac ≤ p - 1 := Nat.le_of_dvd (by omega) hqp
    omega
  have h61 : (6 : ZMod p) = 1 := orderOf_eq_one_iff.mp hord1
  have h5p : (5 : ZMod p) = 0 := by linear_combination h61
  obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  rw [hk] at h2z
  have hkey : ((2 : ZMod p) ^ 2) ^ k * 2 = -1 := by
    rw [← pow_mul, ← pow_succ]
    exact h2z
  have h22 : (2 : ZMod p) ^ 2 = -1 := by linear_combination h5p
  rw [h22] at hkey
  rcases Nat.even_or_odd k with hk2 | hk2
  · rw [hk2.neg_one_pow] at hkey
    exact hone (by linear_combination 2 * hkey - h5p)
  · rw [hk2.neg_one_pow] at hkey
    exact hone (by linear_combination -hkey)
```
