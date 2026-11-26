# Claude Opus 5.5 High (Claude AI)

Model: `Claude Opus 5.5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `59`\
Turn count: `3`

## Solution

```lean4
import Mathlib

theorem eq_one_of_dvd_pow_add_one (n : ℕ) (hn : 0 < n) (h2 : n ∣ 2^n + 1) (h3 : n ∣ 3^n + 1) :
    n = 1 := by
  by_contra hne
  have hp : n.minFac.Prime := Nat.minFac_prime hne
  set p := n.minFac with hpdef
  have hpn : p ∣ n := Nat.minFac_dvd n
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by
    intro h
    have h2n : 2 ∣ n := by rw [← h]; exact hpn
    have ha : 2 ∣ 2^n + 1 := dvd_trans h2n h2
    have hb : 2 ∣ 2^n := dvd_pow_self 2 hn.ne'
    generalize 2^n = m at *
    omega
  have hp3 : p ≠ 3 := by
    intro h
    have h3n : 3 ∣ n := by rw [← h]; exact hpn
    have ha : 3 ∣ 3^n + 1 := dvd_trans h3n h3
    have hb : 3 ∣ 3^n := dvd_pow_self 3 hn.ne'
    generalize 3^n = m at *
    omega
  have hcop : Nat.Coprime n (p - 1) := by
    apply Nat.coprime_of_dvd
    intro q hq hqn hqp
    have h1 : p ≤ q := Nat.minFac_le_of_dvd hq.two_le hqn
    have := hp.two_le
    have h2' : q ≤ p - 1 := Nat.le_of_dvd (by omega) hqp
    omega
  have hpow : (2 : ZMod p)^n = -1 := by
    have : ((2^n + 1 : ℕ) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p _).mpr (dvd_trans hpn h2)
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2:ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hA : (2 : ZMod p)^(2*n) = 1 := by
    rw [pow_mul', hpow]
    first
      | exact neg_one_sq
      | ring
      | simp
  have hB : (2 : ZMod p)^(p-1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  have hg : (2 : ZMod p)^(Nat.gcd (2*n) (p-1)) = 1 := pow_gcd_eq_one.mpr ⟨hA, hB⟩
  have hgd : Nat.gcd (2*n) (p-1) ∣ 2 := by
    have hc : (Nat.gcd (2*n) (p-1)).Coprime n :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) hcop.symm
    exact hc.dvd_of_dvd_mul_right (Nat.gcd_dvd_left _ _)
  obtain ⟨k, hk⟩ := hgd
  have h4 : (2 : ZMod p)^2 = 1 := by rw [hk, pow_mul, hg, one_pow]
  have h3z : ((3:ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination h4
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h3z
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3z)
```
