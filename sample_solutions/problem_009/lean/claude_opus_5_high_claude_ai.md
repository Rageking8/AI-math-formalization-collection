# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `11 August 2026`\
Line count: `29`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem eq_one_of_dvd_pow_add_one (n : ℕ) (hn : 0 < n) (h2 : n ∣ 2^n + 1) (h3 : n ∣ 3^n + 1) :
    n = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpn, hm⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ ∀ q, q.Prime → q ∣ n → p ≤ q :=
    ⟨n.minFac, Nat.minFac_prime hne, n.minFac_dvd, fun _ h g => Nat.minFac_le_of_dvd h.two_le g⟩
  haveI := Fact.mk hp
  have k : (2 : ZMod p) ^ n + 1 = 0 := by
    have h := (CharP.cast_eq_zero_iff (ZMod p) p _).mpr (hpn.trans h2); push_cast at h; exact h
  have h0 : (2 : ZMod p) ≠ 0 := fun h => by
    rw [h, zero_pow hn.ne', zero_add] at k; exact one_ne_zero k
  have hc : Nat.Coprime n (p - 1) := by
    by_contra g
    have hq := Nat.minFac_prime (g : Nat.gcd n (p - 1) ≠ 1)
    have a1 := hm _ hq ((Nat.minFac_dvd _).trans (Nat.gcd_dvd_left n (p - 1)))
    have a2 := Nat.le_of_dvd (by have := hp.two_le; omega)
      ((Nat.minFac_dvd _).trans (Nat.gcd_dvd_right n (p - 1)))
    have := hp.two_le; omega
  have hs : (2 : ZMod p) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp
    ((Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one
      (ZMod.pow_card_sub_one_eq_one h0)) hc.symm).dvd_of_dvd_mul_right
      (orderOf_dvd_of_pow_eq_one (by
        rw [two_mul, pow_add]; linear_combination ((2 : ZMod p) ^ n - 1) * k)))
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
    ((CharP.cast_eq_zero_iff (ZMod p) p 3).mp (by push_cast; linear_combination hs))
  obtain ⟨a, ha⟩ := (hp3 ▸ hpn : (3 : ℕ) ∣ n).trans h3
  obtain ⟨b, hb⟩ : (3 : ℕ) ∣ 3 ^ n := dvd_pow_self 3 hn.ne'
  omega
```
