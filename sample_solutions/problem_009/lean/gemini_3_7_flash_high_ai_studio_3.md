# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `27 August 2026`\
Line count: `28`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem eq_one_of_dvd_pow_add_one (n : ℕ) (hn : 0 < n) (h2 : n ∣ 2^n + 1) (h3 : n ∣ 3^n + 1) :
    n = 1 := by
  by_contra hn1
  have nd (a : ℕ) (ha : 2 ≤ a) (han : a ∣ n) (hpow : n ∣ a^n + 1) : False := by
    have := Nat.le_of_dvd (by decide) ((Nat.dvd_add_right (dvd_pow_self a (by omega))).mp (han.trans hpow))
    omega
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime hn1
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h ↦ nd 2 (by omega) (h ▸ Nat.minFac_dvd n) h2
  have hpge : 3 ≤ p := by have := hp.two_le; omega
  have h20 : (2 : ZMod p) ≠ 0 := fun h ↦ by
    have := Nat.le_of_dvd (by decide) ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp h)
    omega
  have hpow : (2 : ZMod p)^n = -1 := by
    have : ((2^n + 1 : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff _ _ _).2 (Nat.minFac_dvd n |>.trans h2)
    push_cast at this; linear_combination this
  have hdc : (orderOf (2 : ZMod p)).Coprime n := Nat.coprime_of_dvd fun q hq hqd hqn ↦ by
    have := Nat.minFac_le_of_dvd hq.two_le hqn
    have := Nat.le_of_dvd (by omega) (hqd.trans (ZMod.orderOf_dvd_card_sub_one h20))
    omega
  have hd2 := hdc.dvd_of_dvd_mul_right (orderOf_dvd_of_pow_eq_one (by rw [pow_mul', hpow, neg_one_sq]))
  have h4 := orderOf_dvd_iff_pow_eq_one.mp hd2
  have hp3 : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp (by linear_combination h4)
  have hp3eq : p = 3 := by have := Nat.le_of_dvd (by decide) hp3; omega
  exact nd 3 (by omega) (hp3eq ▸ Nat.minFac_dvd n) h3
```
