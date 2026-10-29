# GPT-5.6 Sol xHigh (Arena AI)

Model: `gpt-5.6-sol-xhigh` (via Arena AI)\
Date: `8 August 2026`\
Line count: `70`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  have hx_two : 2 ≤ x := hx.two_le
  have hy_two : 2 ≤ y := hy.two_le

  have hxpow : x ∣ x ^ (y - 1) := by
    refine ⟨x ^ (y - 2), ?_⟩
    rw [show y - 1 = (y - 2) + 1 by omega, pow_succ]
    exact Nat.mul_comm _ _

  have hypow : y ∣ y ^ (x - 1) := by
    refine ⟨y ^ (x - 2), ?_⟩
    rw [show x - 1 = (x - 2) + 1 by omega, pow_succ]
    exact Nat.mul_comm _ _

  have dvd_add_cancel_left {a b c : ℕ} (hb : a ∣ b) (hbc : a ∣ b + c) :
      a ∣ c := by
    rcases hb with ⟨k, hk⟩
    rcases hbc with ⟨l, hl⟩
    refine ⟨l - k, ?_⟩
    calc
      c = (b + c) - b := by omega
      _ = a * l - a * k := by rw [hl, hk]
      _ = a * (l - k) := (Nat.mul_sub_left_distrib a l k).symm

  have hnotx : ¬x ∣ x ^ (y - 1) + y ^ (x - 1) := by
    intro hdiv
    have hdivpow : x ∣ y ^ (x - 1) :=
      dvd_add_cancel_left hxpow hdiv
    have hxy : x ∣ y := hx.dvd_of_dvd_pow hdivpow
    rcases (Nat.dvd_prime hy).mp hxy with h | h
    · omega
    · exact hne h

  have hnoty : ¬y ∣ x ^ (y - 1) + y ^ (x - 1) := by
    intro hdiv
    have hdivpow : y ∣ x ^ (y - 1) := by
      apply dvd_add_cancel_left hypow
      simpa [Nat.add_comm] using hdiv
    have hyx : y ∣ x := hy.dvd_of_dvd_pow hdivpow
    rcases (Nat.dvd_prime hx).mp hyx with h | h
    · omega
    · exact hne h.symm

  have hcx : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) x := by
    unfold Nat.Coprime
    rcases
        (Nat.dvd_prime hx).mp
          (Nat.gcd_dvd_right (x ^ (y - 1) + y ^ (x - 1)) x) with hg | hg
    · exact hg
    · exfalso
      apply hnotx
      simpa only [hg] using
        (Nat.gcd_dvd_left (x ^ (y - 1) + y ^ (x - 1)) x)

  have hcy : Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) y := by
    unfold Nat.Coprime
    rcases
        (Nat.dvd_prime hy).mp
          (Nat.gcd_dvd_right (x ^ (y - 1) + y ^ (x - 1)) y) with hg | hg
    · exact hg
    · exfalso
      apply hnoty
      simpa only [hg] using
        (Nat.gcd_dvd_left (x ^ (y - 1) + y ^ (x - 1)) y)

  change Nat.Coprime (x ^ (y - 1) + y ^ (x - 1)) (x * y)
  exact hcx.mul_right hcy
```
