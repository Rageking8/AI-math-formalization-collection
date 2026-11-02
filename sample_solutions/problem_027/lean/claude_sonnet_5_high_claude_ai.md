# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `7 September 2026`\
Line count: `44`\
Turn count: `3`

## Solution

```lean4
import Mathlib

theorem no_nat_satisfies_congruence :
    ¬ ∃ n : ℕ, (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) % 65 = 5 := by
  have e29 : (29 : ZMod 5) = -1 := by decide
  have e13 : (13 : ZMod 5) = 3 := by decide
  have e5 : (5 : ZMod 5) = 0 := by decide
  have c1 : (1 : ZMod 5) + 3 * 0 ^ 4 ≠ 0 := by decide
  have c2 : (1 : ZMod 5) + 3 * 1 ≠ 0 := by decide
  have c3 : (-1 : ZMod 5) + 3 * 0 ^ 4 ≠ 0 := by decide
  have c4 : (-1 : ZMod 5) + 3 * 1 ≠ 0 := by decide
  rintro ⟨n, hn⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdvd : (5 : ℕ) ∣ 65 := by norm_num
  have h5 : (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) % 5 = 0 := by
    have h := Nat.mod_mod_of_dvd (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) hdvd
    rw [hn] at h
    simpa using h.symm
  have hz : ((29 ^ n + 13 * n ^ 4 + 5 * n ^ 3 : ℕ) : ZMod 5) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod 5) 5 (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3)).mpr
      (Nat.dvd_of_mod_eq_zero h5)
  push_cast at hz
  rw [e29, e13, e5, zero_mul, add_zero] at hz
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow] at hz
    rcases eq_or_ne (n : ZMod 5) 0 with h0 | h0
    · rw [h0] at hz
      exact c1 hz
    · have hp : (n : ZMod 5) ^ 4 = 1 := by
        have hpow := ZMod.pow_card_sub_one_eq_one h0
        norm_num at hpow
        exact hpow
      rw [hp] at hz
      exact c2 hz
  · rw [ho.neg_one_pow] at hz
    rcases eq_or_ne (n : ZMod 5) 0 with h0 | h0
    · rw [h0] at hz
      exact c3 hz
    · have hp : (n : ZMod 5) ^ 4 = 1 := by
        have hpow := ZMod.pow_card_sub_one_eq_one h0
        norm_num at hpow
        exact hpow
      rw [hp] at hz
      exact c4 hz
```
