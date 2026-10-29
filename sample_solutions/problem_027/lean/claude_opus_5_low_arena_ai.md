# Claude Opus 5 Low (Arena AI)

Model: `claude-opus-5-low` (via Arena AI)\
Date: `8 August 2026`\
Line count: `22`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_nat_satisfies_congruence :
    ¬ ∃ n : ℕ, (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) % 65 = 5 := by
  rintro ⟨n, h⟩
  have h5 : (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) % 5 = 0 := by
    have hd : (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) % 5
        = ((29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) % 65) % 5 :=
      (Nat.mod_mod_of_dvd _ (by norm_num)).symm
    rw [hd, h]
  have hdvd : (5 : ℕ) ∣ (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) := Nat.dvd_of_mod_eq_zero h5
  obtain ⟨k, hk⟩ := hdvd
  have hz : ((29 ^ n + 13 * n ^ 4 + 5 * n ^ 3 : ℕ) : ZMod 5) = 0 := by
    rw [hk]
    push_cast
    simp [show (5 : ZMod 5) = 0 from by decide]
  push_cast at hz
  rcases Nat.even_or_odd n with he | ho
  · rw [show (29 : ZMod 5) = -1 from by decide, he.neg_one_pow] at hz
    exact (by decide : ∀ x : ZMod 5, (1 : ZMod 5) + 13 * x ^ 4 + 5 * x ^ 3 ≠ 0) _ hz
  · rw [show (29 : ZMod 5) = -1 from by decide, ho.neg_one_pow] at hz
    exact (by decide : ∀ x : ZMod 5, (-1 : ZMod 5) + 13 * x ^ 4 + 5 * x ^ 3 ≠ 0) _ hz
```
