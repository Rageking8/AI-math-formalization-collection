# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `33`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def R (n d : ℕ) : ℕ := d * ((10 ^ n - 1) / 9)

theorem repdigit_unique_sol_n_one (n : ℕ) (hn : 0 < n) :
    R n 3 ^ 2 - R n 2 = R n 7 ↔ n = 1 := by
  unfold R
  have h10 : 10 ≤ 10 ^ n := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  generalize hm : 10 ^ n = m at h10 ⊢
  constructor
  · intro h
    have hr1 : 1 ≤ (m - 1) / 9 := by omega
    generalize hr : (m - 1) / 9 = r at h hr1
    have hle : 2 * r ≤ (3 * r) ^ 2 := by nlinarith
    have h2 : (3 * r) ^ 2 = 9 * r := by
      generalize (3 * r) ^ 2 = x at h hle ⊢
      omega
    have hle1 : r ≤ 1 := by nlinarith
    have hr_eq : r = 1 := by omega
    by_contra hne
    have hn2 : 2 ≤ n := by omega
    have h100 : 100 ≤ 10 ^ n := by
      calc 100 = 10 ^ 2 := by norm_num
        _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    rw [hm] at h100
    omega
  · intro h
    subst h
    have hm10 : m = 10 := by rw [← hm]; norm_num
    subst hm10
    norm_num
```
