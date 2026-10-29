# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `21 August 2026`\
Line count: `9`\
Turn count: `1`

## Note

This solution uses `native_decide`.

## Solution

```lean4
import Mathlib

def R (n d : ℕ) : ℕ := d * ((10 ^ n - 1) / 9)

def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum

theorem digit_sum_rep_digits_expr :
    S ((Nat.sqrt (R 3334 4 - R 1667 8) - 5) ^ 3) = 24994 := by
  native_decide
```
