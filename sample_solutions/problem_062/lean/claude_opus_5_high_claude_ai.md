# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `18 August 2026`\
Line count: `61`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem no_pos_int_digit_prod_eq :
    ¬ ∃ n : ℕ, 0 < n ∧ ((Nat.digits 10 (n + 3)).prod : ℝ) /
      (((Nat.digits 10 (n + 5)).prod : ℝ) - 6) = (n : ℝ) ^ 2 := by
  -- Auxiliary: the product of the digits of `m` is at most `m`.
  have key : ∀ N m : ℕ, m ≤ N → m ≠ 0 → (Nat.digits 10 m).prod ≤ m := by
    intro N
    induction N with
    | zero => intro m hm h0; exact absurd (Nat.le_zero.mp hm) h0
    | succ N ih =>
      intro m hmN hm0
      rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) (Nat.pos_of_ne_zero hm0)]
      rcases Nat.lt_or_ge m 10 with hlt | hge
      · have hd : m / 10 = 0 := by omega
        have hmod : m % 10 = m := by omega
        rw [hd, hmod]
        simp
      · have h1 : m / 10 ≠ 0 := by omega
        have h2 : m / 10 ≤ N := by omega
        have h3 := ih (m / 10) h2 h1
        rw [List.prod_cons]
        calc m % 10 * (Nat.digits 10 (m / 10)).prod ≤ 9 * (m / 10) :=
              Nat.mul_le_mul (by omega) h3
          _ ≤ m := by omega
  have key' : ∀ m : ℕ, m ≠ 0 → (Nat.digits 10 m).prod ≤ m := fun m => key m m le_rfl
  rintro ⟨n, hn, h⟩
  rcases Nat.lt_or_ge n 3 with hsmall | hbig
  · interval_cases n <;> norm_num [Nat.digits_def'] at h
  · have hQ0 := key' (n + 3) (by omega)
    have hQle : ((Nat.digits 10 (n + 3)).prod : ℝ) ≤ (n : ℝ) + 3 := by
      calc ((Nat.digits 10 (n + 3)).prod : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := Nat.cast_le.mpr hQ0
        _ = (n : ℝ) + 3 := by push_cast; ring
    have hn3 : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hbig
    have hnpos : (0:ℝ) < (n:ℝ) := by linarith
    have hsq : (0:ℝ) < (n:ℝ) ^ 2 := pow_pos hnpos 2
    rcases lt_trichotomy ((Nat.digits 10 (n + 5)).prod) 6 with hc | hc | hc
    · -- denominator negative, numerator nonnegative
      have hPR : ((Nat.digits 10 (n + 5)).prod : ℝ) < 6 := by
        calc ((Nat.digits 10 (n + 5)).prod : ℝ) < ((6 : ℕ) : ℝ) := Nat.cast_lt.mpr hc
          _ = 6 := by norm_num
      have hne : ((Nat.digits 10 (n + 5)).prod : ℝ) - 6 ≠ 0 := by intro hz; linarith
      rw [div_eq_iff hne] at h
      have h1 : (0:ℝ) ≤ ((Nat.digits 10 (n + 3)).prod : ℝ) := Nat.cast_nonneg _
      have h2 : ((Nat.digits 10 (n + 5)).prod : ℝ) - 6 < 0 := by linarith
      have h4 := mul_neg_of_pos_of_neg hsq h2
      linarith
    · -- denominator zero, so the quotient is `0`
      have h6 : ((Nat.digits 10 (n + 5)).prod : ℝ) - 6 = 0 := by rw [hc]; norm_num
      rw [h6, div_zero] at h
      linarith
    · -- denominator at least one, so `n ^ 2 ≤ digit product ≤ n + 3`
      have h7' : (7:ℕ) ≤ (Nat.digits 10 (n + 5)).prod := by omega
      have h7 : (7:ℝ) ≤ ((Nat.digits 10 (n + 5)).prod : ℝ) := by
        calc (7:ℝ) = ((7 : ℕ) : ℝ) := by norm_num
          _ ≤ ((Nat.digits 10 (n + 5)).prod : ℝ) := Nat.cast_le.mpr h7'
      have hne : ((Nat.digits 10 (n + 5)).prod : ℝ) - 6 ≠ 0 := by intro hz; linarith
      rw [div_eq_iff hne] at h
      have h1 : (1:ℝ) ≤ ((Nat.digits 10 (n + 5)).prod : ℝ) - 6 := by linarith
      have h2 := le_mul_of_one_le_right hsq.le h1
      nlinarith [mul_nonneg hnpos.le (by linarith : (0:ℝ) ≤ (n:ℝ) - 3)]
```
