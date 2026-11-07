# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `52`\
Turn count: `1`

## Solution

```lean4
import Mathlib

lemma digits_prod_le_self : ∀ m : ℕ, 0 < m → (Nat.digits 10 m).prod ≤ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rw [Nat.digits_def' (by norm_num) hm, List.prod_cons]
    by_cases h : m / 10 = 0
    · rw [h, Nat.digits_zero, List.prod_nil, mul_one]
      exact Nat.mod_le _ _
    · have h1 : 0 < m / 10 := Nat.pos_of_ne_zero h
      have h2 := ih (m / 10) (Nat.div_lt_self hm (by norm_num)) h1
      have h3 : m % 10 < 10 := Nat.mod_lt _ (by norm_num)
      calc m % 10 * (Nat.digits 10 (m / 10)).prod ≤ 9 * (m / 10) :=
            Nat.mul_le_mul (by omega) h2
        _ ≤ m := by omega

theorem no_pos_int_digit_prod_eq :
    ¬ ∃ n : ℕ, 0 < n ∧ ((Nat.digits 10 (n + 3)).prod : ℝ) /
      (((Nat.digits 10 (n + 5)).prod : ℝ) - 6) = (n : ℝ) ^ 2 := by
  rintro ⟨n, hn, h⟩
  have key : n ≤ 2 := by
    have ha : (Nat.digits 10 (n + 3)).prod ≤ n + 3 :=
      digits_prod_le_self _ (by omega)
    generalize (Nat.digits 10 (n + 3)).prod = a at ha h
    generalize (Nat.digits 10 (n + 5)).prod = b at h
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    by_cases hb : (b : ℝ) - 6 = 0
    · rw [hb, div_zero] at h
      have : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      linarith
    · rw [div_eq_iff hb] at h
      have hb6 : b ≠ 6 := by
        rintro rfl
        apply hb
        norm_num
      have hcases : b ≤ 5 ∨ 7 ≤ b := by omega
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      rcases hcases with hb5 | hb7
      · have hb5' : (b : ℝ) ≤ 5 := by exact_mod_cast hb5
        have := mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.2 hb5')
        nlinarith
      · have hb7' : (7 : ℝ) ≤ b := by exact_mod_cast hb7
        have := mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.2 hb7')
        have hane : (a : ℝ) ≤ n + 3 := by exact_mod_cast ha
        have hsq : (n : ℝ) ^ 2 ≤ n + 3 := by nlinarith
        by_contra hcon
        push_neg at hcon
        have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hcon
        nlinarith
  interval_cases n <;> norm_num at h
```
