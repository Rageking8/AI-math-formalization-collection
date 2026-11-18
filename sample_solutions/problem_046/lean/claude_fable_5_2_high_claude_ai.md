# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `14 November 2026`\
Line count: `79`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem digit_sum_xyz_bounds (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h_prod : ∃ k : ℕ, 1 ≤ k ∧ x * y * z = 10 ^ k)
      (h_not_pow : (¬ ∃ a : ℕ, x = 10 ^ a) ∨ (¬ ∃ b : ℕ, y = 10 ^ b) ∨ (¬ ∃ c : ℕ, z = 10 ^ c)) :
      (Nat.digits 10 x).sum + (Nat.digits 10 y).sum + (Nat.digits 10 z).sum ≥ 8 := by
  -- peel off the last digit
  have step : ∀ n : ℕ, 0 < n →
      (Nat.digits 10 n).sum = n % 10 + (Nat.digits 10 (n / 10)).sum := by
    intro n hn
    rw [Nat.digits_def' (by norm_num) hn, List.sum_cons]
  -- a positive number has positive digit sum
  have pos : ∀ n : ℕ, 0 < n → 0 < (Nat.digits 10 n).sum := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rw [step n hn]
      by_cases h : n % 10 = 0
      · have := ih (n / 10) (by omega) (by omega)
        omega
      · omega
  -- digit sum 1 forces a power of 10
  have one : ∀ n : ℕ, 0 < n → (Nat.digits 10 n).sum = 1 → ∃ a : ℕ, n = 10 ^ a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn h1
      rw [step n hn] at h1
      by_cases h : n / 10 = 0
      · refine ⟨0, ?_⟩
        rw [h] at h1
        simp at h1
        omega
      · have hp := pos (n / 10) (by omega)
        have hs : (Nat.digits 10 (n / 10)).sum = 1 := by omega
        obtain ⟨a, ha⟩ := ih (n / 10) (by omega) (by omega) hs
        refine ⟨a + 1, ?_⟩
        rw [pow_succ, ← ha]
        omega
  -- digit sum is congruent to the number mod 9
  have mod9 : ∀ n : ℕ, (Nat.digits 10 n).sum % 9 = n % 9 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.eq_zero_or_pos n with h | hn
      · subst h; simp
      · rw [step n hn]
        have := ih (n / 10) (by omega)
        omega
  obtain ⟨k, -, hprod⟩ := h_prod
  have h10 : (10 ^ k) % 9 = 1 := by
    rw [Nat.pow_mod]; simp
  have ha := mod9 x
  have hb := mod9 y
  have hc := mod9 z
  have ha0 := pos x hx
  have hb0 := pos y hy
  have hc0 := pos z hz
  have onex := one x hx
  have oney := one y hy
  have onez := one z hz
  generalize (Nat.digits 10 x).sum = a at *
  generalize (Nat.digits 10 y).sum = b at *
  generalize (Nat.digits 10 z).sum = c at *
  have e1 : a * b % 9 = x * y % 9 := by
    rw [Nat.mul_mod, ha, hb, ← Nat.mul_mod]
  have e2 : a * b * c % 9 = 1 := by
    rw [Nat.mul_mod, e1, hc, ← Nat.mul_mod, hprod, h10]
  by_contra hlt
  have key : a = 1 ∧ b = 1 ∧ c = 1 := by
    have ha5 : a ≤ 5 := by omega
    have hb5 : b ≤ 5 := by omega
    interval_cases a <;> interval_cases b <;> omega
  obtain ⟨rfl, rfl, rfl⟩ := key
  rcases h_not_pow with h | h | h
  · exact h (onex rfl)
  · exact h (oney rfl)
  · exact h (onez rfl)
```
