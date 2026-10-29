# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `26 August 2026`\
Line count: `86`\
Turn count: `2`

## Solution

```lean4
import Mathlib

private def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum

private lemma S_zero : S 0 = 0 := by
  dsimp [S]
  rw [Nat.digits_zero, List.sum_nil]

private lemma S_def (n : ℕ) : S n = n % 10 + S (n / 10) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [S_zero]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have h10 : 2 ≤ 10 := by omega
    dsimp [S]
    rw [Nat.digits_of_two_le_of_pos h10 hpos, List.sum_cons]

private lemma S_le_self (n : ℕ) : S n ≤ n :=
  Nat.digit_sum_le 10 n

private lemma S_add (a b : ℕ) : S (a + b) ≤ S a + S b := by
  by_cases h : a + b = 0
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    simp [S_zero]
  · rw [S_def (a + b), S_def a, S_def b]
    have hdiv : (a + b) / 10 = a / 10 + b / 10 + (a % 10 + b % 10) / 10 := by omega
    have hmod : (a + b) % 10 = (a % 10 + b % 10) % 10 := by omega
    rw [hdiv, hmod]
    have ih1 := S_add (a / 10 + b / 10) ((a % 10 + b % 10) / 10)
    have ih2 := S_add (a / 10) (b / 10)
    have hS_rem : S ((a % 10 + b % 10) / 10) ≤ (a % 10 + b % 10) / 10 := S_le_self _
    omega
termination_by a + b
decreasing_by
  all_goals omega

private lemma S_mul_const (k b : ℕ) : S (k * b) ≤ k * S b := by
  induction k with
  | zero =>
    simp [S_zero]
  | succ k ih =>
    have h : (k + 1) * b = k * b + b := by ring
    have h2 : (k + 1) * S b = k * S b + S b := by ring
    rw [h, h2]
    have h1 := S_add (k * b) b
    omega

private lemma S_mul_ten (m : ℕ) : S (10 * m) = S m := by
  rw [S_def (10 * m)]
  have hmod : (10 * m) % 10 = 0 := by omega
  have hdiv : (10 * m) / 10 = m := by omega
  rw [hmod, hdiv, Nat.zero_add]

private lemma S_mul (a b : ℕ) : S (a * b) ≤ S a * S b := by
  by_cases ha : a = 0
  · subst ha
    simp [S_zero]
  · have ha_div : a = a % 10 + 10 * (a / 10) := by omega
    have h_decomp : a * b = (a % 10) * b + 10 * (a / 10 * b) := by
      nth_rw 1 [ha_div]
      ring
    rw [h_decomp]
    have h_add := S_add ((a % 10) * b) (10 * (a / 10 * b))
    rw [S_mul_ten (a / 10 * b)] at h_add
    have h_mod := S_mul_const (a % 10) b
    have ih := S_mul (a / 10) b
    rw [S_def a]
    have h_distrib : (a % 10 + S (a / 10)) * S b = (a % 10) * S b + S (a / 10) * S b := by ring
    rw [h_distrib]
    omega
termination_by a
decreasing_by
  omega

theorem digit_sum_pow_le (n x : ℕ) (hn : 0 < n) (hx : 0 < x) :
    (Nat.digits 10 (n ^ x)).sum ≤ ((Nat.digits 10 n).sum) ^ x := by
  rcases x with _ | k
  · omega
  · clear hx hn
    change S (n ^ (k + 1)) ≤ (S n) ^ (k + 1)
    induction k with
    | zero =>
      rw [show n ^ (0 + 1) = n from Nat.pow_one n,
          show (S n) ^ (0 + 1) = S n from Nat.pow_one (S n)]
    | succ k ih =>
      rw [Nat.pow_succ n (k + 1), Nat.pow_succ (S n) (k + 1)]
      exact le_trans (S_mul (n ^ (k + 1)) n) (Nat.mul_le_mul_right (S n) ih)
```
