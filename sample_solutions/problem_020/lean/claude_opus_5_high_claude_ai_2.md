# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `12 August 2026`\
Line count: `80`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

private abbrev S (n : ℕ) : ℕ := (Nat.digits 10 n).sum

private theorem sr (n : ℕ) : S n = n % 10 + S (n / 10) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [S, h]
  · simp [S, Nat.digits_def' (by norm_num : (1:ℕ) < 10) h]

private theorem st (n : ℕ) : S (10 * n) = S n := by
  have h := sr (10 * n)
  rw [show 10 * n % 10 = 0 by omega, show 10 * n / 10 = n by omega] at h
  omega

private theorem sa (a b : ℕ) : S (a + b) ≤ S a + S b := by
  have H : ∀ N a b : ℕ, a + b ≤ N → S (a + b) ≤ S a + S b := by
    intro N; induction N with
    | zero =>
      intro a b h
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
      simp [S]
    | succ N ih =>
      intro a b h
      have h1 := sr (a + b); have h2 := sr a; have h3 := sr b
      rw [show (a+b)/10 = a/10 + b/10 + (a%10 + b%10)/10 by omega] at h1
      have i1 := ih (a/10 + b/10) ((a%10 + b%10)/10) (by omega)
      have i2 := ih (a/10) (b/10) (by omega)
      have i3 : S ((a%10 + b%10)/10) ≤ (a%10 + b%10)/10 := Nat.digit_sum_le 10 _
      omega
  exact H (a + b) a b le_rfl

private theorem sc (c b : ℕ) : S (c * b) ≤ c * S b := by
  induction c with
  | zero => simp [S]
  | succ c ih =>
    calc S ((c + 1) * b) = S (c * b + b) := by rw [add_mul, one_mul]
      _ ≤ S (c * b) + S b := sa _ _
      _ ≤ c * S b + S b := Nat.add_le_add_right ih _
      _ = (c + 1) * S b := by ring

private theorem sm (a b : ℕ) : S (a * b) ≤ S a * S b := by
  have H : ∀ N a b : ℕ, a ≤ N → S (a * b) ≤ S a * S b := by
    intro N; induction N with
    | zero =>
      intro a b h
      obtain rfl : a = 0 := by omega
      simp [S]
    | succ N ih =>
      intro a b h
      have key : a * b = 10 * (a / 10 * b) + a % 10 * b := by
        have e : 10 * (a / 10) + a % 10 = a := by omega
        calc a * b = (10 * (a / 10) + a % 10) * b := by rw [e]
          _ = 10 * (a / 10 * b) + a % 10 * b := by ring
      rw [key, sr a]
      calc S (10 * (a / 10 * b) + a % 10 * b)
          ≤ S (10 * (a / 10 * b)) + S (a % 10 * b) := sa _ _
        _ = S (a / 10 * b) + S (a % 10 * b) := by rw [st]
        _ ≤ S (a / 10) * S b + a % 10 * S b :=
          Nat.add_le_add (ih (a / 10) b (by omega)) (sc _ _)
        _ = (a % 10 + S (a / 10)) * S b := by ring
  exact H a a b le_rfl

private theorem sp (n k : ℕ) : S (n ^ k) ≤ S n ^ k := by
  induction k with
  | zero => simp only [pow_zero]; exact Nat.digit_sum_le 10 1
  | succ k ih =>
    calc S (n ^ (k + 1)) = S (n ^ k * n) := by rw [pow_succ]
      _ ≤ S (n ^ k) * S n := sm _ _
      _ ≤ S n ^ k * S n := Nat.mul_le_mul ih le_rfl
      _ = S n ^ (k + 1) := (pow_succ _ _).symm

theorem digit_sum_polynomial_le (P : Polynomial ℕ) (n : ℕ) (hn : 0 < n) :
    (Nat.digits 10 (P.eval n)).sum ≤ P.eval (Nat.digits 10 n).sum := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact (sa _ _).trans (Nat.add_le_add hp hq)
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    exact (sc _ _).trans (Nat.mul_le_mul le_rfl (sp n k))
```
