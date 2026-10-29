# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `26 August 2026`\
Line count: `77`\
Turn count: `4`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum

lemma S_step (n : ℕ) : S n = n % 10 + S (n / 10) := by
  cases n <;> simp [S, Nat.digits_add_two_add_one 8]

lemma S_add_one (n : ℕ) : S (n + 1) ≤ S n + 1 := by
  rw [S_step (n + 1), S_step n]
  rcases show n % 10 = 9 ∨ n % 10 < 9 by omega with h | h
  · have hdiv : (n + 1) / 10 = n / 10 + 1 := by omega
    have hmod : (n + 1) % 10 = 0 := by omega
    have hrec := S_add_one (n / 10)
    rw [hdiv, hmod]
    omega
  · have hdiv : (n + 1) / 10 = n / 10 := by omega
    have hmod : (n + 1) % 10 = n % 10 + 1 := by omega
    rw [hdiv, hmod]
    omega
termination_by n
decreasing_by omega

theorem S_add (a b : ℕ) : S (a + b) ≤ S a + S b := by
  if h : a + b = 0 then
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    rfl
  else
    rw [S_step (a + b), S_step a, S_step b]
    have hrec := S_add (a / 10) (b / 10)
    rcases show (a % 10 + b % 10) / 10 = 0 ∨ (a % 10 + b % 10) / 10 = 1 by omega with hc | hc
    · have hdiv : (a + b) / 10 = a / 10 + b / 10 := by omega
      have hmod : (a + b) % 10 = a % 10 + b % 10 := by omega
      rw [hdiv, hmod]
      omega
    · have hdiv : (a + b) / 10 = (a / 10 + b / 10) + 1 := by omega
      have hmod : (a + b) % 10 + 10 = a % 10 + b % 10 := by omega
      have hone := S_add_one (a / 10 + b / 10)
      rw [hdiv]
      omega
termination_by a + b
decreasing_by omega

lemma S_mul_d (a : ℕ) : ∀ d, S (a * d) ≤ S a * d
  | 0 => by simp [S]
  | d + 1 => by
    have h1 : S (a * (d + 1)) ≤ S (a * d) + S a := S_add (a * d) a
    have h2 := S_mul_d a d
    have h3 : S a * (d + 1) = S a * d + S a := rfl
    omega

lemma S_mul_ten (n : ℕ) : S (n * 10) = S n := by
  rw [S_step (n * 10), Nat.mul_div_left n (by decide)]
  omega

theorem S_mul (a : ℕ) : ∀ b, S (a * b) ≤ S a * S b
  | 0 => by simp [S]
  | b + 1 => by
    have h1 : a * (b + 1) = a * ((b + 1) % 10) + (a * ((b + 1) / 10)) * 10 := by
      nlinarith [Nat.div_add_mod (b + 1) 10]
    have h2 := S_add (a * ((b + 1) % 10)) ((a * ((b + 1) / 10)) * 10)
    rw [S_mul_ten] at h2
    have h3 := S_mul_d a ((b + 1) % 10)
    have h4 := S_mul a ((b + 1) / 10)
    have h5 : S a * S (b + 1) = S a * ((b + 1) % 10) + S a * S ((b + 1) / 10) := by
      rw [S_step (b + 1), Nat.mul_add]
    rw [h1]
    omega
termination_by b => b
decreasing_by omega

lemma S_pow (n : ℕ) : ∀ x, S (n ^ x) ≤ S n ^ x
  | 0 => by rw [pow_zero, pow_zero, S_step]; simp [S]
  | x + 1 => (S_mul (n ^ x) n).trans (Nat.mul_le_mul_right (S n) (S_pow n x))

theorem digit_sum_pow_le (n x : ℕ) (hn : 0 < n) (hx : 0 < x) :
    (Nat.digits 10 (n ^ x)).sum ≤ ((Nat.digits 10 n).sum) ^ x :=
  S_pow n x
```
