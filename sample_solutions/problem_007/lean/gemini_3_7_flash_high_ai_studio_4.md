# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `26 August 2026`\
Line count: `54`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

private lemma d_eq (n : ℕ) : (Nat.digits 10 n).sum = n % 10 + (Nat.digits 10 (n / 10)).sum := by
  rcases n with _|n
  · rfl
  · rw [Nat.digits_def' (by decide) (Nat.succ_pos n)]; rfl

private lemma d_add (a b : ℕ) :
    (Nat.digits 10 (a + b)).sum ≤ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum := by
  if h : a + b = 0 then
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    rfl
  else
    have h1 : (a + b) / 10 = a / 10 + b / 10 + (a % 10 + b % 10) / 10 := by omega
    rw [d_eq (a + b), h1, d_eq a, d_eq b]
    have := d_add (a / 10 + b / 10) ((a % 10 + b % 10) / 10)
    have := d_add (a / 10) (b / 10)
    have := Nat.digit_sum_le 10 ((a % 10 + b % 10) / 10)
    omega
termination_by a + b

private lemma d_smul (k b : ℕ) : (Nat.digits 10 (k * b)).sum ≤ k * (Nat.digits 10 b).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.succ_mul]
    exact (d_add (k * b) b).trans (Nat.add_le_add_right ih _)

private lemma d_mul_ten (m : ℕ) : (Nat.digits 10 (10 * m)).sum = (Nat.digits 10 m).sum := by
  have h_div : (10 * m) / 10 = m := by omega
  have h_mod : (10 * m) % 10 = 0 := by omega
  rw [d_eq, h_div, h_mod, Nat.zero_add]

private lemma d_mul (a b : ℕ) :
    (Nat.digits 10 (a * b)).sum ≤ (Nat.digits 10 a).sum * (Nat.digits 10 b).sum := by
  if h : a = 0 then simp [h] else
  have h1 : a * b = (a % 10) * b + 10 * (a / 10 * b) := by
    nth_rw 1 [← Nat.mod_add_div a 10]; ring
  rw [h1, d_eq a]
  have h2 := d_add ((a % 10) * b) (10 * (a / 10 * b))
  have h3 := d_smul (a % 10) b
  have h4 := d_mul (a / 10) b
  have h5 := d_mul_ten (a / 10 * b)
  nlinarith
termination_by a

theorem digit_sum_pow_le (n x : ℕ) (hn : 0 < n) (hx : 0 < x) :
    (Nat.digits 10 (n ^ x)).sum ≤ ((Nat.digits 10 n).sum) ^ x := by
  clear hn hx
  induction x with
  | zero => simp
  | succ x ih =>
    rw [pow_succ, pow_succ]
    exact (d_mul (n ^ x) n).trans (Nat.mul_le_mul_right _ ih)
```
