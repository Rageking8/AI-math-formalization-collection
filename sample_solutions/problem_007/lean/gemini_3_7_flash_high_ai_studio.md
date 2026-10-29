# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `26 August 2026`\
Line count: `100`\
Turn count: `1`

## Solution

```lean4
import Mathlib

lemma digit_sum_eq (n : ℕ) :
    (Nat.digits 10 n).sum = n % 10 + (Nat.digits 10 (n / 10)).sum := by
  rcases n with _|n
  · simp
  · rw [Nat.digits_of_two_le_of_pos (by decide) (Nat.succ_pos n)]
    simp

lemma digit_sum_add_le : ∀ (w u v c : ℕ), u + v + c = w → c ≤ 1 →
    (Nat.digits 10 (u + v + c)).sum ≤ (Nat.digits 10 u).sum + (Nat.digits 10 v).sum + c := by
  intro w
  induction' w using Nat.strong_induction_on with w ih
  intro u v c hw hc
  rcases w with _|w
  · have : u = 0 := by omega
    have : v = 0 := by omega
    have : c = 0 := by omega
    subst u v c
    simp
  · have hc' : (u % 10 + v % 10 + c) / 10 ≤ 1 := by omega
    have hdiv : u / 10 + v / 10 + (u % 10 + v % 10 + c) / 10 = (u + v + c) / 10 := by omega
    have hlt : (u + v + c) / 10 < w + 1 := by omega
    have ih' := ih ((u + v + c) / 10) hlt (u / 10) (v / 10) ((u % 10 + v % 10 + c) / 10) hdiv hc'
    rw [hdiv] at ih'
    rw [digit_sum_eq (u + v + c), digit_sum_eq u, digit_sum_eq v]
    omega

lemma digit_sum_add_le_two (u v : ℕ) :
    (Nat.digits 10 (u + v)).sum ≤ (Nat.digits 10 u).sum + (Nat.digits 10 v).sum := by
  have h := digit_sum_add_le (u + v) u v 0 rfl (by omega)
  omega

lemma digit_sum_mul_ten (n : ℕ) :
    (Nat.digits 10 (10 * n)).sum = (Nat.digits 10 n).sum := by
  rcases n with _|n
  · simp
  · rw [digit_sum_eq (10 * (n + 1))]
    have hmod : (10 * (n + 1)) % 10 = 0 := by omega
    have hdiv : (10 * (n + 1)) / 10 = n + 1 := by omega
    rw [hmod, hdiv]
    omega

lemma digit_sum_smul_le (k n : ℕ) :
    (Nat.digits 10 (k * n)).sum ≤ k * (Nat.digits 10 n).sum := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h1 : (k + 1) * n = k * n + n := by ring
    rw [h1]
    calc (Nat.digits 10 (k * n + n)).sum
      _ ≤ (Nat.digits 10 (k * n)).sum + (Nat.digits 10 n).sum := digit_sum_add_le_two (k * n) n
      _ ≤ k * (Nat.digits 10 n).sum + (Nat.digits 10 n).sum := Nat.add_le_add_right ih _
      _ = (k + 1) * (Nat.digits 10 n).sum := by ring

lemma digit_sum_mul_le (a b : ℕ) :
    (Nat.digits 10 (a * b)).sum ≤ (Nat.digits 10 a).sum * (Nat.digits 10 b).sum := by
  induction' a using Nat.strong_induction_on with a ih
  rcases a with _|a
  · simp
  · have hdiv : a + 1 = (a + 1) % 10 + 10 * ((a + 1) / 10) := by omega
    have hab : (a + 1) * b = ((a + 1) % 10) * b + 10 * (((a + 1) / 10) * b) := by
      nth_rw 1 [hdiv]
      ring
    have h1 : (Nat.digits 10 ((a + 1) * b)).sum ≤
        (Nat.digits 10 (((a + 1) % 10) * b)).sum + (Nat.digits 10 (10 * (((a + 1) / 10) * b))).sum := by
      rw [hab]
      exact digit_sum_add_le_two _ _
    have h2 : (Nat.digits 10 (10 * (((a + 1) / 10) * b))).sum = (Nat.digits 10 (((a + 1) / 10) * b)).sum :=
      digit_sum_mul_ten _
    have h3 : (Nat.digits 10 (((a + 1) % 10) * b)).sum ≤ ((a + 1) % 10) * (Nat.digits 10 b).sum :=
      digit_sum_smul_le _ _
    have hlt : (a + 1) / 10 < a + 1 := by omega
    have h4 : (Nat.digits 10 (((a + 1) / 10) * b)).sum ≤ (Nat.digits 10 ((a + 1) / 10)).sum * (Nat.digits 10 b).sum :=
      ih ((a + 1) / 10) hlt
    have h5 : (Nat.digits 10 (a + 1)).sum = (a + 1) % 10 + (Nat.digits 10 ((a + 1) / 10)).sum :=
      digit_sum_eq (a + 1)
    calc (Nat.digits 10 ((a + 1) * b)).sum
      _ ≤ (Nat.digits 10 (((a + 1) % 10) * b)).sum + (Nat.digits 10 (10 * (((a + 1) / 10) * b))).sum := h1
      _ = (Nat.digits 10 (((a + 1) % 10) * b)).sum + (Nat.digits 10 (((a + 1) / 10) * b)).sum := by rw [h2]
      _ ≤ ((a + 1) % 10) * (Nat.digits 10 b).sum + (Nat.digits 10 ((a + 1) / 10)).sum * (Nat.digits 10 b).sum :=
        Nat.add_le_add h3 h4
      _ = ((a + 1) % 10 + (Nat.digits 10 ((a + 1) / 10)).sum) * (Nat.digits 10 b).sum := by ring
      _ = (Nat.digits 10 (a + 1)).sum * (Nat.digits 10 b).sum := by rw [← h5]

theorem digit_sum_pow_le (n x : ℕ) (hn : 0 < n) (hx : 0 < x) :
    (Nat.digits 10 (n ^ x)).sum ≤ ((Nat.digits 10 n).sum) ^ x := by
  rcases x with _|x
  · omega
  clear hx
  induction x with
  | zero =>
    rw [pow_one, pow_one]
  | succ x ih =>
    rw [Nat.pow_succ n (x + 1), Nat.pow_succ ((Nat.digits 10 n).sum) (x + 1)]
    calc (Nat.digits 10 (n ^ (x + 1) * n)).sum
      _ ≤ (Nat.digits 10 (n ^ (x + 1))).sum * (Nat.digits 10 n).sum := digit_sum_mul_le _ _
      _ ≤ ((Nat.digits 10 n).sum) ^ (x + 1) * (Nat.digits 10 n).sum :=
        Nat.mul_le_mul_right _ ih
```
