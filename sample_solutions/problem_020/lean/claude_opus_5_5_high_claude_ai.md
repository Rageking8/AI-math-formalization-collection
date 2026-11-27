# Claude Opus 5.5 High (Claude AI)

Model: `Claude Opus 5.5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `107`\
Turn count: `1`

## Solution

```lean4
import Mathlib

lemma dsP_eq (n : ℕ) :
    (Nat.digits 10 n).sum = n % 10 + (Nat.digits 10 (n / 10)).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · rw [Nat.digits_def' (by norm_num : 1 < 10) h, List.sum_cons]

lemma dsP_one : (Nat.digits 10 1).sum = 1 := by
  rw [dsP_eq 1] <;> norm_num

lemma dsP_add_aux (N : ℕ) : ∀ a b : ℕ, a + b ≤ N →
    (Nat.digits 10 (a + b)).sum ≤ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum := by
  induction N with
  | zero =>
    intro a b h
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha
    subst hb
    simp
  | succ N ih =>
    intro a b h
    have E := dsP_eq (a + b)
    have Ea := dsP_eq a
    have Eb := dsP_eq b
    by_cases hc : a % 10 + b % 10 < 10
    · have h2 : (a + b) / 10 = a / 10 + b / 10 := by omega
      rw [h2] at E
      have k := ih (a / 10) (b / 10) (by omega)
      omega
    · have h2 : (a + b) / 10 = a / 10 + b / 10 + 1 := by omega
      rw [h2] at E
      have k1 := ih (a / 10 + b / 10) 1 (by omega)
      have k2 := ih (a / 10) (b / 10) (by omega)
      have k3 := dsP_one
      omega

lemma dsP_add (a b : ℕ) :
    (Nat.digits 10 (a + b)).sum ≤ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum :=
  dsP_add_aux (a + b) a b le_rfl

lemma dsP_nsmul (c m : ℕ) :
    (Nat.digits 10 (c * m)).sum ≤ c * (Nat.digits 10 m).sum := by
  induction c with
  | zero => simp
  | succ c ih =>
    calc (Nat.digits 10 ((c + 1) * m)).sum = (Nat.digits 10 (c * m + m)).sum := by
          rw [add_one_mul]
      _ ≤ (Nat.digits 10 (c * m)).sum + (Nat.digits 10 m).sum := dsP_add _ _
      _ ≤ c * (Nat.digits 10 m).sum + (Nat.digits 10 m).sum := Nat.add_le_add ih le_rfl
      _ = (c + 1) * (Nat.digits 10 m).sum := by ring

lemma dsP_ten (x : ℕ) : (Nat.digits 10 (10 * x)).sum = (Nat.digits 10 x).sum := by
  have e2 : 10 * x / 10 = x := by omega
  rw [dsP_eq (10 * x), e2]
  omega

lemma dsP_mul_aux (N : ℕ) : ∀ a b : ℕ, b ≤ N →
    (Nat.digits 10 (a * b)).sum ≤ (Nat.digits 10 a).sum * (Nat.digits 10 b).sum := by
  induction N with
  | zero =>
    intro a b h
    have hb : b = 0 := by omega
    subst hb
    simp
  | succ N ih =>
    intro a b h
    have Eb := dsP_eq b
    have hb : b = 10 * (b / 10) + b % 10 := (Nat.div_add_mod b 10).symm
    have hsplit : a * b = 10 * (a * (b / 10)) + (b % 10) * a := by
      calc a * b = a * (10 * (b / 10) + b % 10) := by rw [← hb]
        _ = 10 * (a * (b / 10)) + (b % 10) * a := by ring
    have k2 := ih a (b / 10) (by omega)
    have k3 := dsP_nsmul (b % 10) a
    rw [hsplit]
    calc (Nat.digits 10 (10 * (a * (b / 10)) + (b % 10) * a)).sum
        ≤ (Nat.digits 10 (10 * (a * (b / 10)))).sum
            + (Nat.digits 10 ((b % 10) * a)).sum := dsP_add _ _
      _ = (Nat.digits 10 (a * (b / 10))).sum
            + (Nat.digits 10 ((b % 10) * a)).sum := by rw [dsP_ten]
      _ ≤ (Nat.digits 10 a).sum * (Nat.digits 10 (b / 10)).sum
            + (b % 10) * (Nat.digits 10 a).sum := Nat.add_le_add k2 k3
      _ = (Nat.digits 10 a).sum * (b % 10 + (Nat.digits 10 (b / 10)).sum) := by ring
      _ = (Nat.digits 10 a).sum * (Nat.digits 10 b).sum := by rw [← Eb]

lemma dsP_mul (a b : ℕ) :
    (Nat.digits 10 (a * b)).sum ≤ (Nat.digits 10 a).sum * (Nat.digits 10 b).sum :=
  dsP_mul_aux b a b le_rfl

lemma dsP_pow (n k : ℕ) :
    (Nat.digits 10 (n ^ k)).sum ≤ (Nat.digits 10 n).sum ^ k := by
  induction k with
  | zero => simp [dsP_one]
  | succ k ih =>
    simp only [pow_succ]
    exact le_trans (dsP_mul _ _) (Nat.mul_le_mul ih le_rfl)

theorem digit_sum_polynomial_le (P : Polynomial ℕ) (n : ℕ) (hn : 0 < n) :
    (Nat.digits 10 (P.eval n)).sum ≤ P.eval (Nat.digits 10 n).sum := by
  refine Polynomial.induction_on' P ?_ ?_
  · intro p q hp hq
    simp only [Polynomial.eval_add]
    exact le_trans (dsP_add _ _) (Nat.add_le_add hp hq)
  · intro k c
    simp only [Polynomial.eval_monomial]
    exact le_trans (dsP_nsmul c (n ^ k)) (Nat.mul_le_mul le_rfl (dsP_pow n k))
```
