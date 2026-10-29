# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `31 July 2026`\
Line count: `141`\
Turn count: `1`

## Solution

```lean4
import Mathlib

namespace DigitSumAux

/-- Sum of the base-10 digits. -/
def S (m : ℕ) : ℕ := (Nat.digits 10 m).sum

lemma S_zero : S 0 = 0 := by unfold S; simp

lemma S_eq (m : ℕ) (hm : 0 < m) : S m = m % 10 + S (m / 10) := by
  unfold S
  rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hm]
  simp

lemma S_one : S 1 = 1 := by
  rw [S_eq 1 (by norm_num)]
  simp [S_zero]

lemma S_le_self_aux : ∀ N m : ℕ, m ≤ N → S m ≤ m := by
  intro N
  induction N with
  | zero =>
    intro m hm
    obtain rfl : m = 0 := by omega
    simp [S_zero]
  | succ N ih =>
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp [S_zero]
    · have h1 := S_eq m hpos
      have h2 : S (m / 10) ≤ m / 10 := ih _ (by omega)
      omega

lemma S_le_self (m : ℕ) : S m ≤ m := S_le_self_aux m m le_rfl

lemma S_add_le_aux : ∀ N a b : ℕ, a + b ≤ N → S (a + b) ≤ S a + S b := by
  intro N
  induction N with
  | zero =>
    intro a b h
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    simp [S_zero]
  | succ N ih =>
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [S_zero]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [S_zero]
    have hpos : 0 < a + b := by omega
    have h1 : S (a + b) = (a + b) % 10 + S ((a + b) / 10) := S_eq _ hpos
    have h2 : S a = a % 10 + S (a / 10) := S_eq _ ha
    have h3 : S b = b % 10 + S (b / 10) := S_eq _ hb
    have hd : (a + b) / 10 = a / 10 + (b / 10 + (a % 10 + b % 10) / 10) := by omega
    have hs1 : S (a / 10 + (b / 10 + (a % 10 + b % 10) / 10))
        ≤ S (a / 10) + S (b / 10 + (a % 10 + b % 10) / 10) := ih _ _ (by omega)
    have hs2 : S (b / 10 + (a % 10 + b % 10) / 10)
        ≤ S (b / 10) + S ((a % 10 + b % 10) / 10) := ih _ _ (by omega)
    have hs3 : S ((a % 10 + b % 10) / 10) ≤ (a % 10 + b % 10) / 10 := S_le_self _
    rw [hd] at h1
    omega

lemma S_add_le (a b : ℕ) : S (a + b) ≤ S a + S b := S_add_le_aux (a + b) a b le_rfl

lemma S_mul_nat : ∀ d x : ℕ, S (d * x) ≤ d * S x := by
  intro d
  induction d with
  | zero => intro x; simp [S_zero]
  | succ d ih =>
    intro x
    have key : S ((d + 1) * x) ≤ (d + 1) * S x := by
      have h : (d + 1) * x = d * x + x := by ring
      rw [h]
      calc S (d * x + x) ≤ S (d * x) + S x := S_add_le _ _
        _ ≤ d * S x + S x := Nat.add_le_add (ih x) le_rfl
        _ = (d + 1) * S x := by ring
    exact key

lemma S_ten_mul (x : ℕ) : S (10 * x) = S x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have h : 0 < 10 * x := by omega
    rw [S_eq _ h]
    have h1 : 10 * x % 10 = 0 := by omega
    have h2 : 10 * x / 10 = x := by omega
    rw [h1, h2, zero_add]

lemma S_mul_ofDigits (x : ℕ) : ∀ L : List ℕ, S (x * Nat.ofDigits 10 L) ≤ S x * L.sum := by
  intro L
  induction L with
  | nil => simp [S_zero, Nat.ofDigits_nil]
  | cons d L ih =>
    have hof : x * Nat.ofDigits 10 (d :: L) = x * d + 10 * (x * Nat.ofDigits 10 L) := by
      simp only [Nat.ofDigits_cons, Nat.cast_id]
      ring
    rw [hof, List.sum_cons]
    calc S (x * d + 10 * (x * Nat.ofDigits 10 L))
        ≤ S (x * d) + S (10 * (x * Nat.ofDigits 10 L)) := S_add_le _ _
      _ = S (x * d) + S (x * Nat.ofDigits 10 L) := by rw [S_ten_mul]
      _ ≤ d * S x + S x * L.sum :=
          Nat.add_le_add (by rw [mul_comm x d]; exact S_mul_nat d x) ih
      _ = S x * (d + L.sum) := by ring

lemma S_mul_le (x y : ℕ) : S (x * y) ≤ S x * S y := by
  have h := S_mul_ofDigits x (Nat.digits 10 y)
  rw [Nat.ofDigits_digits] at h
  exact h

lemma S_pow_le (x : ℕ) : ∀ k : ℕ, S (x ^ k) ≤ (S x) ^ k := by
  intro k
  induction k with
  | zero => simp [S_one]
  | succ k ih =>
    have key : S (x ^ (k + 1)) ≤ (S x) ^ (k + 1) := by
      rw [pow_succ, pow_succ]
      calc S (x ^ k * x) ≤ S (x ^ k) * S x := S_mul_le _ _
        _ ≤ (S x) ^ k * S x := Nat.mul_le_mul ih le_rfl
    exact key

lemma S_sum_range_le (f : ℕ → ℕ) :
    ∀ k : ℕ, S (∑ i ∈ Finset.range k, f i) ≤ ∑ i ∈ Finset.range k, S (f i) := by
  intro k
  induction k with
  | zero => simp [S_zero]
  | succ k ih =>
    have key : S (∑ i ∈ Finset.range (k + 1), f i) ≤ ∑ i ∈ Finset.range (k + 1), S (f i) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact le_trans (S_add_le _ _) (Nat.add_le_add ih le_rfl)
    exact key

end DigitSumAux

open DigitSumAux in
theorem digit_sum_polynomial_le (P : Polynomial ℕ) (n : ℕ) (hn : 0 < n) :
    (Nat.digits 10 (P.eval n)).sum ≤ P.eval (Nat.digits 10 n).sum := by
  have key : S (P.eval n) ≤ P.eval (S n) := by
    rw [Polynomial.eval_eq_sum_range (p := P) n, Polynomial.eval_eq_sum_range (p := P) (S n)]
    refine le_trans (S_sum_range_le _ _) (Finset.sum_le_sum ?_)
    intro i _
    calc S (P.coeff i * n ^ i) ≤ P.coeff i * S (n ^ i) := S_mul_nat _ _
      _ ≤ P.coeff i * (S n) ^ i := Nat.mul_le_mul le_rfl (S_pow_le n i)
  exact key
```
