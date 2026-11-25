# Claude Opus 5.5 High (Claude AI)

Model: `Claude Opus 5.5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `105`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem digit_sum_pow_le (n x : ℕ) (hn : 0 < n) (hx : 0 < x) :
    (Nat.digits 10 (n ^ x)).sum ≤ ((Nat.digits 10 n).sum) ^ x := by
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → ℕ, S = fun m => (Nat.digits 10 m).sum := ⟨_, rfl⟩
  have hconv : ∀ m, (Nat.digits 10 m).sum = S m := by
    intro m; simp only [hSdef]
  have hS0 : S 0 = 0 := by simp [hSdef]
  have hS : ∀ m, S m = m % 10 + S (m / 10) := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp [hSdef]
    · simp only [hSdef]
      rw [Nat.digits_eq_cons_digits_div (by norm_num) h.ne', List.sum_cons]
  have hS1 : S 1 = 1 := by
    have := hS 1
    have e1 : (1 : ℕ) % 10 = 1 := by norm_num
    have e2 : (1 : ℕ) / 10 = 0 := by norm_num
    rw [e1, e2, hS0] at this
    omega
  have hadd : ∀ N, ∀ a b, a + b ≤ N → S (a + b) ≤ S a + S b := by
    intro N
    induction N with
    | zero =>
      intro a b h
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb
      simp [hS0]
    | succ N ih =>
      intro a b h
      by_cases hab : a + b = 0
      · have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha hb
        simp [hS0]
      have h1 := hS (a + b)
      have h2 := hS a
      have h3 := hS b
      by_cases hc : a % 10 + b % 10 < 10
      · have e1 : (a + b) / 10 = a / 10 + b / 10 := by omega
        have e2 : (a + b) % 10 = a % 10 + b % 10 := by omega
        rw [e1, e2] at h1
        have h4 := ih (a / 10) (b / 10) (by omega)
        omega
      · have e1 : (a + b) / 10 = a / 10 + b / 10 + 1 := by omega
        have e2 : (a + b) % 10 = a % 10 + b % 10 - 10 := by omega
        rw [e1, e2] at h1
        have h4 := ih (a / 10 + b / 10) 1 (by omega)
        have h5 := ih (a / 10) (b / 10) (by omega)
        rw [hS1] at h4
        omega
  have hadd' : ∀ a b, S (a + b) ≤ S a + S b := fun a b => hadd (a + b) a b le_rfl
  have h10 : ∀ m, S (10 * m) = S m := by
    intro m
    have := hS (10 * m)
    have e1 : 10 * m % 10 = 0 := by omega
    have e2 : 10 * m / 10 = m := by omega
    rw [e1, e2] at this
    omega
  have hmulk : ∀ k b, S (k * b) ≤ k * S b := by
    intro k b
    induction k with
    | zero => simp [hS0]
    | succ k ih =>
      have e : (k + 1) * b = k * b + b := by ring
      rw [e]
      have := hadd' (k * b) b
      nlinarith
  have hmul : ∀ N, ∀ a b, a ≤ N → S (a * b) ≤ S a * S b := by
    intro N
    induction N with
    | zero =>
      intro a b h
      have ha : a = 0 := by omega
      subst ha
      simp [hS0]
    | succ N ih =>
      intro a b h
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha; simp [hS0]
      have e : a * b = 10 * (a / 10 * b) + a % 10 * b := by
        have h := Nat.div_add_mod a 10
        calc a * b = (10 * (a / 10) + a % 10) * b := by rw [h]
          _ = 10 * (a / 10 * b) + a % 10 * b := by ring
      rw [e]
      have h1 := hadd' (10 * (a / 10 * b)) (a % 10 * b)
      have h2 := h10 (a / 10 * b)
      have h3 := hmulk (a % 10) b
      have h4 := ih (a / 10) b (by omega)
      have h5 := hS a
      rw [h5]
      nlinarith [h1, h2, h3, h4]
  have hmul' : ∀ a b, S (a * b) ≤ S a * S b := fun a b => hmul a a b le_rfl
  rw [hconv, hconv]
  revert hx
  induction x with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · rw [pow_succ, pow_succ]
      calc S (n ^ k * n) ≤ S (n ^ k) * S n := hmul' _ _
        _ ≤ S n ^ k * S n := Nat.mul_le_mul (ih hk) le_rfl
```
