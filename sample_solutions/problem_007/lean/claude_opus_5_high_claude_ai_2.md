# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `11 August 2026`\
Line count: `74`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem digit_sum_pow_le (n x : ℕ) (hn : 0 < n) (hx : 0 < x) :
    (Nat.digits 10 (n ^ x)).sum ≤ ((Nat.digits 10 n).sum) ^ x := by
  clear hx hn
  -- the digit-sum recursion
  have K : ∀ m : ℕ, (Nat.digits 10 m).sum = m % 10 + (Nat.digits 10 (m / 10)).sum := fun m => by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h]; simp
  have D : ∀ d : ℕ, d < 10 → (Nat.digits 10 d).sum = d := fun d hd => by
    rw [K d, Nat.mod_eq_of_lt hd, Nat.div_eq_of_lt hd]; simp
  -- subadditivity, by strong induction via a bound
  have A : ∀ m a b : ℕ, a + b ≤ m →
      (Nat.digits 10 (a + b)).sum ≤ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum := by
    intro m
    induction m with
    | zero =>
      intro a b h
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
      simp
    | succ k ih =>
      intro a b h
      have h1 : (a + b) / 10 = a / 10 + b / 10 + (a % 10 + b % 10) / 10 := by omega
      have h2 : (a + b) / 10 ≤ k := by omega
      have t1 := ih (a / 10 + b / 10) ((a % 10 + b % 10) / 10) (by omega)
      have t2 := ih (a / 10) (b / 10) (by omega)
      rw [D _ (by omega : (a % 10 + b % 10) / 10 < 10)] at t1
      rw [K (a + b), h1, K a, K b]
      omega
  have M : ∀ m : ℕ, (Nat.digits 10 (10 * m)).sum = (Nat.digits 10 m).sum := fun m => by
    rw [K (10 * m), (show (10 * m) % 10 = 0 by omega), (show (10 * m) / 10 = m by omega), zero_add]
  have G : ∀ d b : ℕ, (Nat.digits 10 (d * b)).sum ≤ d * (Nat.digits 10 b).sum := by
    intro d
    induction d with
    | zero => simp
    | succ e ihe =>
      intro b
      calc (Nat.digits 10 ((e + 1) * b)).sum
          = (Nat.digits 10 (e * b + b)).sum := by rw [add_mul, one_mul]
        _ ≤ (Nat.digits 10 (e * b)).sum + (Nat.digits 10 b).sum := A _ _ _ le_rfl
        _ ≤ e * (Nat.digits 10 b).sum + (Nat.digits 10 b).sum := Nat.add_le_add_right (ihe b) _
        _ = (e + 1) * (Nat.digits 10 b).sum := by ring
  -- sub-multiplicativity
  have MU : ∀ m a b : ℕ, a ≤ m →
      (Nat.digits 10 (a * b)).sum ≤ (Nat.digits 10 a).sum * (Nat.digits 10 b).sum := by
    intro m
    induction m with
    | zero =>
      intro a b ha
      obtain rfl : a = 0 := by omega
      simp
    | succ k ih =>
      intro a b ha
      rcases Nat.eq_zero_or_pos a with rfl | h
      · simp
      · calc (Nat.digits 10 (a * b)).sum
            = (Nat.digits 10 (10 * (a / 10 * b) + a % 10 * b)).sum := by
              rw [← mul_assoc, ← add_mul, Nat.div_add_mod]
          _ ≤ (Nat.digits 10 (10 * (a / 10 * b))).sum + (Nat.digits 10 (a % 10 * b)).sum :=
              A _ _ _ le_rfl
          _ = (Nat.digits 10 (a / 10 * b)).sum + (Nat.digits 10 (a % 10 * b)).sum := by rw [M]
          _ ≤ (Nat.digits 10 (a / 10)).sum * (Nat.digits 10 b).sum
                + a % 10 * (Nat.digits 10 b).sum := Nat.add_le_add (ih _ _ (by omega)) (G _ _)
          _ = ((Nat.digits 10 (a / 10)).sum + a % 10) * (Nat.digits 10 b).sum := by ring
          _ = (Nat.digits 10 a).sum * (Nat.digits 10 b).sum := by rw [K a]; ring
  induction x with
  | zero => simp [D 1 (by norm_num)]
  | succ j ihj =>
    calc (Nat.digits 10 (n ^ (j + 1))).sum
        = (Nat.digits 10 (n ^ j * n)).sum := by rw [pow_succ]
      _ ≤ (Nat.digits 10 (n ^ j)).sum * (Nat.digits 10 n).sum := MU _ _ _ le_rfl
      _ ≤ (Nat.digits 10 n).sum ^ j * (Nat.digits 10 n).sum := Nat.mul_le_mul ihj le_rfl
      _ = (Nat.digits 10 n).sum ^ (j + 1) := (pow_succ _ _).symm
```
