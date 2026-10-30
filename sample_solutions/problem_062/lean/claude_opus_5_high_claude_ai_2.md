# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `3 September 2026`\
Line count: `48`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem no_pos_int_digit_prod_eq :
    ¬ ∃ n : ℕ, 0 < n ∧ ((Nat.digits 10 (n + 3)).prod : ℝ) /
      (((Nat.digits 10 (n + 5)).prod : ℝ) - 6) = (n : ℝ) ^ 2 := by
  have key : ∀ k m : ℕ, m ≤ k → 0 < m → (Nat.digits 10 m).prod ≤ m := by
    intro k
    induction k with
    | zero => intro m h1 h2; omega
    | succ k ih =>
      intro m h1 h2
      rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h2, List.prod_cons]
      by_cases h : m < 10
      · rw [(by omega : m / 10 = 0), Nat.digits_zero, List.prod_nil, mul_one]; omega
      · exact (Nat.mul_le_mul (by omega : m % 10 ≤ 9)
          (ih (m / 10) (by omega) (by omega))).trans (by omega)
  rintro ⟨n, hn, heq⟩
  obtain ⟨a, ha⟩ : ∃ a, (Nat.digits 10 (n + 3)).prod = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, (Nat.digits 10 (n + 5)).prod = b := ⟨_, rfl⟩
  rw [ha, hb] at heq
  have hA : (a : ℤ) ≤ (n : ℤ) + 3 := by
    have : a ≤ n + 3 := by rw [← ha]; exact key (n + 3) (n + 3) le_rfl (by omega)
    exact_mod_cast this
  have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  by_cases hb6 : b = 6
  · have h0 : ((b : ℝ) - 6) = 0 := by rw [hb6]; norm_num
    rw [h0, div_zero] at heq
    have : n = 0 := by exact_mod_cast sq_eq_zero_iff.mp heq.symm
    omega
  have hB : ((b : ℝ) - 6) ≠ 0 := by
    intro h; apply hb6
    have : (b : ℝ) = 6 := by linarith
    exact_mod_cast this
  have hZ : (a : ℤ) = (n : ℤ) ^ 2 * ((b : ℤ) - 6) := by
    have h := (div_eq_iff hB).mp heq
    have h' : ((a : ℤ) : ℝ) = (((n : ℤ) ^ 2 * ((b : ℤ) - 6) : ℤ) : ℝ) := by
      push_cast; linear_combination h
    exact Int.cast_injective h'
  have hb1 : (1 : ℤ) ≤ (b : ℤ) - 6 := by
    rcases (by omega : (b:ℤ) - 6 ≤ -1 ∨ (1:ℤ) ≤ (b:ℤ) - 6) with h | h
    · nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ((n:ℤ))), sq_nonneg ((n:ℤ) - 1)]
    · exact h
  have hn2 : n ≤ 2 := by
    by_contra hc
    have h3 : (3:ℤ) ≤ (n:ℤ) := by omega
    nlinarith [mul_le_mul_of_nonneg_left hb1 (sq_nonneg ((n:ℤ)))]
  interval_cases n <;> rw [← ha, ← hb] at hZ <;> norm_num at hZ
```
