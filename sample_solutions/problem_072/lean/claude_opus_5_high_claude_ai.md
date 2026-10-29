# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `21 August 2026`\
Line count: `47`\
Turn count: `2`

## Solution

```lean4
import Mathlib

def R (n d : ℕ) : ℕ := d * ((10 ^ n - 1) / 9)

theorem repdigit_unique_sol_n_one (n : ℕ) (hn : 0 < n) :
    R n 3 ^ 2 - R n 2 = R n 7 ↔ n = 1 := by
  have gen : ∀ m : ℕ, ∃ k, (10:ℕ) ^ m = 9 * k + 1 := by
    intro m
    induction m with
    | zero => exact ⟨0, by norm_num⟩
    | succ p ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨10 * k + 1, by rw [pow_succ, hk]; ring⟩
  obtain ⟨k, hk⟩ := gen n
  have h10 : (10:ℕ) ≤ 10 ^ n := by
    calc (10:ℕ) = 10 ^ 1 := (pow_one 10).symm
      _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h10' : (10:ℕ) ≤ 9 * k + 1 := by rw [← hk]; exact h10
  have hk1 : 1 ≤ k := by omega
  have hr : (10 ^ n - 1) / 9 = k := by rw [hk]; omega
  have hstep : R n 3 ^ 2 - R n 2 = R n 7 ↔ k = 1 := by
    simp only [R, hr]
    constructor
    · intro h
      have h3 : (3 * k) ^ 2 = 9 * (k * k) := by ring
      rw [h3] at h
      have hkk : k ≤ k * k := by
        calc k = k * 1 := (mul_one k).symm
          _ ≤ k * k := Nat.mul_le_mul (le_refl k) hk1
      obtain ⟨K, hK⟩ : ∃ K, k * k = K := ⟨_, rfl⟩
      rw [hK] at h hkk
      have hkk2 : k * k = k := by rw [hK]; omega
      have hmul : k * k = k * 1 := by rw [mul_one]; exact hkk2
      exact Nat.eq_of_mul_eq_mul_left hk1 hmul
    · intro h
      subst h
      norm_num
  rw [hstep]
  constructor
  · intro h
    subst h
    have h9 : (10:ℕ) ^ n = 10 ^ 1 := by rw [hk]; norm_num
    exact Nat.pow_right_injective (by norm_num) h9
  · intro h
    subst h
    rw [pow_one] at hk
    omega
```
