# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `22 August 2026`\
Line count: `48`\
Turn count: `3`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

def a : ℕ → ℤ
  | 0 => 2
  | 1 => 5
  | n + 2 => 5 * a (n + 1) - 2 * a n

lemma a_odd : ∀ n, Odd (a (n + 1))
  | 0 => ⟨2, rfl⟩
  | n + 1 => let ⟨k, _⟩ := a_odd n; ⟨5 * k + 2 - a n, by dsimp [a]; omega⟩

lemma a_eq (n : ℕ) :
    (a n : ℝ) = (((5 : ℝ) + Real.sqrt 17) / 2) ^ n + (((5 : ℝ) - Real.sqrt 17) / 2) ^ n := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hu : (((5 : ℝ) + Real.sqrt 17) / 2) ^ 2 = 5 * (((5 : ℝ) + Real.sqrt 17) / 2) - 2 := by
    linear_combination (1 / 4) * hs
  have hv : (((5 : ℝ) - Real.sqrt 17) / 2) ^ 2 = 5 * (((5 : ℝ) - Real.sqrt 17) / 2) - 2 := by
    linear_combination (1 / 4) * hs
  induction n using Nat.twoStepInduction with
  | zero => dsimp [a]; norm_num
  | one => dsimp [a]; ring
  | more k h1 h2 =>
    dsimp [a]; push_cast; rw [h1, h2]
    simp only [pow_add, hu, hv, pow_one]; ring

theorem ceil_pow_expr_odd (x : ℕ) :
    Odd ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ x⌉ := by
  rcases x with _ | n
  · norm_num
  have : (3 : ℝ) < Real.sqrt 17 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have : Real.sqrt 17 < (5 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hv_pos : 0 < ((5 : ℝ) - Real.sqrt 17) / 2 := by linarith
  have hv_lt : ∀ m : ℕ, (((5 : ℝ) - Real.sqrt 17) / 2) ^ (m + 1) < 1 := by
    intro m
    induction m with
    | zero => simp; linarith
    | succ m ih =>
      rw [pow_succ]
      have := pow_pos hv_pos (m + 1)
      nlinarith
  have hc : ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ (n + 1)⌉ = a (n + 1) := by
    rw [Int.ceil_eq_iff]
    have := a_eq (n + 1)
    have := pow_pos hv_pos (n + 1)
    have := hv_lt n
    constructor <;> linarith
  rw [hc]
  exact a_odd n
```
