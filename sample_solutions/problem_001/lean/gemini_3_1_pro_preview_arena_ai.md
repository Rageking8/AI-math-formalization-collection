# Gemini 3.1 Pro Preview (Arena AI)

Model: `gemini-3.1-pro-preview` (via Arena AI)\
Date: `18 July 2026`\
Line count: `147`\
Turn count: `1`

## Solution

```lean4
import Mathlib

-- Define the integer sequence S_n = α^n + β^n
def S : ℕ → ℤ
  | 0 => 2
  | 1 => 5
  | (n + 2) => 5 * S (n + 1) - 2 * S n

lemma S_add_two (n : ℕ) : S (n + 2) = 5 * S (n + 1) - 2 * S n := rfl

-- Algebraic identities for the roots
lemma root_eq1 : (((5 : ℝ) + Real.sqrt 17) / 2) ^ 2 = 5 * (((5 : ℝ) + Real.sqrt 17) / 2) - 2 := by
  have h : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  calc (((5 : ℝ) + Real.sqrt 17) / 2) ^ 2
    _ = (25 + (Real.sqrt 17)^2 + 10 * Real.sqrt 17) / 4 := by ring
    _ = (25 + 17 + 10 * Real.sqrt 17) / 4 := by rw [h]
    _ = 5 * (((5 : ℝ) + Real.sqrt 17) / 2) - 2 := by ring

lemma root_eq2 : (((5 : ℝ) - Real.sqrt 17) / 2) ^ 2 = 5 * (((5 : ℝ) - Real.sqrt 17) / 2) - 2 := by
  have h : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  calc (((5 : ℝ) - Real.sqrt 17) / 2) ^ 2
    _ = (25 + (Real.sqrt 17)^2 - 10 * Real.sqrt 17) / 4 := by ring
    _ = (25 + 17 - 10 * Real.sqrt 17) / 4 := by rw [h]
    _ = 5 * (((5 : ℝ) - Real.sqrt 17) / 2) - 2 := by ring

lemma pow_add_two (α : ℝ) (h : α^2 = 5*α - 2) (n : ℕ) : α^(n+2) = 5*α^(n+1) - 2*α^n := by
  have h1 : α^(n+2) = α^n * α^2 := by rw [pow_add]
  have h2 : α^(n+1) = α^n * α^1 := by rw [pow_add]
  have h3 : α^1 = α := pow_one α
  rw [h3] at h2
  rw [h1, h2, h]
  ring

-- Relate sequence S to real exponents
lemma S_eq_both (n : ℕ) :
  (S n : ℝ) = (((5 : ℝ) + Real.sqrt 17) / 2) ^ n + (((5 : ℝ) - Real.sqrt 17) / 2) ^ n ∧
  (S (n + 1) : ℝ) = (((5 : ℝ) + Real.sqrt 17) / 2) ^ (n + 1) + (((5 : ℝ) - Real.sqrt 17) / 2) ^ (n + 1) := by
  induction' n with n ih
  · constructor
    · change (2 : ℝ) = (((5 : ℝ) + Real.sqrt 17) / 2) ^ 0 + (((5 : ℝ) - Real.sqrt 17) / 2) ^ 0
      rw [pow_zero, pow_zero]
      ring
    · change (5 : ℝ) = (((5 : ℝ) + Real.sqrt 17) / 2) ^ 1 + (((5 : ℝ) - Real.sqrt 17) / 2) ^ 1
      rw [pow_one, pow_one]
      ring
  · rcases ih with ⟨ih1, ih2⟩
    constructor
    · exact ih2
    · rw [S_add_two]
      push_cast
      rw [ih1, ih2]
      have h1 := pow_add_two (((5 : ℝ) + Real.sqrt 17) / 2) root_eq1 n
      have h2 := pow_add_two (((5 : ℝ) - Real.sqrt 17) / 2) root_eq2 n
      linarith

-- Proofs bounding the conjugate root base β = (5 - sqrt 17) / 2 in (0, 1)
lemma beta_pos : 0 < ((5 : ℝ) - Real.sqrt 17) / 2 := by
  have h_sq : (25 : ℝ) = 5 ^ 2 := by norm_num
  have h_sqrt : Real.sqrt 25 = 5 := by
    rw [h_sq]
    exact Real.sqrt_sq (by norm_num)
  have h2 : Real.sqrt 17 < Real.sqrt 25 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma beta_lt_one : ((5 : ℝ) - Real.sqrt 17) / 2 < 1 := by
  have h_sq : (9 : ℝ) = 3 ^ 2 := by norm_num
  have h_sqrt : Real.sqrt 9 = 3 := by
    rw [h_sq]
    exact Real.sqrt_sq (by norm_num)
  have h2 : Real.sqrt 9 < Real.sqrt 17 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma beta_pow_pos (n : ℕ) : 0 < (((5 : ℝ) - Real.sqrt 17) / 2) ^ n := by
  apply pow_pos beta_pos

lemma beta_pow_lt_one (n : ℕ) (hn : n ≠ 0) : (((5 : ℝ) - Real.sqrt 17) / 2) ^ n < 1 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [hk]
  clear hn hk n
  induction' k with k ih
  · rw [pow_one]
    exact beta_lt_one
  · rw [pow_succ]
    have h1 := beta_pos
    have h2 := beta_lt_one
    have h3 : (((5 : ℝ) - Real.sqrt 17) / 2) ^ (k + 1) < 1 := ih
    calc (((5 : ℝ) - Real.sqrt 17) / 2) ^ (k + 1) * (((5 : ℝ) - Real.sqrt 17) / 2)
      _ < 1 * (((5 : ℝ) - Real.sqrt 17) / 2) := mul_lt_mul_of_pos_right ih h1
      _ = (((5 : ℝ) - Real.sqrt 17) / 2) := by ring
      _ < 1 := h2

-- Establishing the behavior linking Real powers up to integer Ceil
lemma ceil_unique (a : ℝ) (z : ℤ) (h1 : (z : ℝ) - 1 < a) (h2 : a ≤ (z : ℝ)) : ⌈a⌉ = z := by
  apply le_antisymm
  · exact Int.ceil_le.mpr h2
  · have h3 : a ≤ (⌈a⌉ : ℝ) := Int.le_ceil a
    have h4 : (↑(z - 1) : ℝ) < ↑⌈a⌉ := by
      push_cast
      linarith
    have h5 : z - 1 < ⌈a⌉ := Int.cast_lt.mp h4
    linarith

lemma ceil_alpha_pow (n : ℕ) (hn : n ≠ 0) : ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ n⌉ = S n := by
  apply ceil_unique
  · have eq : (((5 : ℝ) + Real.sqrt 17) / 2) ^ n = (S n : ℝ) - (((5 : ℝ) - Real.sqrt 17) / 2) ^ n := by
      have h := (S_eq_both n).1
      linarith
    rw [eq]
    have := beta_pow_lt_one n hn
    push_cast
    linarith
  · have eq : (((5 : ℝ) + Real.sqrt 17) / 2) ^ n = (S n : ℝ) - (((5 : ℝ) - Real.sqrt 17) / 2) ^ n := by
      have h := (S_eq_both n).1
      linarith
    rw [eq]
    have := beta_pow_pos n
    push_cast
    linarith

-- Parity Proof
lemma S_odd_succ (n : ℕ) : Odd (S (n + 1)) := by
  induction' n with n ih
  · use 2
    rfl
  · rw [S_add_two]
    rcases ih with ⟨k, hk⟩
    use 5 * k + 2 - S n
    calc 5 * S (n + 1) - 2 * S n
      _ = 5 * (2 * k + 1) - 2 * S n := by rw [hk]
      _ = 2 * (5 * k + 2 - S n) + 1 := by ring

-- Main Theorem Statement
theorem ceil_pow_expr_odd (x : ℕ) :
    Odd ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ x⌉ := by
  rcases x with _ | x
  · rw [pow_zero]
    have h : ⌈(1 : ℝ)⌉ = 1 := by
      apply ceil_unique
      · norm_num
      · norm_num
    rw [h]
    use 0
    ring
  · have hx : x + 1 ≠ 0 := by simp
    have eq := ceil_alpha_pow (x + 1) hx
    rw [eq]
    exact S_odd_succ x
```
