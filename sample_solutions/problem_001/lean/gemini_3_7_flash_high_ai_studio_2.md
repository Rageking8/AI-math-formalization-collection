# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `22 August 2026`\
Line count: `137`\
Turn count: `1`

## Solution

```lean4
import Mathlib

/-- The integer sequence `S n = α^n + β^n`. -/
def S : ℕ → ℤ
  | 0 => 2
  | 1 => 5
  | n + 2 => 5 * S (n + 1) - 2 * S n

lemma S_odd : ∀ n : ℕ, Odd (S (n + 1))
  | 0 => ⟨2, rfl⟩
  | 1 => ⟨10, rfl⟩
  | n + 2 => by
    have ih := S_odd (n + 1)
    rcases ih with ⟨k, hk⟩
    use 5 * k + 2 - S (n + 1)
    have hrec : S (n + 3) = 5 * S (n + 2) - 2 * S (n + 1) := rfl
    linarith [hrec, hk]

lemma alpha_sq : (((5 : ℝ) + Real.sqrt 17) / 2) ^ 2 = 5 * (((5 : ℝ) + Real.sqrt 17) / 2) - 2 := by
  have h17 : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h_eq : (((5 : ℝ) + Real.sqrt 17) / 2) ^ 2 - (5 * (((5 : ℝ) + Real.sqrt 17) / 2) - 2) =
      ((Real.sqrt 17) ^ 2 - 17) / 4 := by ring
  linarith [h_eq, h17]

lemma beta_sq : (((5 : ℝ) - Real.sqrt 17) / 2) ^ 2 = 5 * (((5 : ℝ) - Real.sqrt 17) / 2) - 2 := by
  have h17 : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h_eq : (((5 : ℝ) - Real.sqrt 17) / 2) ^ 2 - (5 * (((5 : ℝ) - Real.sqrt 17) / 2) - 2) =
      ((Real.sqrt 17) ^ 2 - 17) / 4 := by ring
  linarith [h_eq, h17]

lemma alpha_rec (n : ℕ) : (((5 : ℝ) + Real.sqrt 17) / 2) ^ (n + 2) =
    5 * (((5 : ℝ) + Real.sqrt 17) / 2) ^ (n + 1) - 2 * (((5 : ℝ) + Real.sqrt 17) / 2) ^ n := by
  have h1 : (((5 : ℝ) + Real.sqrt 17) / 2) ^ (n + 2) =
      (((5 : ℝ) + Real.sqrt 17) / 2) ^ n * (((5 : ℝ) + Real.sqrt 17) / 2) ^ 2 := by rw [pow_add]
  have h2 : (((5 : ℝ) + Real.sqrt 17) / 2) ^ (n + 1) =
      (((5 : ℝ) + Real.sqrt 17) / 2) ^ n * (((5 : ℝ) + Real.sqrt 17) / 2) := by rw [pow_add, pow_one]
  have hsq := alpha_sq
  rw [h1, h2, hsq]
  ring

lemma beta_rec (n : ℕ) : (((5 : ℝ) - Real.sqrt 17) / 2) ^ (n + 2) =
    5 * (((5 : ℝ) - Real.sqrt 17) / 2) ^ (n + 1) - 2 * (((5 : ℝ) - Real.sqrt 17) / 2) ^ n := by
  have h1 : (((5 : ℝ) - Real.sqrt 17) / 2) ^ (n + 2) =
      (((5 : ℝ) - Real.sqrt 17) / 2) ^ n * (((5 : ℝ) - Real.sqrt 17) / 2) ^ 2 := by rw [pow_add]
  have h2 : (((5 : ℝ) - Real.sqrt 17) / 2) ^ (n + 1) =
      (((5 : ℝ) - Real.sqrt 17) / 2) ^ n * (((5 : ℝ) - Real.sqrt 17) / 2) := by rw [pow_add, pow_one]
  have hsq := beta_sq
  rw [h1, h2, hsq]
  ring

lemma S_eq_pow : ∀ (n : ℕ), (((5 : ℝ) + Real.sqrt 17) / 2) ^ n + (((5 : ℝ) - Real.sqrt 17) / 2) ^ n = (S n : ℝ)
  | 0 => by
    have : (((5 : ℝ) + Real.sqrt 17) / 2) ^ 0 + (((5 : ℝ) - Real.sqrt 17) / 2) ^ 0 = 2 := by
      rw [pow_zero, pow_zero]
      ring
    have hS0 : (S 0 : ℝ) = 2 := rfl
    rw [this, hS0]
  | 1 => by
    have : (((5 : ℝ) + Real.sqrt 17) / 2) ^ 1 + (((5 : ℝ) - Real.sqrt 17) / 2) ^ 1 = 5 := by
      rw [pow_one, pow_one]
      ring
    have hS1 : (S 1 : ℝ) = 5 := rfl
    rw [this, hS1]
  | n + 2 => by
    have ih1 := S_eq_pow n
    have ih2 := S_eq_pow (n + 1)
    have hrecA := alpha_rec n
    have hrecB := beta_rec n
    have hSrec : (S (n + 2) : ℝ) = 5 * (S (n + 1) : ℝ) - 2 * (S n : ℝ) := by
      change ((5 * S (n + 1) - 2 * S n : ℤ) : ℝ) = 5 * (S (n + 1) : ℝ) - 2 * (S n : ℝ)
      push_cast
      ring
    linarith [ih1, ih2, hrecA, hrecB, hSrec]

lemma beta_pos : 0 < ((5 : ℝ) - Real.sqrt 17) / 2 := by
  have h25 : Real.sqrt 25 = 5 := by
    have : (25 : ℝ) = 5 ^ 2 := by norm_num
    rw [this, Real.sqrt_sq (by norm_num)]
  have h_lt5 : Real.sqrt 17 < 5 := by
    rw [← h25]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma beta_lt_one : ((5 : ℝ) - Real.sqrt 17) / 2 < 1 := by
  have h16 : Real.sqrt 16 = 4 := by
    have : (16 : ℝ) = 4 ^ 2 := by norm_num
    rw [this, Real.sqrt_sq (by norm_num)]
  have h_gt4 : 4 < Real.sqrt 17 := by
    rw [← h16]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma beta_pow_pos (m : ℕ) : 0 < (((5 : ℝ) - Real.sqrt 17) / 2) ^ m := by
  induction m with
  | zero =>
    norm_num
  | succ m ih =>
    have hstep : (((5 : ℝ) - Real.sqrt 17) / 2) ^ (m + 1) =
        (((5 : ℝ) - Real.sqrt 17) / 2) ^ m * (((5 : ℝ) - Real.sqrt 17) / 2) := by
      rw [pow_add, pow_one]
    rw [hstep]
    have hb := beta_pos
    nlinarith

lemma beta_pow_lt_one (n : ℕ) : (((5 : ℝ) - Real.sqrt 17) / 2) ^ (n + 1) < 1 := by
  induction n with
  | zero =>
    rw [pow_one]
    exact beta_lt_one
  | succ n ih =>
    have hstep : (((5 : ℝ) - Real.sqrt 17) / 2) ^ (n + 1 + 1) =
        (((5 : ℝ) - Real.sqrt 17) / 2) ^ (n + 1) * (((5 : ℝ) - Real.sqrt 17) / 2) := by
      rw [pow_add, pow_one]
    rw [hstep]
    have hb_pos := beta_pos
    have hb_lt := beta_lt_one
    have hpow_pos := beta_pow_pos (n + 1)
    nlinarith

theorem ceil_pow_expr_odd (x : ℕ) :
    Odd ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ x⌉ := by
  rcases x with _ | n
  · have h0 : ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ 0⌉ = 1 := by
      rw [pow_zero, Int.ceil_eq_iff]
      norm_num
    rw [h0]
    exact ⟨0, rfl⟩
  · have h_ceil : ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ (n + 1)⌉ = S (n + 1) := by
      rw [Int.ceil_eq_iff]
      have h_sum := S_eq_pow (n + 1)
      have h_pos := beta_pow_pos (n + 1)
      have h_lt := beta_pow_lt_one n
      constructor
      · linarith
      · linarith
    rw [h_ceil]
    exact S_odd n
```
