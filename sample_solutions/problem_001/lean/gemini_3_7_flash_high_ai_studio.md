# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `22 August 2026`\
Line count: `124`\
Turn count: `1`

## Solution

```lean4
import Mathlib

noncomputable def α : ℝ := ((5 : ℝ) + Real.sqrt 17) / 2
noncomputable def β : ℝ := ((5 : ℝ) - Real.sqrt 17) / 2

def seq : ℕ → ℤ
  | 0 => 2
  | 1 => 5
  | n + 2 => 5 * seq (n + 1) - 2 * seq n

lemma seq_succ_odd (n : ℕ) : Odd (seq (n + 1)) := by
  induction n with
  | zero =>
    exact ⟨2, rfl⟩
  | succ n ih =>
    rcases ih with ⟨k, hk⟩
    refine ⟨5 * k + 2 - seq n, ?_⟩
    calc seq (n + 1 + 1) = 5 * seq (n + 1) - 2 * seq n := rfl
    _ = 5 * (2 * k + 1) - 2 * seq n := by rw [hk]
    _ = 2 * (5 * k + 2 - seq n) + 1 := by ring

lemma seq_eq_pair (n : ℕ) :
    (seq n : ℝ) = α ^ n + β ^ n ∧ (seq (n + 1) : ℝ) = α ^ (n + 1) + β ^ (n + 1) := by
  induction n with
  | zero =>
    constructor
    · show (2 : ℝ) = α ^ 0 + β ^ 0
      rw [pow_zero, pow_zero]
      norm_num
    · show (5 : ℝ) = α ^ 1 + β ^ 1
      rw [pow_one, pow_one]
      dsimp [α, β]
      ring
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · exact ih2
    · have h17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
      have hα2 : α ^ 2 = 5 * α - 2 := by
        have : α ^ 2 - 5 * α + 2 = (Real.sqrt 17 ^ 2 - 17) / 4 := by
          dsimp [α]
          ring
        rw [h17] at this
        linarith
      have hβ2 : β ^ 2 = 5 * β - 2 := by
        have : β ^ 2 - 5 * β + 2 = (Real.sqrt 17 ^ 2 - 17) / 4 := by
          dsimp [β]
          ring
        rw [h17] at this
        linarith
      have hα_rec : α ^ (n + 2) = 5 * α ^ (n + 1) - 2 * α ^ n := by
        calc α ^ (n + 2) = α ^ n * α ^ 2 := by rw [pow_add]
        _ = α ^ n * (5 * α - 2) := by rw [hα2]
        _ = 5 * (α ^ n * α ^ 1) - 2 * α ^ n := by rw [pow_one]; ring
        _ = 5 * α ^ (n + 1) - 2 * α ^ n := by rw [← pow_add]
      have hβ_rec : β ^ (n + 2) = 5 * β ^ (n + 1) - 2 * β ^ n := by
        calc β ^ (n + 2) = β ^ n * β ^ 2 := by rw [pow_add]
        _ = β ^ n * (5 * β - 2) := by rw [hβ2]
        _ = 5 * (β ^ n * β ^ 1) - 2 * β ^ n := by rw [pow_one]; ring
        _ = 5 * β ^ (n + 1) - 2 * β ^ n := by rw [← pow_add]
      calc (seq (n + 1 + 1) : ℝ) = 5 * (seq (n + 1) : ℝ) - 2 * (seq n : ℝ) := by
            show ((5 * seq (n + 1) - 2 * seq n : ℤ) : ℝ) = _
            push_cast
            rfl
        _ = 5 * (α ^ (n + 1) + β ^ (n + 1)) - 2 * (α ^ n + β ^ n) := by rw [ih1, ih2]
        _ = (5 * α ^ (n + 1) - 2 * α ^ n) + (5 * β ^ (n + 1) - 2 * β ^ n) := by ring
        _ = α ^ (n + 2) + β ^ (n + 2) := by rw [← hα_rec, ← hβ_rec]

lemma seq_eq (n : ℕ) : (seq n : ℝ) = α ^ n + β ^ n :=
  (seq_eq_pair n).1

lemma sqrt_17_gt_four : 4 < Real.sqrt 17 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

lemma sqrt_17_lt_five : Real.sqrt 17 < 5 := by
  rw [Real.sqrt_lt (by norm_num) (by norm_num)]
  norm_num

lemma beta_pos : 0 < β := by
  dsimp [β]
  have := sqrt_17_lt_five
  linarith

lemma beta_lt_one : β < 1 := by
  dsimp [β]
  have := sqrt_17_gt_four
  linarith

lemma beta_pow_lt_one (n : ℕ) : β ^ (n + 1) < 1 := by
  induction n with
  | zero =>
    rw [zero_add, pow_one]
    exact beta_lt_one
  | succ n ih =>
    have h_split : β ^ (n + 1 + 1) = β ^ (n + 1) * β := by rw [pow_add, pow_one]
    rw [h_split]
    have hb_pos := beta_pos
    have hb_lt := beta_lt_one
    have h_ih_pos : 0 < β ^ (n + 1) := pow_pos beta_pos (n + 1)
    nlinarith

theorem ceil_pow_expr_odd (x : ℕ) :
    Odd ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ x⌉ := by
  cases x with
  | zero =>
    rw [pow_zero]
    have h : ⌈(1 : ℝ)⌉ = 1 := by
      rw [Int.ceil_eq_iff]
      norm_num
    rw [h]
    exact ⟨0, rfl⟩
  | succ n =>
    have h_seq := seq_eq (n + 1)
    have hβ_pow_pos : 0 < β ^ (n + 1) := pow_pos beta_pos (n + 1)
    have hβ_pow_lt : β ^ (n + 1) < 1 := beta_pow_lt_one n
    have h_ceil : ⌈α ^ (n + 1)⌉ = seq (n + 1) := by
      rw [Int.ceil_eq_iff]
      constructor
      · linarith [h_seq, hβ_pow_lt]
      · linarith [h_seq, hβ_pow_pos]
    show Odd ⌈α ^ (n + 1)⌉
    rw [h_ceil]
    exact seq_succ_odd n
```
