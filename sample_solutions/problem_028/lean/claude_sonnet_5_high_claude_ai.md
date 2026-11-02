# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `7 September 2026`\
Line count: `67`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem unique_real_solution_nested_radical (x : ℝ) (hx : 0 ≤ x) :
    (19 * Real.sqrt (2 * x + 1) + 34 * Real.sqrt x) ^ (1 / 3 : ℝ) =
      Real.sqrt (2 * x + 1) + Real.sqrt x ↔ x = 4 := by
  set a := Real.sqrt (2 * x + 1) with ha_def
  set b := Real.sqrt x with hb_def
  have ha0 : 0 ≤ a := by rw [ha_def]; exact Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := by rw [hb_def]; exact Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * x + 1 := by rw [ha_def]; exact Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = x := by rw [hb_def]; exact Real.sq_sqrt hx
  have hab : a ^ 2 = 2 * b ^ 2 + 1 := by rw [hb2]; exact ha2
  have hapos : 0 < a := by nlinarith [hab, sq_nonneg b]
  have cube_iff : ∀ y z : ℝ, 0 ≤ y → 0 ≤ z → (y ^ (1 / 3 : ℝ) = z ↔ y = z ^ 3) := by
    intro y z hy hz
    have zpow3 : z ^ (3 : ℝ) = z ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    constructor
    · intro h
      have h1 : y ^ ((1 / 3 : ℝ) * 3) = y := by
        rw [show (1 / 3 : ℝ) * 3 = 1 by norm_num, Real.rpow_one]
      rw [Real.rpow_mul hy, h, zpow3] at h1
      exact h1.symm
    · intro h
      rw [h, ← zpow3, ← Real.rpow_mul hz, show (3 : ℝ) * (1 / 3 : ℝ) = 1 by norm_num,
        Real.rpow_one]
  have hy0 : (0 : ℝ) ≤ 19 * a + 34 * b := by linarith [ha0, hb0]
  have hz0 : (0 : ℝ) ≤ a + b := by linarith [ha0, hb0]
  rw [cube_iff (19 * a + 34 * b) (a + b) hy0 hz0]
  constructor
  · intro heq
    have heq2 : a * (5 * b ^ 2 - 18) + b * (7 * b ^ 2 - 31) = 0 := by
      linear_combination -heq - (a + 3 * b) * hab
    have hsq : a ^ 2 * (5 * b ^ 2 - 18) ^ 2 = b ^ 2 * (7 * b ^ 2 - 31) ^ 2 := by
      have hXY : a * (5 * b ^ 2 - 18) = -(b * (7 * b ^ 2 - 31)) := by linarith [heq2]
      calc a ^ 2 * (5 * b ^ 2 - 18) ^ 2 = (a * (5 * b ^ 2 - 18)) ^ 2 := by ring
        _ = (-(b * (7 * b ^ 2 - 31))) ^ 2 := by rw [hXY]
        _ = b ^ 2 * (7 * b ^ 2 - 31) ^ 2 := by ring
    have hcubic : (2 * b ^ 2 + 1) * (5 * b ^ 2 - 18) ^ 2 = b ^ 2 * (7 * b ^ 2 - 31) ^ 2 := by
      rw [← hab]; exact hsq
    have hfactor : (b ^ 2 - 4) * ((b ^ 2) ^ 2 + 103 * b ^ 2 - 81) = 0 := by
      linear_combination hcubic
    rcases mul_eq_zero.mp hfactor with h4 | h2
    · have hbeq4 : b ^ 2 = 4 := by linarith
      linarith [hb2, hbeq4]
    · exfalso
      have hb2lt1 : b ^ 2 < 1 := by nlinarith [h2, sq_nonneg (b ^ 2), sq_nonneg b]
      have hlt1 : 5 * b ^ 2 - 18 < 0 := by linarith
      have hlt2 : 7 * b ^ 2 - 31 < 0 := by linarith
      have hbpos : 0 < b := by
        by_contra hcon
        push_neg at hcon
        have hb0' : b = 0 := le_antisymm hcon hb0
        rw [hb0'] at h2
        norm_num at h2
      have hn1 : a * (5 * b ^ 2 - 18) < 0 := mul_neg_of_pos_of_neg hapos hlt1
      have hn2 : b * (7 * b ^ 2 - 31) < 0 := mul_neg_of_pos_of_neg hbpos hlt2
      linarith [heq2, hn1, hn2]
  · intro hx4
    have hbval : b = 2 := by
      rw [hb_def, hx4, show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    have haval : a = 3 := by
      rw [ha_def, hx4, show (2 * (4 : ℝ) + 1) = 3 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [haval, hbval]
    norm_num
```
