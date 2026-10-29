# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `7 August 2026`\
Line count: `52`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem im_div_re_is_integer (n : ℕ) (hn : 0 < n) :
    ∃ k : ℤ, (((2 : ℂ) + Complex.I) ^ (2 * n)).im / (((1 : ℂ) + 2 * Complex.I) ^ n).re = (k : ℝ) := by
  have key : ∀ m : ℕ, ∃ a b : ℤ,
      ((1 : ℂ) + 2 * Complex.I) ^ m = (a : ℂ) + (b : ℂ) * Complex.I ∧
      ((1 : ℂ) - 2 * Complex.I) ^ m = (a : ℂ) - (b : ℂ) * Complex.I := by
    intro m
    induction m with
    | zero => exact ⟨1, 0, by norm_num, by norm_num⟩
    | succ j ih =>
      obtain ⟨a, b, h1, h2⟩ := ih
      refine ⟨a - 2 * b, 2 * a + b, ?_, ?_⟩
      · rw [pow_succ, h1]
        push_cast
        linear_combination (2 * (b : ℂ)) * Complex.I_sq
      · rw [pow_succ, h2]
        push_cast
        linear_combination (2 * (b : ℂ)) * Complex.I_sq
  obtain ⟨a, b, h1, h2⟩ := key n
  obtain ⟨c, hcC⟩ : ∃ c : ℤ, ((c : ℂ)) = (-1) ^ n := ⟨(-1) ^ n, by push_cast; try ring⟩
  have hbase : ((2 : ℂ) + Complex.I) ^ 2 = (-1) * ((1 : ℂ) - 2 * Complex.I) ^ 2 := by
    linear_combination (5 : ℂ) * Complex.I_sq
  have hsq : (((1 : ℂ) - 2 * Complex.I) ^ n) ^ 2 = (((1 : ℂ) - 2 * Complex.I) ^ 2) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
  have hpow : ((2 : ℂ) + Complex.I) ^ (2 * n)
      = (c : ℂ) * ((a : ℂ) - (b : ℂ) * Complex.I) ^ 2 := by
    rw [← h2, hsq, hcC, pow_mul, hbase, mul_pow]
  have hfull : ((2 : ℂ) + Complex.I) ^ (2 * n)
      = ((c * (a ^ 2 - b ^ 2) : ℤ) : ℂ) + ((-2 * c * a * b : ℤ) : ℂ) * Complex.I := by
    rw [hpow]
    push_cast
    linear_combination ((c : ℂ) * (b : ℂ) ^ 2) * Complex.I_sq
  have him : (((2 : ℂ) + Complex.I) ^ (2 * n)).im = ((-2 * c * a * b : ℤ) : ℝ) := by
    rw [hfull]
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im]
    ring
  have hre : (((1 : ℂ) + 2 * Complex.I) ^ n).re = ((a : ℤ) : ℝ) := by
    rw [h1]
    simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im]
    ring
  by_cases ha : a = 0
  · refine ⟨0, ?_⟩
    rw [him, hre, ha]
    simp
  · refine ⟨-2 * c * b, ?_⟩
    have ha' : ((a : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
    rw [him, hre, div_eq_iff ha']
    push_cast
    ring
```
