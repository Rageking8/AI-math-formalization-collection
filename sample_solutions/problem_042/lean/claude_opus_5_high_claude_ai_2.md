# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `31 August 2026`\
Line count: `26`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem im_div_re_is_integer (n : ℕ) (hn : 0 < n) :
    ∃ k : ℤ, (((2 : ℂ) + Complex.I) ^ (2 * n)).im / (((1 : ℂ) + 2 * Complex.I) ^ n).re = (k : ℝ) := by
  clear hn
  have kim : ∀ x y : ℤ, ((x : ℂ) + (y : ℂ) * Complex.I).im = (y : ℝ) := by intros; simp
  have kre : ∀ x y : ℤ, ((x : ℂ) + (y : ℂ) * Complex.I).re = (x : ℝ) := by intros; simp
  obtain ⟨a, b, h, h'⟩ : ∃ a b : ℤ, ((1:ℂ) + 2 * Complex.I) ^ n = a + b * Complex.I ∧
      ((1:ℂ) - 2 * Complex.I) ^ n = a - b * Complex.I := by
    induction n with
    | zero => exact ⟨1, 0, by simp, by simp⟩
    | succ p ih =>
      obtain ⟨a, b, h, h'⟩ := ih
      refine ⟨a - 2 * b, 2 * a + b, ?_, ?_⟩ <;> simp only [pow_succ, h, h'] <;> push_cast <;>
        linear_combination (2 * (b : ℂ)) * Complex.I_sq
  have h5 : ((2:ℂ) + Complex.I) ^ (2 * n) = (((-1) ^ n * (a ^ 2 - b ^ 2) : ℤ) : ℂ)
      + (((-1) ^ (n + 1) * 2 * a * b : ℤ) : ℂ) * Complex.I := by
    rw [pow_mul, show ((2:ℂ) + Complex.I) ^ 2 = -1 * ((1:ℂ) - 2 * Complex.I) ^ 2 by
      linear_combination (5 : ℂ) * Complex.I_sq,
      mul_pow, ← pow_mul, mul_comm 2 n, pow_mul, h']
    push_cast
    linear_combination ((-1 : ℂ) ^ n * (b : ℂ) ^ 2) * Complex.I_sq
  rw [h5, h, kim, kre]
  rcases eq_or_ne ((a : ℝ)) 0 with ha | ha
  · exact ⟨0, by rw [ha, div_zero]; simp⟩
  · exact ⟨(-1) ^ (n + 1) * 2 * b, by rw [div_eq_iff ha]; push_cast; ring⟩
```
