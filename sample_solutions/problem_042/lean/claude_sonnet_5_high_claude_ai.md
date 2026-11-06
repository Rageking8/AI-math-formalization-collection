# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `15 September 2026`\
Line count: `100`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem im_div_re_is_integer (n : ℕ) (hn : 0 < n) :
    ∃ k : ℤ, (((2 : ℂ) + Complex.I) ^ (2 * n)).im / (((1 : ℂ) + 2 * Complex.I) ^ n).re = (k : ℝ) := by
  -- (2+I)^n is a Gaussian integer a + b*I, for every m
  have hz : ∀ m : ℕ, ∃ a b : ℤ, ((2:ℂ) + Complex.I) ^ m = (a : ℂ) + (b : ℂ) * Complex.I := by
    intro m
    induction m with
    | zero => exact ⟨1, 0, by simp⟩
    | succ k ih =>
      obtain ⟨a, b, hab⟩ := ih
      refine ⟨2 * a - b, a + 2 * b, ?_⟩
      have hstep : ((2:ℂ) + Complex.I) ^ (k + 1)
          = ((2:ℂ) + Complex.I) ^ k * ((2:ℂ) + Complex.I) := pow_succ _ _
      rw [hstep, hab]
      push_cast
      linear_combination (b : ℂ) * Complex.I_sq
  obtain ⟨a, b, hab⟩ := hz n
  -- Im of (2+I)^(2n) = 2ab
  have hz2n : ((2:ℂ) + Complex.I) ^ (2 * n)
      = ((a:ℂ) + (b:ℂ) * Complex.I) * ((a:ℂ) + (b:ℂ) * Complex.I) := by
    rw [two_mul, pow_add, hab]
  have hre0 : ((a:ℂ) + (b:ℂ) * Complex.I).re = (a : ℝ) := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have him0 : ((a:ℂ) + (b:ℂ) * Complex.I).im = (b : ℝ) := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  have him : (((2:ℂ) + Complex.I) ^ (2 * n)).im = 2 * (a : ℝ) * (b : ℝ) := by
    rw [hz2n, Complex.mul_im, hre0, him0]
    ring
  -- Re of (1+2I)^n, via the conjugate trick
  have hzconj2 : (starRingEnd ℂ) ((2:ℂ) + Complex.I) = (2:ℂ) - Complex.I := by
    apply Complex.ext <;>
      simp [Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
            Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  have hzconj : (starRingEnd ℂ) (((2:ℂ) + Complex.I) ^ n) = (a : ℂ) - (b : ℂ) * Complex.I := by
    rw [hab]
    apply Complex.ext <;>
      simp [Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
            Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
            Complex.I_re, Complex.I_im]
  have hconjpow : ((2:ℂ) - Complex.I) ^ n = (a : ℂ) - (b : ℂ) * Complex.I := by
    rw [← hzconj2, ← map_pow, hzconj]
  have hw : (1:ℂ) + 2 * Complex.I = Complex.I * ((2:ℂ) - Complex.I) := by
    linear_combination Complex.I_sq
  have hwn : ((1:ℂ) + 2 * Complex.I) ^ n = Complex.I ^ n * ((a : ℂ) - (b : ℂ) * Complex.I) := by
    rw [hw, mul_pow, hconjpow]
  have hI4 : Complex.I ^ 4 = 1 := by
    have h : Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
    rw [h, Complex.I_sq]
    norm_num
  have hInmod : Complex.I ^ n = Complex.I ^ (n % 4) := by
    conv_lhs => rw [← Nat.div_add_mod n 4]
    rw [pow_add, pow_mul, hI4, one_pow, one_mul]
  have hcase : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have hdiv : ∀ x y : ℝ, ∀ c : ℤ, x = (c : ℝ) * y → ∃ k : ℤ, x / y = (k : ℝ) := by
    intro x y c hxy
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    · exact ⟨c, by rw [hxy, mul_div_assoc, div_self hy, mul_one]⟩
  rcases hcase with h0 | h1 | h2 | h3
  · have hIn : Complex.I ^ n = 1 := by rw [hInmod, h0, pow_zero]
    have hRe : (((1:ℂ) + 2 * Complex.I) ^ n).re = (a : ℝ) := by
      rw [hwn, hIn]
      simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
            Complex.I_re, Complex.I_im]
    refine hdiv _ _ (2 * b) ?_
    rw [him, hRe]
    push_cast
    ring
  · have hIn : Complex.I ^ n = Complex.I := by rw [hInmod, h1, pow_one]
    have hRe : (((1:ℂ) + 2 * Complex.I) ^ n).re = (b : ℝ) := by
      rw [hwn, hIn]
      simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
            Complex.I_re, Complex.I_im]
    refine hdiv _ _ (2 * a) ?_
    rw [him, hRe]
    push_cast
    ring
  · have hIn : Complex.I ^ n = -1 := by rw [hInmod, h2]; exact Complex.I_sq
    have hRe : (((1:ℂ) + 2 * Complex.I) ^ n).re = -(a : ℝ) := by
      rw [hwn, hIn]
      simp [Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
            Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    refine hdiv _ _ (-(2 * b)) ?_
    rw [him, hRe]
    push_cast
    ring
  · have hIn : Complex.I ^ n = -Complex.I := by
      rw [hInmod, h3]
      have h33 : Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      rw [h33, Complex.I_sq]
      ring
    have hRe : (((1:ℂ) + 2 * Complex.I) ^ n).re = -(b : ℝ) := by
      rw [hwn, hIn]
      simp [Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
            Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    refine hdiv _ _ (-(2 * a)) ?_
    rw [him, hRe]
    push_cast
    ring
```
