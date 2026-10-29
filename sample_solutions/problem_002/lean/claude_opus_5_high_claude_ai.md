# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `29 July 2026`\
Line count: `55`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem sin_mul_upper_bound
    (x y z : ℝ)
    (h : x + y + z = Real.pi) :
    Real.sin x * Real.sin y * Real.sin z ≤
      (3 * Real.sqrt 3) / 8 := by
  have ht : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have ht0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  -- Key one-variable lemma: if s ≥ 0 and s² + k² = 1 then s(1+k) ≤ 3√3/4
  have key : ∀ s k : ℝ, 0 ≤ s → s ^ 2 + k ^ 2 = 1 → s * (1 + k) ≤ 3 * Real.sqrt 3 / 4 := by
    intro s k hs hsk
    have hk : -1 ≤ k := by linarith [sq_nonneg s, sq_nonneg (k + 1)]
    have hA : 0 ≤ s * (1 + k) := mul_nonneg hs (by linarith)
    have hs2 : s ^ 2 = 1 - k ^ 2 := by linarith
    have h1 : (s * (1 + k)) ^ 2 = (1 - k ^ 2) * (1 + k) ^ 2 := by
      linear_combination (1 + k) ^ 2 * hs2
    have hsq : (s * (1 + k)) ^ 2 ≤ 27 / 16 := by
      rw [h1]
      nlinarith [sq_nonneg ((2 * k - 1) * (2 * k + 3)), sq_nonneg (2 * k - 1)]
    by_contra hcon
    push_neg at hcon
    have hB : (0 : ℝ) < 3 * Real.sqrt 3 / 4 := by linarith
    have hB2 : (3 * Real.sqrt 3 / 4) ^ 2 = 27 / 16 := by linear_combination (9 / 16) * ht
    nlinarith [hcon, hB, hsq, hB2]
  -- Main algebraic inequality on the torus
  have main : ∀ a b c d : ℝ, a ^ 2 + b ^ 2 = 1 → c ^ 2 + d ^ 2 = 1 →
      a * c * (a * d + b * c) ≤ 3 * Real.sqrt 3 / 8 := by
    intro a b c d ha hc
    have hSK : (a * d + b * c) ^ 2 + (b * d - a * c) ^ 2 = 1 := by
      have e : (a * d + b * c) ^ 2 + (b * d - a * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
        ring
      rw [e, ha, hc, mul_one]
    have hC : (b * d + a * c) ^ 2 + (a * d - b * c) ^ 2 = 1 := by
      have e : (b * d + a * c) ^ 2 + (a * d - b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
        ring
      rw [e, ha, hc, mul_one]
    have hCle : (b * d + a * c) ^ 2 ≤ 1 := by linarith [sq_nonneg (a * d - b * c)]
    have hC2 : b * d + a * c ≤ 1 := by linarith [sq_nonneg (b * d + a * c - 1)]
    have hC1 : -1 ≤ b * d + a * c := by linarith [sq_nonneg (b * d + a * c + 1)]
    rcases le_total 0 (a * d + b * c) with hS | hS
    · have h1 := key (a * d + b * c) (-(b * d - a * c)) hS (by linear_combination hSK)
      have h2 : 0 ≤ (a * d + b * c) * (1 - (b * d + a * c)) :=
        mul_nonneg hS (by linarith)
      linarith [h1, h2]
    · have hS' : 0 ≤ -(a * d + b * c) := by linarith
      have h1 := key (-(a * d + b * c)) (b * d - a * c) hS' (by linear_combination hSK)
      have h2 : 0 ≤ -(a * d + b * c) * (1 + (b * d + a * c)) :=
        mul_nonneg hS' (by linarith)
      linarith [h1, h2]
  have hz : z = Real.pi - (x + y) := by linarith
  subst hz
  rw [Real.sin_pi_sub, Real.sin_add]
  exact main (Real.sin x) (Real.cos x) (Real.sin y) (Real.cos y)
    (Real.sin_sq_add_cos_sq x) (Real.sin_sq_add_cos_sq y)
```
