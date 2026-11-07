# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `23 September 2026`\
Line count: `82`\
Turn count: `3 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem sgn_add_sub_eq (x y : ℝ) :
    Real.sign (x + y) + Real.sign (x - y) =
      Real.sign (Real.sin x + x) * (1 + Real.sign (x ^ 4 - y ^ 4)) := by
  have sign_cases : ∀ a : ℝ,
      (Real.sign a = -1 ∧ a < 0) ∨ (Real.sign a = 0 ∧ a = 0) ∨ (Real.sign a = 1 ∧ 0 < a) := by
    intro a
    rcases lt_trichotomy a 0 with h | h | h
    · exact Or.inl ⟨Real.sign_of_neg h, h⟩
    · exact Or.inr (Or.inl ⟨by rw [h]; exact Real.sign_zero, h⟩)
    · exact Or.inr (Or.inr ⟨Real.sign_of_pos h, h⟩)
  have sign_mul_local : ∀ a b : ℝ, Real.sign (a * b) = Real.sign a * Real.sign b := by
    intro a b
    rcases sign_cases a with ⟨hsa, ha⟩ | ⟨hsa, ha⟩ | ⟨hsa, ha⟩ <;>
      rcases sign_cases b with ⟨hsb, hb⟩ | ⟨hsb, hb⟩ | ⟨hsb, hb⟩ <;>
      rw [hsa, hsb]
    · rw [Real.sign_of_pos (mul_pos_of_neg_of_neg ha hb)]; norm_num
    · rw [hb, mul_zero, Real.sign_zero]; norm_num
    · rw [Real.sign_of_neg (mul_neg_of_neg_of_pos ha hb)]; norm_num
    · rw [ha, zero_mul, Real.sign_zero]; norm_num
    · rw [ha, zero_mul, Real.sign_zero]; norm_num
    · rw [ha, zero_mul, Real.sign_zero]; norm_num
    · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb)]; norm_num
    · rw [hb, mul_zero, Real.sign_zero]; norm_num
    · rw [Real.sign_of_pos (mul_pos ha hb)]; norm_num
  have hpos : ∀ z : ℝ, 0 < z → 0 < z + Real.sin z := by
    intro z hz
    by_cases h1 : z ≤ 1
    · have hzpi : z < Real.pi := by linarith [Real.pi_gt_three]
      have hsinpos := Real.sin_pos_of_pos_of_lt_pi hz hzpi
      linarith
    · push_neg at h1
      have hsb := Real.neg_one_le_sin z
      linarith
  have hsin : Real.sign (Real.sin x + x) = Real.sign x := by
    rcases sign_cases x with ⟨hs, hx⟩ | ⟨hs, hx⟩ | ⟨hs, hx⟩
    · have h1 : Real.sin x + x < 0 := by
        have h2 := hpos (-x) (by linarith)
        rw [Real.sin_neg] at h2
        linarith
      rw [Real.sign_of_neg h1, hs]
    · subst hx
      simp [Real.sign_zero, Real.sin_zero]
    · have h1 : 0 < Real.sin x + x := by
        have h2 := hpos x hx
        linarith
      rw [Real.sign_of_pos h1, hs]
  rw [hsin]
  have hx2pos : x ≠ 0 → 0 < x ^ 2 := by
    intro h
    rcases lt_or_gt_of_ne h with h' | h'
    · nlinarith [mul_pos_of_neg_of_neg h' h']
    · nlinarith [mul_pos h' h']
  have hy2pos : y ≠ 0 → 0 < y ^ 2 := by
    intro h
    rcases lt_or_gt_of_ne h with h' | h'
    · nlinarith [mul_pos_of_neg_of_neg h' h']
    · nlinarith [mul_pos h' h']
  have hquartic : Real.sign (x ^ 4 - y ^ 4) = Real.sign (x + y) * Real.sign (x - y) := by
    have e1 : x ^ 2 - y ^ 2 = (x + y) * (x - y) := by ring
    have e2 : x ^ 4 - y ^ 4 = (x ^ 2 + y ^ 2) * (x ^ 2 - y ^ 2) := by ring
    rw [e2, sign_mul_local, e1, sign_mul_local]
    by_cases hxy : x = 0 ∧ y = 0
    · obtain ⟨hx0, hy0⟩ := hxy
      subst hx0; subst hy0
      norm_num [Real.sign_zero]
    · have hpos2 : (0:ℝ) < x ^ 2 + y ^ 2 := by
        rcases not_and_or.mp hxy with h | h
        · have := hx2pos h
          linarith [sq_nonneg y]
        · have := hy2pos h
          linarith [sq_nonneg x]
      rw [Real.sign_of_pos hpos2, one_mul]
  rw [hquartic]
  rcases sign_cases (x + y) with ⟨hSs, hs⟩ | ⟨hSs, hs⟩ | ⟨hSs, hs⟩ <;>
    rcases sign_cases (x - y) with ⟨hSt, ht⟩ | ⟨hSt, ht⟩ | ⟨hSt, ht⟩ <;>
    rcases sign_cases x with ⟨hSc, hc⟩ | ⟨hSc, hc⟩ | ⟨hSc, hc⟩ <;>
    rw [hSs, hSt, hSc] <;>
    first
      | (exfalso; linarith)
      | norm_num
```
