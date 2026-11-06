# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `15 September 2026`\
Line count: `113`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def preconditions (a b : ℂ) : Prop :=
  ‖a ^ 3 + b ^ 3‖ = 2 ∧ 1 ≤ ‖a - b‖ ∧ ‖a - b‖ ≤ 2

theorem tight_lower_bound_complex_ratio :
    let bound := (Real.goldenRatio ^ (1 / 3 : ℝ) - (Real.goldenRatio - 1) ^ (1 / 3 : ℝ)) ^ 2;
      (∀ a b : ℂ, preconditions a b → bound ≤ ‖a + b‖ ^ 2 / ‖a - b‖ ^ 2) ∧
      (∃ a b : ℂ, preconditions a b ∧ ‖a + b‖ ^ 2 / ‖a - b‖ ^ 2 = bound) := by
  intro bound
  have hbound : bound
      = (Real.goldenRatio ^ (1 / 3 : ℝ) - (Real.goldenRatio - 1) ^ (1 / 3 : ℝ)) ^ 2 := rfl
  -- facts about √5 and φ
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5nn : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs5gt : (2:ℝ) < Real.sqrt 5 := by nlinarith
  have hg : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have hgpos : (0:ℝ) < Real.goldenRatio := by rw [hg]; linarith
  have hg1pos : (0:ℝ) < Real.goldenRatio - 1 := by rw [hg]; linarith
  have hcpos : (0:ℝ) < Real.goldenRatio ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hgpos _
  have hepos : (0:ℝ) < (Real.goldenRatio - 1) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hg1pos _
  have hc3 : (Real.goldenRatio ^ (1 / 3 : ℝ)) ^ 3 = Real.goldenRatio := by
    rw [← Real.rpow_natCast (Real.goldenRatio ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hgpos.le]
    norm_num
  have he3 : ((Real.goldenRatio - 1) ^ (1 / 3 : ℝ)) ^ 3 = Real.goldenRatio - 1 := by
    rw [← Real.rpow_natCast ((Real.goldenRatio - 1) ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hg1pos.le]
    norm_num
  have hce : Real.goldenRatio ^ (1 / 3 : ℝ) * (Real.goldenRatio - 1) ^ (1 / 3 : ℝ) = 1 := by
    rw [← Real.mul_rpow hgpos.le hg1pos.le]
    have h1 : Real.goldenRatio * (Real.goldenRatio - 1) = 1 := by
      rw [hg]; linear_combination (1/4 : ℝ) * hs5
    rw [h1, Real.one_rpow]
  have hlt : (Real.goldenRatio - 1) ^ (1 / 3 : ℝ) < Real.goldenRatio ^ (1 / 3 : ℝ) := by
    nlinarith [hc3, he3, hcpos, hepos, mul_pos hcpos hepos,
      sq_nonneg (Real.goldenRatio ^ (1 / 3 : ℝ)),
      sq_nonneg ((Real.goldenRatio - 1) ^ (1 / 3 : ℝ))]
  obtain ⟨u, hupos, hucube, hbu⟩ :
      ∃ u : ℝ, 0 < u ∧ u ^ 3 + 3 * u = 1 ∧ bound = u ^ 2 := by
    refine ⟨Real.goldenRatio ^ (1 / 3 : ℝ) - (Real.goldenRatio - 1) ^ (1 / 3 : ℝ),
      by linarith, ?_, hbound⟩
    linear_combination hc3 - he3
      - 3 * (Real.goldenRatio ^ (1 / 3 : ℝ) - (Real.goldenRatio - 1) ^ (1 / 3 : ℝ)) * hce
  -- the real-variable core of the estimate
  have arith : ∀ x r : ℝ, 0 ≤ x → 1 ≤ r → r ≤ 2 → 8 ≤ x ^ 3 + 3 * x * r ^ 2 →
      u ^ 2 ≤ x ^ 2 / r ^ 2 := by
    intro x r hx0 hr1 hr2 hmain
    have hr0 : (0:ℝ) < r := by linarith
    have hr3 : r ^ 3 ≤ 8 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hr2) (sq_nonneg r),
        mul_nonneg (sub_nonneg.mpr hr2) hr0.le]
    have heq : (u * r) ^ 3 + 3 * (u * r) * r ^ 2 = r ^ 3 := by
      linear_combination r ^ 3 * hucube
    have hle2 : (u * r) ^ 3 + 3 * (u * r) * r ^ 2 ≤ x ^ 3 + 3 * x * r ^ 2 := by
      rw [heq]; linarith
    have hurpos : 0 < u * r := mul_pos hupos hr0
    have hP : 0 < x ^ 2 + x * (u * r) + (u * r) ^ 2 + 3 * r ^ 2 := by
      nlinarith [sq_nonneg x, sq_nonneg (u * r), mul_nonneg hx0 hurpos.le, mul_pos hr0 hr0]
    have hfac : 0 ≤ (x - u * r) * (x ^ 2 + x * (u * r) + (u * r) ^ 2 + 3 * r ^ 2) := by
      nlinarith [hle2]
    have hxur : u * r ≤ x := by nlinarith [hfac, hP]
    have hnum : u ^ 2 * r ^ 2 ≤ x ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxur) (by linarith : (0:ℝ) ≤ x + u * r)]
    have hr2ne : r ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hr0)
    have h1' : u ^ 2 * r ^ 2 * (r ^ 2)⁻¹ ≤ x ^ 2 * (r ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    rwa [mul_inv_cancel_right₀ hr2ne, ← div_eq_mul_inv] at h1'
  have hnormR : ∀ t : ℝ, 0 ≤ t → ‖(t : ℂ)‖ = t := by
    intro t ht
    simp [abs_of_nonneg ht]
  rw [hbu]
  constructor
  · intro a b hab
    obtain ⟨h1, h2, h3⟩ : ‖a ^ 3 + b ^ 3‖ = 2 ∧ 1 ≤ ‖a - b‖ ∧ ‖a - b‖ ≤ 2 := hab
    have hid : (a + b) * ((a + b) ^ 2 + 3 * (a - b) ^ 2) = 4 * (a ^ 3 + b ^ 3) := by ring
    have hn : ‖a + b‖ * ‖(a + b) ^ 2 + 3 * (a - b) ^ 2‖ = 8 := by
      have h : ‖(a + b) * ((a + b) ^ 2 + 3 * (a - b) ^ 2)‖ = ‖(4 : ℂ) * (a ^ 3 + b ^ 3)‖ := by
        rw [hid]
      simp only [norm_mul, h1] at h
      rw [h]
      norm_num
    have hle : ‖(a + b) ^ 2 + 3 * (a - b) ^ 2‖ ≤ ‖a + b‖ ^ 2 + 3 * ‖a - b‖ ^ 2 := by
      calc ‖(a + b) ^ 2 + 3 * (a - b) ^ 2‖
          ≤ ‖(a + b) ^ 2‖ + ‖(3 : ℂ) * (a - b) ^ 2‖ := norm_add_le _ _
        _ = ‖a + b‖ ^ 2 + 3 * ‖a - b‖ ^ 2 := by
            norm_num [norm_mul, norm_pow]
    have hkey : (8:ℝ) ≤ ‖a + b‖ ^ 3 + 3 * ‖a + b‖ * ‖a - b‖ ^ 2 := by
      nlinarith [hn, hle, norm_nonneg (a + b), norm_nonneg (a - b)]
    exact arith ‖a + b‖ ‖a - b‖ (norm_nonneg _) h2 h3 hkey
  · have hucubeC : (u : ℂ) ^ 3 + 3 * (u : ℂ) = 1 := by
      have h := congrArg (fun t : ℝ => (t : ℂ)) hucube
      push_cast at h
      linear_combination h
    have hsub : ((u + 1 : ℝ) : ℂ) - ((u - 1 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) := by
      push_cast; ring
    have hadd : ((u + 1 : ℝ) : ℂ) + ((u - 1 : ℝ) : ℂ) = ((2 * u : ℝ) : ℂ) := by
      push_cast; ring
    have hcube : ((u + 1 : ℝ) : ℂ) ^ 3 + ((u - 1 : ℝ) : ℂ) ^ 3 = ((2 : ℝ) : ℂ) := by
      push_cast
      linear_combination (2 : ℂ) * hucubeC
    have hnsub : ‖((u + 1 : ℝ) : ℂ) - ((u - 1 : ℝ) : ℂ)‖ = 2 := by
      rw [hsub]; exact hnormR 2 (by norm_num)
    have hnadd : ‖((u + 1 : ℝ) : ℂ) + ((u - 1 : ℝ) : ℂ)‖ = 2 * u := by
      rw [hadd]; exact hnormR (2 * u) (by linarith)
    have hncube : ‖((u + 1 : ℝ) : ℂ) ^ 3 + ((u - 1 : ℝ) : ℂ) ^ 3‖ = 2 := by
      rw [hcube]; exact hnormR 2 (by norm_num)
    have hpre0 : ‖((u + 1 : ℝ) : ℂ) ^ 3 + ((u - 1 : ℝ) : ℂ) ^ 3‖ = 2 ∧
        1 ≤ ‖((u + 1 : ℝ) : ℂ) - ((u - 1 : ℝ) : ℂ)‖ ∧
        ‖((u + 1 : ℝ) : ℂ) - ((u - 1 : ℝ) : ℂ)‖ ≤ 2 :=
      ⟨hncube, by rw [hnsub]; norm_num, le_of_eq hnsub⟩
    have hpre : preconditions ((u + 1 : ℝ) : ℂ) ((u - 1 : ℝ) : ℂ) := hpre0
    refine ⟨((u + 1 : ℝ) : ℂ), ((u - 1 : ℝ) : ℂ), hpre, ?_⟩
    rw [hnadd, hnsub]
    ring
```
