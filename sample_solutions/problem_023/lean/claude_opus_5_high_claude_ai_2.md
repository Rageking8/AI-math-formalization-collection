# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `12 August 2026`\
Line count: `66`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem distinct_pos_real_power_ineq (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hne : x ≠ y) (h : x ^ y = y ^ x) :
      Real.exp (x + y) < (x ^ x) * (y ^ y) := by
  have crux : ∀ d : ℝ, 0 < d → Real.exp (2 * d) * (1 - d) < 1 + d := by
    have mono : StrictMonoOn (fun t : ℝ => 1 + t - Real.exp (2 * t) * (1 - t)) (Set.Ici 0) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      · exact Continuous.continuousOn (by fun_prop)
      · intro t ht
        simp only [interior_Ici, Set.mem_Ioi] at ht
        have hp := Real.exp_pos (2 * t)
        have h1 : HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (Real.exp (2 * t) * (2 * 1)) t :=
          ((hasDerivAt_id t).const_mul (2 : ℝ)).exp
        have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1 : ℝ) t :=
          (hasDerivAt_id t).const_sub (1 : ℝ)
        have hderiv : HasDerivAt (fun t : ℝ => 1 + t - Real.exp (2 * t) * (1 - t))
            (0 + 1 - (Real.exp (2 * t) * (2 * 1) * (1 - t) + Real.exp (2 * t) * (-1))) t :=
          ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).sub (h1.mul h2)
        rw [hderiv.deriv]
        have hne2 : -(2 * t) ≠ 0 := ne_of_lt (by linarith)
        have h4 := Real.add_one_lt_exp hne2
        rw [Real.exp_neg] at h4
        have h5 := mul_lt_mul_of_pos_left h4 hp
        rw [mul_inv_cancel₀ hp.ne'] at h5
        linarith
    intro d hd
    have h := mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hd.le) hd
    simp only [mul_zero, Real.exp_zero, sub_zero, add_zero, one_mul] at h
    linarith
  have main : ∀ a b : ℝ, a < b → Real.exp b * a = Real.exp a * b →
      Real.exp a + Real.exp b < Real.exp a * a + Real.exp b * b := by
    intro a b hab hrel
    obtain ⟨d, hd, rfl⟩ : ∃ d, 0 < d ∧ b = a + d := ⟨b - a, by linarith, by ring⟩
    have hea := Real.exp_pos a
    rw [Real.exp_add] at hrel ⊢
    have hda : Real.exp d * a = a + d :=
      mul_left_cancel₀ hea.ne' (by rw [← mul_assoc]; exact hrel)
    have hE1 : 1 < Real.exp d := by linarith [Real.add_one_lt_exp hd.ne']
    have hd' : d = Real.exp d * a - a := by linarith
    have hc : Real.exp d * Real.exp d * (1 - d) < 1 + d := by
      have := crux d hd; rwa [two_mul, Real.exp_add] at this
    have h6 : Real.exp d * Real.exp d * d
        = Real.exp d * Real.exp d * (Real.exp d * a - a) := by rw [← hd']
    have key : 1 + Real.exp d < a * (1 + Real.exp d * Real.exp d) := by
      by_contra hcon
      push_neg at hcon
      have hP := mul_le_mul_of_nonneg_right hcon (by linarith : (0:ℝ) ≤ Real.exp d - 1)
      nlinarith [hc, h6, hd', hP]
    rw [← hda]
    nlinarith [mul_lt_mul_of_pos_left key hea]
  have hlog : y * Real.log x = x * Real.log y := by
    have h2 := congrArg Real.log h
    rwa [Real.log_rpow hx, Real.log_rpow hy] at h2
  have hxy : Real.log x ≠ Real.log y := by
    intro hc
    apply hne
    have h3 := congrArg Real.exp hc
    rwa [Real.exp_log hx, Real.exp_log hy] at h3
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, ← Real.exp_add, Real.exp_lt_exp,
    mul_comm (Real.log x) x, mul_comm (Real.log y) y]
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · have := main _ _ hlt (by rw [Real.exp_log hx, Real.exp_log hy]; exact hlog)
    rw [Real.exp_log hx, Real.exp_log hy] at this; linarith
  · have := main _ _ hlt (by rw [Real.exp_log hx, Real.exp_log hy]; exact hlog.symm)
    rw [Real.exp_log hx, Real.exp_log hy] at this; linarith
```
