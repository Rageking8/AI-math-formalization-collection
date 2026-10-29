# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `31 July 2026`\
Line count: `109`\
Turn count: `3`

## Solution

```lean4
import Mathlib

theorem distinct_pos_real_power_ineq (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hne : x ≠ y) (h : x ^ y = y ^ x) :
      Real.exp (x + y) < (x ^ x) * (y ^ y) := by
  have expkey : ∀ w : ℝ, 0 < w → (1 - w) * (Real.exp w * Real.exp w) < 1 + w := by
    have hmono : StrictMonoOn (fun u : ℝ => 1 + u - (1 - u) * Real.exp (u + u)) (Set.Ici 0) := by
      have hdiff : Differentiable ℝ (fun u : ℝ => 1 + u - (1 - u) * Real.exp (u + u)) := by
        intro v
        have hid : HasDerivAt (fun u : ℝ => u) 1 v := hasDerivAt_id v
        exact ((hid.const_add (1 : ℝ)).sub
          ((hid.const_sub (1 : ℝ)).mul ((hid.add hid).exp))).differentiableAt
      apply strictMonoOn_of_deriv_pos (convex_Ici 0) hdiff.continuous.continuousOn
      intro v hv
      rw [interior_Ici] at hv
      have hv0 : (0 : ℝ) < v := Set.mem_Ioi.mp hv
      have hid : HasDerivAt (fun u : ℝ => u) 1 v := hasDerivAt_id v
      have h5 : HasDerivAt (fun u : ℝ => 1 + u - (1 - u) * Real.exp (u + u))
          (1 - (-1 * Real.exp (v + v) + (1 - v) * (Real.exp (v + v) * (1 + 1)))) v :=
        (hid.const_add (1 : ℝ)).sub ((hid.const_sub (1 : ℝ)).mul ((hid.add hid).exp))
      rw [h5.deriv]
      have hEpos : 0 < Real.exp (v + v) := Real.exp_pos _
      have hkey : Real.exp (v + v) * (1 - 2 * v) < 1 := by
        by_cases hv1 : (1 : ℝ) ≤ v
        · nlinarith [hEpos, mul_nonneg hEpos.le (sub_nonneg.mpr hv1)]
        · push_neg at hv1
          have h1 : 1 - v ≤ Real.exp (-v) := by
            have h := Real.add_one_le_exp (-v)
            linarith
          have h1' : (0 : ℝ) < 1 - v := by linarith
          have h2 : (1 - v) * (1 - v) ≤ Real.exp (-v) * Real.exp (-v) :=
            mul_le_mul h1 h1 h1'.le (Real.exp_pos _).le
          have h3 : Real.exp (-v) * Real.exp (-v) = Real.exp (-(v + v)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          have h4 : Real.exp (v + v) * Real.exp (-(v + v)) = 1 := by
            rw [← Real.exp_add]
            simp
          have h6 : 1 - 2 * v < Real.exp (-(v + v)) := by
            rw [← h3]
            nlinarith [h2, mul_pos hv0 hv0]
          calc Real.exp (v + v) * (1 - 2 * v)
              < Real.exp (v + v) * Real.exp (-(v + v)) := mul_lt_mul_of_pos_left h6 hEpos
            _ = 1 := h4
      linarith
    intro w hw
    have h0 : 1 + 0 - (1 - 0) * Real.exp (0 + 0) < 1 + w - (1 - w) * Real.exp (w + w) :=
      hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hw.le) hw
    rw [Real.exp_add, Real.exp_add, Real.exp_zero] at h0
    linarith
  have keyineq : ∀ a b : ℝ, 0 < a → a < b →
      b ^ 2 - a ^ 2 < (Real.log b - Real.log a) * (a ^ 2 + b ^ 2) := by
    intro a b ha hab
    have hb : 0 < b := ha.trans hab
    have hw : 0 < Real.log b - Real.log a := by
      have := Real.log_lt_log ha hab
      linarith
    obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = Real.log b - Real.log a := ⟨_, rfl⟩
    rw [← hwdef] at hw ⊢
    have hane : a ≠ 0 := ne_of_gt ha
    have hexp : Real.exp w * a = b := by
      rw [hwdef, Real.exp_sub, Real.exp_log ha, Real.exp_log hb]
      field_simp
    have hk := expkey w hw
    have haa : 0 < a * a := mul_pos ha ha
    have h1 : a * a * ((1 - w) * (Real.exp w * Real.exp w)) < a * a * (1 + w) :=
      mul_lt_mul_of_pos_left hk haa
    have h2 : (1 - w) * (b * b) < (1 + w) * (a * a) := by
      calc (1 - w) * (b * b) = a * a * ((1 - w) * (Real.exp w * Real.exp w)) := by
            rw [← hexp]; ring
        _ < a * a * (1 + w) := h1
        _ = (1 + w) * (a * a) := by ring
    nlinarith [h2]
  have main : ∀ a b : ℝ, 0 < a → a < b → b * Real.log a = a * Real.log b →
      a + b < Real.log a * a + Real.log b * b := by
    intro a b ha hab hc
    have hb : 0 < b := ha.trans hab
    have hba : 0 < b - a := sub_pos.mpr hab
    have hk := keyineq a b ha hab
    have e1 : a * (Real.log b - Real.log a) = Real.log a * (b - a) := by linarith
    have e2 : a * (b ^ 2 - a ^ 2) < a * ((Real.log b - Real.log a) * (a ^ 2 + b ^ 2)) :=
      mul_lt_mul_of_pos_left hk ha
    have e3 : a * (b ^ 2 - a ^ 2) < Real.log a * (b - a) * (a ^ 2 + b ^ 2) := by
      calc a * (b ^ 2 - a ^ 2)
          < a * ((Real.log b - Real.log a) * (a ^ 2 + b ^ 2)) := e2
        _ = a * (Real.log b - Real.log a) * (a ^ 2 + b ^ 2) := by ring
        _ = Real.log a * (b - a) * (a ^ 2 + b ^ 2) := by rw [e1]
    have e4 : (b - a) * (a * (a + b)) < (b - a) * (Real.log a * (a ^ 2 + b ^ 2)) := by
      calc (b - a) * (a * (a + b)) = a * (b ^ 2 - a ^ 2) := by ring
        _ < Real.log a * (b - a) * (a ^ 2 + b ^ 2) := e3
        _ = (b - a) * (Real.log a * (a ^ 2 + b ^ 2)) := by ring
    have e5 : a * (a + b) < Real.log a * (a ^ 2 + b ^ 2) := lt_of_mul_lt_mul_left e4 hba.le
    have e0 : b * (b * Real.log a) = b * (a * Real.log b) := by rw [hc]
    have e6 : a * (Real.log a * a + Real.log b * b) = Real.log a * (a ^ 2 + b ^ 2) := by
      linarith
    have e7 : a * (a + b) < a * (Real.log a * a + Real.log b * b) := by
      rw [e6]; exact e5
    exact lt_of_mul_lt_mul_left e7 ha.le
  have hlog : y * Real.log x = x * Real.log y := by
    have h' := congrArg Real.log h
    rwa [Real.log_rpow hx, Real.log_rpow hy] at h'
  have hfinal : x + y < Real.log x * x + Real.log y * y := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact main x y hx hlt hlog
    · have := main y x hy hgt hlog.symm
      linarith
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, ← Real.exp_add]
  exact Real.exp_lt_exp.mpr hfinal
```
