# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `14 November 2026`\
Line count: `239`\
Turn count: `2`

## Solution

```lean4
import Mathlib

/-!
Idea: on each of `(0, π/3)`, `(π/3, 2π/3)`, `(2π/3, π)` the factor `sign (sin (3x))` is a
constant `c = 1, -1, 1`, and `x * sign (sin (11 x²))` has the continuous antiderivative
`arccos (cos (11 x²)) / 22` (a triangle wave in `x²`), differentiable away from the countable
set where `sin (11 x²) = 0`.  So the FTC with countably many exceptional points applies on each
piece, and the endpoint values of `arccos (cos _)` are computed from `3.14 < π < 3.15`.
-/

/-- Pure algebra behind the derivative computation. -/
private lemma sgn_alg_aux (x s c : ℝ) (hs : s ≠ 0) (h : s ^ 2 + c ^ 2 = 1) :
    -(1 / Real.sqrt (1 - c ^ 2)) * (-s * (11 * (2 * x))) / 22 = x * Real.sign s := by
  have h1 : (1 : ℝ) - c ^ 2 = s ^ 2 := by linarith
  rw [h1, Real.sqrt_sq_eq_abs]
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · rw [abs_of_neg hneg, Real.sign_of_neg hneg]
    have h3 : 1 / -s * -s = 1 := one_div_mul_cancel (neg_ne_zero.mpr hs)
    linear_combination (-x) * h3
  · rw [abs_of_pos hpos, Real.sign_of_pos hpos]
    have h3 : 1 / s * s = 1 := one_div_mul_cancel hs
    linear_combination x * h3

/-- `arccos (cos (11 y²)) / 22` is an antiderivative of `y * sign (sin (11 y²))`
away from the zeros of `sin (11 y²)`. -/
private lemma sgn_hasDerivAt_aux (x : ℝ) (hx : Real.sin (11 * x ^ 2) ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.arccos (Real.cos (11 * y ^ 2)) / 22)
      (x * Real.sign (Real.sin (11 * x ^ 2))) x := by
  have h1 : Real.cos (11 * x ^ 2) ≠ -1 := fun h =>
    hx (Real.sin_eq_zero_iff_cos_eq.mpr (Or.inr h))
  have h2 : Real.cos (11 * x ^ 2) ≠ 1 := fun h =>
    hx (Real.sin_eq_zero_iff_cos_eq.mpr (Or.inl h))
  have hin : HasDerivAt (fun y : ℝ => 11 * y ^ 2) (11 * (2 * x)) x :=
    ((hasDerivAt_pow 2 x).const_mul (11 : ℝ)).congr_deriv
      (by norm_num)
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (11 * y ^ 2))
      (-Real.sin (11 * x ^ 2) * (11 * (2 * x))) x := hin.cos
  -- no type ascription here: with an expected type, Lean unfolds `arccos` before
  -- unifying the composition and picks the wrong decomposition
  have harc := HasDerivAt.comp x (Real.hasDerivAt_arccos h1 h2) hcos
  have hdiv := harc.div_const 22
  exact hdiv.congr_deriv (sgn_alg_aux x _ _ hx (Real.sin_sq_add_cos_sq _))

/-- The exceptional set is countable. -/
private lemma sgn_countable_aux : Set.Countable {x : ℝ | Real.sin (11 * x ^ 2) = 0} := by
  have hsub : {x : ℝ | Real.sin (11 * x ^ 2) = 0} ⊆
      ⋃ n : ℤ, ({Real.sqrt ((n : ℝ) * Real.pi / 11),
        -Real.sqrt ((n : ℝ) * Real.pi / 11)} : Set ℝ) := by
    intro x hx
    have hx' : Real.sin (11 * x ^ 2) = 0 := hx
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hx'
    have hx2 : (n : ℝ) * Real.pi / 11 = x ^ 2 := by linarith
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    show x ∈ ({Real.sqrt ((n : ℝ) * Real.pi / 11),
        -Real.sqrt ((n : ℝ) * Real.pi / 11)} : Set ℝ)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, hx2, Real.sqrt_sq_eq_abs]
    rcases le_total 0 x with h | h
    · left
      rw [abs_of_nonneg h]
    · right
      rw [abs_of_nonpos h, neg_neg]
  exact Set.Countable.mono hsub
    (Set.countable_iUnion fun n => (Set.countable_singleton _).insert _)

private lemma sgn_measurable_sign : Measurable Real.sign := by
  have h : Real.sign = fun r : ℝ => if r < 0 then (-1 : ℝ) else if 0 < r then 1 else 0 := by
    funext r
    first
      | rfl
      | (unfold Real.sign; rfl)
      | simp [Real.sign]
  rw [h]
  first
    | exact Measurable.ite measurableSet_Iio measurable_const
        (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
    | exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
        (Measurable.ite (measurableSet_lt measurable_const measurable_id)
          measurable_const measurable_const)
    | measurability

/-- The integrand is interval integrable on every interval (measurable and bounded by `|x|`). -/
private lemma sgn_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => x * Real.sign (Real.sin (3 * x)) * Real.sign (Real.sin (11 * x ^ 2)))
      MeasureTheory.volume a b := by
  have c1 : Continuous (fun x : ℝ => Real.sin (3 * x)) := by
    first | fun_prop | continuity
  have c2 : Continuous (fun x : ℝ => Real.sin (11 * x ^ 2)) := by
    first | fun_prop | continuity
  have m1 : Measurable (fun x : ℝ => Real.sign (Real.sin (3 * x))) :=
    sgn_measurable_sign.comp c1.measurable
  have m2 : Measurable (fun x : ℝ => Real.sign (Real.sin (11 * x ^ 2))) :=
    sgn_measurable_sign.comp c2.measurable
  have hm : Measurable
      (fun x : ℝ => x * Real.sign (Real.sin (3 * x)) * Real.sign (Real.sin (11 * x ^ 2))) := by
    first
      | exact (measurable_id.mul m1).mul m2
      | measurability
      | fun_prop
  have hb : ∀ r : ℝ, |Real.sign r| ≤ 1 := by
    intro r
    rcases Real.sign_apply_eq r with h | h | h <;> rw [h] <;> first | norm_num | simp
  refine IntervalIntegrable.mono_fun' (g := fun x : ℝ => |x|)
    (Continuous.intervalIntegrable (continuous_abs : Continuous (fun x : ℝ => |x|)) a b)
    hm.aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro x
  show ‖x * Real.sign (Real.sin (3 * x)) * Real.sign (Real.sin (11 * x ^ 2))‖ ≤ |x|
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  calc |x| * |Real.sign (Real.sin (3 * x))| * |Real.sign (Real.sin (11 * x ^ 2))|
      ≤ |x| * |Real.sign (Real.sin (3 * x))| :=
        mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hb _)
    _ ≤ |x| := mul_le_of_le_one_right (abs_nonneg _) (hb _)

/-- FTC on an interval where `sign (sin (3x))` is the constant `c`. -/
private lemma sgn_piece (a b c : ℝ) (hab : a ≤ b)
    (hc : ∀ x ∈ Set.Ioo a b, Real.sign (Real.sin (3 * x)) = c) :
    (∫ x in a..b, x * Real.sign (Real.sin (3 * x)) * Real.sign (Real.sin (11 * x ^ 2))) =
      c * (Real.arccos (Real.cos (11 * b ^ 2)) / 22) -
        c * (Real.arccos (Real.cos (11 * a ^ 2)) / 22) := by
  have hcont : Continuous
      (fun y : ℝ => c * (Real.arccos (Real.cos (11 * y ^ 2)) / 22)) := by
    first
      | fun_prop
      | continuity
      | exact continuous_const.mul
          ((Real.continuous_arccos.comp
            (Real.continuous_cos.comp (continuous_const.mul (continuous_pow 2)))).div_const 22)
  have Hc : ContinuousOn
      (fun y : ℝ => c * (Real.arccos (Real.cos (11 * y ^ 2)) / 22)) (Set.Icc a b) :=
    hcont.continuousOn
  have Hd : ∀ x ∈ Set.Ioo a b \ {x : ℝ | Real.sin (11 * x ^ 2) = 0},
      HasDerivAt (fun y : ℝ => c * (Real.arccos (Real.cos (11 * y ^ 2)) / 22))
        (x * Real.sign (Real.sin (3 * x)) * Real.sign (Real.sin (11 * x ^ 2))) x := by
    intro x hx
    have hx1 : x ∈ Set.Ioo a b := hx.1
    have hx2 : Real.sin (11 * x ^ 2) ≠ 0 := hx.2
    have hd := (sgn_hasDerivAt_aux x hx2).const_mul c
    rw [hc x hx1]
    refine hd.congr_deriv ?_
    ring
  first
    | exact MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
        (fun y : ℝ => c * (Real.arccos (Real.cos (11 * y ^ 2)) / 22))
        (fun x : ℝ => x * Real.sign (Real.sin (3 * x)) * Real.sign (Real.sin (11 * x ^ 2)))
        hab sgn_countable_aux Hc Hd (sgn_intervalIntegrable a b)
    | exact MeasureTheory.integral_eq_of_hasDerivWithinAt_off_countable_of_le
        (fun y : ℝ => c * (Real.arccos (Real.cos (11 * y ^ 2)) / 22))
        (fun x : ℝ => x * Real.sign (Real.sin (3 * x)) * Real.sign (Real.sin (11 * x ^ 2)))
        hab sgn_countable_aux Hc Hd (sgn_intervalIntegrable a b)

/-- `arccos (cos θ) = t - θ` when `t` is a multiple of `2π` and `t - θ ∈ [0, π]`. -/
private lemma sgn_arccos_cos_sub (θ t : ℝ) (n : ℤ) (ht : (n : ℝ) * (2 * Real.pi) = t)
    (h0 : 0 ≤ t - θ) (h1 : t - θ ≤ Real.pi) : Real.arccos (Real.cos θ) = t - θ := by
  subst ht
  exact (congrArg Real.arccos (Real.cos_int_mul_two_pi_sub θ n)).symm.trans
    (Real.arccos_cos h0 h1)

/-- `arccos (cos θ) = θ - t` when `t` is a multiple of `2π` and `θ - t ∈ [0, π]`. -/
private lemma sgn_arccos_cos_sub' (θ t : ℝ) (n : ℤ) (ht : (n : ℝ) * (2 * Real.pi) = t)
    (h0 : 0 ≤ θ - t) (h1 : θ - t ≤ Real.pi) : Real.arccos (Real.cos θ) = θ - t := by
  subst ht
  exact (congrArg Real.arccos (Real.cos_sub_int_mul_two_pi θ n)).symm.trans
    (Real.arccos_cos h0 h1)

theorem integral_sgn_sin :
    ∫ x in (0)..Real.pi,
      x * Real.sign (Real.sin (3 * x)) * Real.sign (Real.sin (11 * x ^ 2)) =
      (5 * Real.pi ^ 2) / 6 - (29 * Real.pi) / 11 := by
  -- numeric bounds on π
  have hpos : 0 < Real.pi := Real.pi_pos
  have hlo : (157 : ℝ) < 50 * Real.pi := by
    have h : (3.14 : ℝ) < Real.pi := by
      first | exact Real.pi_gt_d2 | exact Real.pi_gt_314
    have h' : (3.14 : ℝ) = 157 / 50 := by norm_num
    rw [h'] at h
    linarith
  have hhi : 20 * Real.pi < (63 : ℝ) := by
    have h : Real.pi < (3.15 : ℝ) := by
      first | exact Real.pi_lt_d2 | exact Real.pi_lt_315
    have h' : (3.15 : ℝ) = 63 / 20 := by norm_num
    rw [h'] at h
    linarith
  -- 3.14 π < π² < 3.15 π
  have hA : 0 < Real.pi * (50 * Real.pi - 157) := mul_pos hpos (by linarith)
  have hB : 0 < Real.pi * (63 - 20 * Real.pi) := mul_pos hpos (by linarith)
  -- endpoint values of the antiderivative
  have e0 : Real.arccos (Real.cos (11 * (0 : ℝ) ^ 2)) = 0 := by
    first
      | norm_num
      | simp
      | rw [show (11 : ℝ) * 0 ^ 2 = 0 by norm_num, Real.cos_zero, Real.arccos_one]
  have e1 : Real.arccos (Real.cos (11 * (Real.pi / 3) ^ 2)) =
      4 * Real.pi - 11 * Real.pi ^ 2 / 9 := by
    have a1 : 11 * (Real.pi / 3) ^ 2 = 11 * Real.pi ^ 2 / 9 := by ring
    rw [a1]
    exact sgn_arccos_cos_sub (11 * Real.pi ^ 2 / 9) (4 * Real.pi) 2
      (by first | (push_cast; ring) | (norm_num; ring) | norm_num)
      (by first | linarith | nlinarith [hA, hB, hpos])
      (by first | linarith | nlinarith [hA, hB, hpos])
  have e2 : Real.arccos (Real.cos (11 * (2 * Real.pi / 3) ^ 2)) =
      16 * Real.pi - 44 * Real.pi ^ 2 / 9 := by
    have a2 : 11 * (2 * Real.pi / 3) ^ 2 = 44 * Real.pi ^ 2 / 9 := by ring
    rw [a2]
    exact sgn_arccos_cos_sub (44 * Real.pi ^ 2 / 9) (16 * Real.pi) 8
      (by first | (push_cast; ring) | (norm_num; ring) | norm_num)
      (by first | linarith | nlinarith [hA, hB, hpos])
      (by first | linarith | nlinarith [hA, hB, hpos])
  have e3 : Real.arccos (Real.cos (11 * Real.pi ^ 2)) =
      11 * Real.pi ^ 2 - 34 * Real.pi :=
    sgn_arccos_cos_sub' (11 * Real.pi ^ 2) (34 * Real.pi) 17
      (by first | (push_cast; ring) | (norm_num; ring) | norm_num)
      (by first | linarith | nlinarith [hA, hB, hpos])
      (by first | linarith | nlinarith [hA, hB, hpos])
  -- the three pieces
  have h1 := sgn_piece 0 (Real.pi / 3) 1 (by linarith) (fun x hx =>
    Real.sign_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])))
  have h2 := sgn_piece (Real.pi / 3) (2 * Real.pi / 3) (-1) (by linarith) (fun x hx =>
    Real.sign_of_neg (by
      have h := Real.sin_pos_of_pos_of_lt_pi (x := 3 * x - Real.pi)
        (by linarith [hx.1]) (by linarith [hx.2])
      rw [Real.sin_sub_pi] at h
      linarith))
  have h3 := sgn_piece (2 * Real.pi / 3) Real.pi 1 (by linarith) (fun x hx =>
    Real.sign_of_pos (by
      have h := Real.sin_pos_of_pos_of_lt_pi (x := 3 * x - 2 * Real.pi)
        (by linarith [hx.1]) (by linarith [hx.2])
      rw [Real.sin_sub_two_pi] at h
      exact h))
  -- glue the pieces together
  have s1 := intervalIntegral.integral_add_adjacent_intervals
    (sgn_intervalIntegrable 0 (Real.pi / 3))
    (sgn_intervalIntegrable (Real.pi / 3) (2 * Real.pi / 3))
  have s2 := intervalIntegral.integral_add_adjacent_intervals
    (sgn_intervalIntegrable 0 (2 * Real.pi / 3))
    (sgn_intervalIntegrable (2 * Real.pi / 3) Real.pi)
  first
    | linarith [s1, s2, h1, h2, h3, e0, e1, e2, e3]
    | (rw [← s2, ← s1, h1, h2, h3, e0, e1, e2, e3]; ring)
```
