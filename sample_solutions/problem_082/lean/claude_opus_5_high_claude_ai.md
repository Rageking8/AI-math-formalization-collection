# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `27 August 2026`\
Line count: `198`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem infinite_product_cos_fract :
    Filter.Tendsto (fun N => ∏ n ∈ Finset.Icc 1 N,
      (1 + 2 * Real.cos (Real.pi * Int.fract (25 / (2 * (3 : ℝ) ^ n) -
      Int.fract (16 / (2 * (3 : ℝ) ^ n))))) / 3)
      Filter.atTop (nhds ((2 * Real.sqrt 2) / (9 * Real.pi))) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  have fract_add_int : ∀ (r : ℝ) (m : ℤ), Int.fract (r + (m : ℝ)) = Int.fract r := by
    intro r m
    have h1 : Int.fract (r + (m:ℝ)) = (r + (m:ℝ)) - (⌊r + (m:ℝ)⌋ : ℝ) := rfl
    have h2 : Int.fract r = r - (⌊r⌋ : ℝ) := rfl
    have h3 : (⌊r + (m:ℝ)⌋ : ℤ) = ⌊r⌋ + m := by
      first
        | exact Int.floor_add_int r m
        | exact Int.floor_add_intCast r m
        | simp
    rw [h1, h2, h3]
    push_cast
    ring
  have alg : ∀ u t s c : ℝ, t ≠ 0 → s ≠ 0 → c ≠ 0 →
      u / (t * (s * c)) * (c / 3) = u / (3 * t * s) := by
    intro u t s c ht hs hc
    field_simp
    try ring
  have hpow1 : ∀ n : ℕ, (1:ℝ) ≤ 3 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
      have h : (3:ℝ) ^ (k + 1) = 3 * 3 ^ k := by ring
      rw [h]; linarith
  have hpowne : ∀ n : ℕ, ((3:ℝ) ^ n) ≠ 0 := by
    intro n; positivity
  have tri : ∀ x : ℝ, Real.sin (3 * x) = Real.sin x * (1 + 2 * Real.cos (2 * x)) := by
    intro x
    rw [Real.sin_three_mul, Real.cos_two_mul]
    linear_combination (-4 * Real.sin x) * Real.sin_sq_add_cos_sq x
  have hspos : ∀ n : ℕ, 0 < Real.sin (9 * Real.pi / (4 * (3:ℝ) ^ (n + 1))) := by
    intro n
    have hd : (0:ℝ) < 4 * (3:ℝ) ^ (n + 1) := by positivity
    have h12 : (12:ℝ) ≤ 4 * (3:ℝ) ^ (n + 1) := by
      have h : (3:ℝ) ^ (n + 1) = 3 * 3 ^ n := by ring
      have h2 := hpow1 n
      rw [h]; linarith
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact div_pos (by linarith) hd
    · have hEq : Real.pi - 9 * Real.pi / (4 * (3:ℝ) ^ (n + 1))
          = Real.pi * (4 * (3:ℝ) ^ (n + 1) - 9) / (4 * (3:ℝ) ^ (n + 1)) := by
        field_simp
        try ring
      have hp2 : 0 < Real.pi * (4 * (3:ℝ) ^ (n + 1) - 9) / (4 * (3:ℝ) ^ (n + 1)) :=
        div_pos (mul_pos hpi (by linarith)) hd
      linarith
  have hsin0 : Real.sin (9 * Real.pi / (4 * (3:ℝ) ^ (0:ℕ))) = Real.sqrt 2 / 2 := by
    have h : 9 * Real.pi / (4 * (3:ℝ) ^ (0:ℕ)) = Real.pi / 4 + 2 * Real.pi := by
      rw [pow_zero]; ring
    rw [h, Real.sin_add_two_pi, Real.sin_pi_div_four]
  have hsne : ∀ M : ℕ, Real.sin (9 * Real.pi / (4 * (3:ℝ) ^ M)) ≠ 0 := by
    intro M
    cases M with
    | zero => rw [hsin0]; positivity
    | succ k => exact ne_of_gt (hspos k)
  have key : ∀ n : ℕ, 1 ≤ n →
      (1 + 2 * Real.cos (Real.pi * Int.fract (25 / (2 * (3 : ℝ) ^ n) -
        Int.fract (16 / (2 * (3 : ℝ) ^ n))))) / 3
      = (1 + 2 * Real.cos (2 * (9 * Real.pi / (4 * (3:ℝ) ^ n)))) / 3 := by
    intro n hn
    have hfd : Int.fract (16 / (2 * (3:ℝ) ^ n))
        = 16 / (2 * (3:ℝ) ^ n) - (Int.floor (16 / (2 * (3:ℝ) ^ n)) : ℝ) := rfl
    have hb : 25 / (2 * (3:ℝ) ^ n) - Int.fract (16 / (2 * (3:ℝ) ^ n))
        = 9 / (2 * (3:ℝ) ^ n) + (Int.floor (16 / (2 * (3:ℝ) ^ n)) : ℝ) := by
      rw [hfd]
      have h9 : 25 / (2 * (3:ℝ) ^ n) - 16 / (2 * (3:ℝ) ^ n) = 9 / (2 * (3:ℝ) ^ n) := by
        rw [div_sub_div_same]; norm_num
      linarith
    rw [hb, fract_add_int]
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      have hf : Int.fract ((9:ℝ) / (2 * (3:ℝ) ^ (1:ℕ))) = 1 / 2 := by
        have h : (9:ℝ) / (2 * (3:ℝ) ^ (1:ℕ)) = 1 / 2 + ((1:ℤ) : ℝ) := by
          rw [pow_one]; norm_num
        rw [h, fract_add_int]
        exact Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩
      rw [hf]
      have c1 : Real.cos (Real.pi * (1 / 2 : ℝ)) = 0 := by
        rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring, Real.cos_pi_div_two]
      have c2 : Real.cos (2 * (9 * Real.pi / (4 * (3:ℝ) ^ (1:ℕ)))) = 0 := by
        rw [show 2 * (9 * Real.pi / (4 * (3:ℝ) ^ (1:ℕ))) = Real.pi + Real.pi / 2 by
              rw [pow_one]; ring, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi]
        ring
      rw [c1, c2]
    · obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      subst hk
      have h3 : ((3:ℝ) ^ (k + 2)) ≠ 0 := hpowne (k + 2)
      have h9 : (9:ℝ) ≤ 3 ^ (k + 2) := by
        have h : (3:ℝ) ^ (k + 2) = 9 * 3 ^ k := by ring
        have h2 := hpow1 k
        rw [h]; linarith
      have hd : (0:ℝ) < 2 * (3:ℝ) ^ (k + 2) := by positivity
      have hlt : (9:ℝ) / (2 * (3:ℝ) ^ (k + 2)) < 1 := by
        have hEq : (1:ℝ) - 9 / (2 * (3:ℝ) ^ (k + 2))
            = (2 * (3:ℝ) ^ (k + 2) - 9) / (2 * (3:ℝ) ^ (k + 2)) := by
          field_simp
          try ring
        have hp : 0 < (2 * (3:ℝ) ^ (k + 2) - 9) / (2 * (3:ℝ) ^ (k + 2)) :=
          div_pos (by linarith) hd
        linarith
      have hf : Int.fract ((9:ℝ) / (2 * (3:ℝ) ^ (k + 2))) = 9 / (2 * (3:ℝ) ^ (k + 2)) :=
        Int.fract_eq_self.2 ⟨by positivity, hlt⟩
      rw [hf]
      have harg : Real.pi * (9 / (2 * (3:ℝ) ^ (k + 2)))
          = 2 * (9 * Real.pi / (4 * (3:ℝ) ^ (k + 2))) := by
        field_simp
        try ring
      rw [harg]
  have hfun : ∀ N : ℕ, (∏ n ∈ Finset.Icc 1 N,
      (1 + 2 * Real.cos (Real.pi * Int.fract (25 / (2 * (3 : ℝ) ^ n) -
        Int.fract (16 / (2 * (3 : ℝ) ^ n))))) / 3)
      = ∏ n ∈ Finset.Icc 1 N, (1 + 2 * Real.cos (2 * (9 * Real.pi / (4 * (3:ℝ) ^ n)))) / 3 := by
    intro N
    refine Finset.prod_congr rfl ?_
    intro n hn
    exact key n (Finset.mem_Icc.mp hn).1
  have hprod : ∀ N : ℕ,
      (∏ n ∈ Finset.Icc 1 N, (1 + 2 * Real.cos (2 * (9 * Real.pi / (4 * (3:ℝ) ^ n)))) / 3)
      = Real.sqrt 2 / 2 / ((3:ℝ) ^ N * Real.sin (9 * Real.pi / (4 * (3:ℝ) ^ N))) := by
    intro N
    induction N with
    | zero =>
      have hemp : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
      have hs2 : (Real.sqrt 2 / 2 : ℝ) ≠ 0 := by positivity
      rw [hemp, Finset.prod_empty, hsin0, pow_zero, one_mul]
      exact (div_self hs2).symm
    | succ M ih =>
      have h3M : ((3:ℝ) ^ M) ≠ 0 := hpowne M
      have h3M1 : ((3:ℝ) ^ (M + 1)) ≠ 0 := hpowne (M + 1)
      have hx : 3 * (9 * Real.pi / (4 * (3:ℝ) ^ (M + 1))) = 9 * Real.pi / (4 * (3:ℝ) ^ M) := by
        field_simp
        try ring
      have hid : Real.sin (9 * Real.pi / (4 * (3:ℝ) ^ M))
          = Real.sin (9 * Real.pi / (4 * (3:ℝ) ^ (M + 1)))
            * (1 + 2 * Real.cos (2 * (9 * Real.pi / (4 * (3:ℝ) ^ (M + 1))))) := by
        rw [← hx, tri]
      have hsM1 : Real.sin (9 * Real.pi / (4 * (3:ℝ) ^ (M + 1))) ≠ 0 := hsne (M + 1)
      have hcne : (1 + 2 * Real.cos (2 * (9 * Real.pi / (4 * (3:ℝ) ^ (M + 1))))) ≠ 0 := by
        intro hc
        rw [hc, mul_zero] at hid
        exact hsne M hid
      rw [Finset.prod_Icc_succ_top (show 1 ≤ M + 1 by omega), ih, hid,
        alg (Real.sqrt 2 / 2) ((3:ℝ) ^ M) _ _ h3M hsM1 hcne,
        show (3:ℝ) * 3 ^ M = 3 ^ (M + 1) from by ring]
  have heq : ∀ N : ℕ, (∏ n ∈ Finset.Icc 1 N,
      (1 + 2 * Real.cos (Real.pi * Int.fract (25 / (2 * (3 : ℝ) ^ n) -
        Int.fract (16 / (2 * (3 : ℝ) ^ n))))) / 3)
      = Real.sqrt 2 / 2 / ((3:ℝ) ^ N * Real.sin (9 * Real.pi / (4 * (3:ℝ) ^ N))) := by
    intro N; rw [hfun N, hprod N]
  simp only [heq]
  have hsinlim : Filter.Tendsto (fun y : ℝ => Real.sin y / y)
      (nhdsWithin 0 {(0:ℝ)}ᶜ) (nhds 1) := by
    have h : HasDerivAt Real.sin 1 0 := by simpa using Real.hasDerivAt_sin 0
    rw [hasDerivAt_iff_tendsto_slope] at h
    refine h.congr (fun y => ?_)
    rw [slope_def_field, Real.sin_zero, sub_zero, sub_zero]
  have hu : Filter.Tendsto (fun N : ℕ => 9 * Real.pi / (4 * (3:ℝ) ^ N)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.Tendsto.const_mul_atTop (by norm_num)
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)))
  have hupos : ∀ N : ℕ, 0 < 9 * Real.pi / (4 * (3:ℝ) ^ N) := by
    intro N
    exact div_pos (by linarith) (by positivity)
  have hu' : Filter.Tendsto (fun N : ℕ => 9 * Real.pi / (4 * (3:ℝ) ^ N)) Filter.atTop
      (nhdsWithin 0 {(0:ℝ)}ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu
      (Filter.Eventually.of_forall (fun N => ne_of_gt (hupos N)))
  have hdiv : Filter.Tendsto
      (fun N : ℕ => Real.sin (9 * Real.pi / (4 * (3:ℝ) ^ N)) / (9 * Real.pi / (4 * (3:ℝ) ^ N)))
      Filter.atTop (nhds 1) := hsinlim.comp hu'
  have hfinal : Filter.Tendsto
      (fun N : ℕ => (3:ℝ) ^ N * Real.sin (9 * Real.pi / (4 * (3:ℝ) ^ N)))
      Filter.atTop (nhds (9 * Real.pi / 4)) := by
    have h := hdiv.const_mul (9 * Real.pi / 4)
    rw [mul_one] at h
    refine h.congr (fun N => ?_)
    have h3 : ((3:ℝ) ^ N) ≠ 0 := hpowne N
    field_simp
    try ring
  have hne : (9 * Real.pi / 4 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hc : Filter.Tendsto (fun _ : ℕ => Real.sqrt 2 / 2) Filter.atTop
      (nhds (Real.sqrt 2 / 2)) := tendsto_const_nhds
  have hlim := hc.div hfinal hne
  have hval : Real.sqrt 2 / 2 / (9 * Real.pi / 4) = 2 * Real.sqrt 2 / (9 * Real.pi) := by
    field_simp
    try ring
  rw [hval] at hlim
  exact hlim
```
