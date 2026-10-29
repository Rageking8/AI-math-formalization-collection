# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `31 July 2026`\
Line count: `275`\
Turn count: `2`

## Solution

```lean4
import Mathlib

open MeasureTheory

theorem integral_fract_ceil (n : ℕ) (hn : 0 < n) :
    ∫ x in (0 : ℝ)..(n : ℝ),
      x * Int.fract ((n : ℝ) / x) * (Int.ceil ((n : ℝ) / x) : ℝ) = ((n : ℝ) ^ 2) / 2 := by
  have hcastZ : Measurable (fun z : ℤ => (z : ℝ)) := by
    first
      | exact measurable_from_top
      | exact fun s _ => trivial
      | measurability
  have hfloorm : Measurable (fun x : ℝ => ⌊x⌋) := by
    first
      | exact Int.measurable_floor
      | exact measurable_id.floor
      | measurability
  have hfractm : Measurable (Int.fract : ℝ → ℝ) := by
    have h : (Int.fract : ℝ → ℝ) = fun x : ℝ => x - ((⌊x⌋ : ℤ) : ℝ) := rfl
    rw [h]
    exact measurable_id.sub (hcastZ.comp hfloorm)
  have hceilcast : ∀ y : ℝ, ((⌈y⌉ : ℤ) : ℝ) = y + Int.fract (-y) := by
    intro y
    have h2 : Int.fract (-y) = -y - ((⌊-y⌋ : ℤ) : ℝ) := rfl
    rw [h2, Int.floor_neg]
    push_cast
    ring
  have main : ∀ (N : ℝ) (f : ℝ → ℝ), 0 < N →
      (∀ x : ℝ, f x = x * Int.fract (N / x) * ((⌈N / x⌉ : ℤ) : ℝ)) →
      (∫ x in (0:ℝ)..N, f x) = N ^ 2 / 2 := by
    intro N f hN hfeq
    have hN2 : (0:ℝ) < N ^ 2 := pow_pos hN 2
    -- measurability of `f`
    have hmeas : Measurable f := by
      have hdiv : Measurable (fun x : ℝ => N / x) := measurable_const.div measurable_id
      have h1 : Measurable (fun x : ℝ => Int.fract (N / x)) := hfractm.comp hdiv
      have h2 : Measurable (fun x : ℝ => ((⌈N / x⌉ : ℤ) : ℝ)) := by
        have hh : (fun x : ℝ => ((⌈N / x⌉ : ℤ) : ℝ))
            = fun x : ℝ => N / x + Int.fract (-(N / x)) := by
          funext x; exact hceilcast _
        rw [hh]
        exact hdiv.add (hfractm.comp hdiv.neg)
      have hh : f = fun x : ℝ => x * Int.fract (N / x) * ((⌈N / x⌉ : ℤ) : ℝ) := funext hfeq
      rw [hh]
      exact (measurable_id.mul h1).mul h2
    -- pointwise bound on `(0, N]`
    have hbd : ∀ x : ℝ, 0 < x → x ≤ N → ‖f x‖ ≤ 2 * N := by
      intro x hx0 hxN
      have hxne : x ≠ 0 := ne_of_gt hx0
      have hy : 0 < N / x := div_pos hN hx0
      have h1 : Int.fract (N / x) < 1 := Int.fract_lt_one _
      have h2 : (0:ℝ) ≤ Int.fract (N / x) := Int.fract_nonneg _
      have h3 : ((⌈N / x⌉ : ℤ) : ℝ) < N / x + 1 := Int.ceil_lt_add_one _
      have h4 : (0:ℝ) ≤ ((⌈N / x⌉ : ℤ) : ℝ) := by
        have hc : (0:ℤ) ≤ ⌈N / x⌉ := Int.ceil_nonneg hy.le
        exact_mod_cast hc
      have hfx : 0 ≤ f x := by
        rw [hfeq]
        exact mul_nonneg (mul_nonneg hx0.le h2) h4
      have hxn : x * (N / x + 1) = N + x := by
        field_simp
      rw [Real.norm_eq_abs, abs_of_nonneg hfx, hfeq]
      have step1 : x * Int.fract (N / x) ≤ x := by
        nlinarith [mul_pos hx0 (sub_pos.mpr h1)]
      have step2 : x * Int.fract (N / x) * ((⌈N / x⌉ : ℤ) : ℝ) ≤ x * ((⌈N / x⌉ : ℤ) : ℝ) :=
        mul_le_mul_of_nonneg_right step1 h4
      have step3 : x * ((⌈N / x⌉ : ℤ) : ℝ) ≤ x * (N / x + 1) :=
        mul_le_mul_of_nonneg_left h3.le hx0.le
      linarith
    -- integrability on subintervals of `[0, N]`
    have hII : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ N → IntervalIntegrable f volume a b := by
      intro a b ha hab hbN
      have hconst : IntervalIntegrable (fun _ : ℝ => 2 * N) volume a b := intervalIntegrable_const
      apply IntervalIntegrable.mono_fun hconst hmeas.aestronglyMeasurable
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
      rw [Set.uIoc_of_le hab] at hx
      have hb2 : ‖(2:ℝ) * N‖ = 2 * N := by
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg (by linarith)
      show ‖f x‖ ≤ ‖(2:ℝ) * N‖
      rw [hb2]
      exact hbd x (lt_of_le_of_lt ha hx.1) (le_trans hx.2 hbN)
    -- the value of `f` on each piece
    have hpiece : ∀ (k : ℕ), 1 ≤ k → ∀ x : ℝ, N / ((k:ℝ) + 1) < x → x < N / (k:ℝ) →
        f x = ((k:ℝ) + 1) * (N - (k:ℝ) * x) := by
      intro k hk x hx1 hx2
      have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
      have hkne : (k:ℝ) ≠ 0 := ne_of_gt hk0
      have hk1 : (0:ℝ) < (k:ℝ) + 1 := by linarith
      have hk1ne : (k:ℝ) + 1 ≠ 0 := ne_of_gt hk1
      have hxpos : 0 < x := lt_of_le_of_lt (div_nonneg hN.le hk1.le) hx1
      have hxne : x ≠ 0 := ne_of_gt hxpos
      have hinv : (0:ℝ) < x⁻¹ := inv_pos.mpr hxpos
      have hkk : (k:ℝ) * (N / (k:ℝ)) = N := by field_simp
      have hkk1 : ((k:ℝ) + 1) * (N / ((k:ℝ) + 1)) = N := by field_simp
      have hkx : (k:ℝ) * x < N := by
        have h := mul_lt_mul_of_pos_left hx2 hk0
        linarith [hkk]
      have hkx1 : N < ((k:ℝ) + 1) * x := by
        have h := mul_lt_mul_of_pos_left hx1 hk1
        linarith [hkk1]
      have hy1 : (k:ℝ) < N / x := by
        have h := mul_lt_mul_of_pos_right hkx hinv
        rw [mul_assoc, mul_inv_cancel₀ hxne, mul_one] at h
        rwa [div_eq_mul_inv]
      have hy2 : N / x < (k:ℝ) + 1 := by
        have h := mul_lt_mul_of_pos_right hkx1 hinv
        rw [mul_assoc, mul_inv_cancel₀ hxne, mul_one] at h
        rwa [div_eq_mul_inv]
      have hfloor : ⌊N / x⌋ = (k : ℤ) := by
        rw [Int.floor_eq_iff]
        constructor
        · push_cast; linarith
        · push_cast; linarith
      have hceil : ⌈N / x⌉ = (k : ℤ) + 1 := by
        rw [Int.ceil_eq_iff]
        constructor
        · push_cast; linarith
        · push_cast; linarith
      have hfr : Int.fract (N / x) = N / x - (k:ℝ) := by
        have hd : Int.fract (N / x) = N / x - ((⌊N / x⌋ : ℤ) : ℝ) := rfl
        rw [hd, hfloor]
        push_cast
        try ring
      have hxx : x * (N / x) = N := by field_simp
      rw [hfeq, hfr, hceil]
      push_cast
      linear_combination ((k:ℝ) + 1) * hxx
    -- integral of a linear function, via FTC
    have hpolyint : ∀ c d a b : ℝ,
        (∫ x in a..b, (c - d * x)) = c * (b - a) - d * (b ^ 2 - a ^ 2) / 2 := by
      intro c d a b
      have hderiv : ∀ x ∈ Set.uIcc a b,
          HasDerivAt (fun y : ℝ => c * y - d * y ^ 2 / 2) (c - d * x) x := by
        intro x _
        have h1 : HasDerivAt (fun y : ℝ => c * y) c x := by
          simpa using (hasDerivAt_id x).const_mul c
        have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        have h3 : HasDerivAt (fun y : ℝ => d * y ^ 2 / 2) (d * (2 * x) / 2) x :=
          (h2.const_mul d).div_const 2
        have heq : c - d * x = c - d * (2 * x) / 2 := by ring
        rw [heq]
        exact h1.sub h3
      have hint : IntervalIntegrable (fun x : ℝ => c - d * x) volume a b :=
        (continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable a b
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      ring
    -- integral over one piece
    have hpieceint : ∀ (k : ℕ), 1 ≤ k →
        (∫ x in (N / ((k:ℝ) + 1))..(N / (k:ℝ)), f x) = N ^ 2 / (2 * (k:ℝ) * ((k:ℝ) + 1)) := by
      intro k hk
      have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
      have hk1 : (0:ℝ) < (k:ℝ) + 1 := by linarith
      have hkne : (k:ℝ) ≠ 0 := ne_of_gt hk0
      have hk1ne : (k:ℝ) + 1 ≠ 0 := ne_of_gt hk1
      have hlt : N / ((k:ℝ) + 1) < N / (k:ℝ) := by
        have e1 : N / (k:ℝ) - N / ((k:ℝ) + 1) = N / ((k:ℝ) * ((k:ℝ) + 1)) := by
          field_simp
          try ring
        have e2 : 0 < N / ((k:ℝ) * ((k:ℝ) + 1)) := div_pos hN (mul_pos hk0 hk1)
        linarith
      have hae : (∫ x in (N / ((k:ℝ) + 1))..(N / (k:ℝ)), f x)
          = ∫ x in (N / ((k:ℝ) + 1))..(N / (k:ℝ)),
              (((k:ℝ) + 1) * N - ((k:ℝ) + 1) * (k:ℝ) * x) := by
        apply intervalIntegral.integral_congr_ae
        have h0 : ∀ᵐ (x : ℝ), x ≠ N / (k:ℝ) := by
          rw [MeasureTheory.ae_iff]
          simp
        filter_upwards [h0] with x hx hmem
        rw [Set.uIoc_of_le hlt.le] at hmem
        rw [hpiece k hk x hmem.1 (lt_of_le_of_ne hmem.2 hx)]
        ring
      rw [hae, hpolyint]
      field_simp
      try ring
    -- telescoping
    have hmain : ∀ m : ℕ, 1 ≤ m →
        (∫ x in (N / (m:ℝ))..N, f x) = N ^ 2 * ((m:ℝ) - 1) / (2 * (m:ℝ)) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ p hp ih =>
        have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
        have hpne : (p:ℝ) ≠ 0 := ne_of_gt hp0
        have hp1 : (0:ℝ) < (p:ℝ) + 1 := by linarith
        have hp1ne : (p:ℝ) + 1 ≠ 0 := ne_of_gt hp1
        have hNple : N / (p:ℝ) ≤ N := div_le_self hN.le (by exact_mod_cast hp)
        have hle1 : N / ((p:ℝ) + 1) ≤ N / (p:ℝ) := by
          have e1 : N / (p:ℝ) - N / ((p:ℝ) + 1) = N / ((p:ℝ) * ((p:ℝ) + 1)) := by
            field_simp
            try ring
          have e2 : 0 < N / ((p:ℝ) * ((p:ℝ) + 1)) := div_pos hN (mul_pos hp0 hp1)
          linarith
        have h0a : (0:ℝ) ≤ N / ((p:ℝ) + 1) := div_nonneg hN.le hp1.le
        have h0b : (0:ℝ) ≤ N / (p:ℝ) := div_nonneg hN.le hp0.le
        have key := intervalIntegral.integral_add_adjacent_intervals
          (hII (N / ((p:ℝ) + 1)) (N / (p:ℝ)) h0a hle1 hNple)
          (hII (N / (p:ℝ)) N h0b hNple le_rfl)
        push_cast
        rw [← key, hpieceint p hp, ih]
        field_simp
        try ring
    -- the remaining bit near 0 is small
    have htail : ∀ m : ℕ, 1 ≤ m →
        |∫ x in (0:ℝ)..(N / (m:ℝ)), f x| ≤ 2 * N * (N / (m:ℝ)) := by
      intro m hm
      have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
      have hmle : N / (m:ℝ) ≤ N := div_le_self hN.le (by exact_mod_cast hm)
      have hnn : (0:ℝ) ≤ N / (m:ℝ) := div_nonneg hN.le hm0.le
      have hC : ∀ x ∈ Set.uIoc (0:ℝ) (N / (m:ℝ)), ‖f x‖ ≤ 2 * N := by
        intro x hx
        rw [Set.uIoc_of_le hnn] at hx
        exact hbd x hx.1 (le_trans hx.2 hmle)
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hC
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hnn] at h
      exact h
    have hsplit : ∀ m : ℕ, 1 ≤ m →
        (∫ x in (0:ℝ)..N, f x)
          = (∫ x in (0:ℝ)..(N / (m:ℝ)), f x) + N ^ 2 * ((m:ℝ) - 1) / (2 * (m:ℝ)) := by
      intro m hm
      have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
      have hmle : N / (m:ℝ) ≤ N := div_le_self hN.le (by exact_mod_cast hm)
      have hnn : (0:ℝ) ≤ N / (m:ℝ) := div_nonneg hN.le hm0.le
      rw [← hmain m hm]
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hII 0 (N / (m:ℝ)) le_rfl hnn hmle) (hII (N / (m:ℝ)) N hnn hmle le_rfl)).symm
    have hfinal : ∀ m : ℕ, 1 ≤ m →
        |(∫ x in (0:ℝ)..N, f x) - N ^ 2 / 2| ≤ 3 * (N ^ 2 / (m:ℝ)) := by
      intro m hm
      have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
      have hmne : (m:ℝ) ≠ 0 := ne_of_gt hm0
      have h1 := hsplit m hm
      have h2 := htail m hm
      have hidt : N ^ 2 * ((m:ℝ) - 1) / (2 * (m:ℝ)) - N ^ 2 / 2
          = -(N ^ 2 / (m:ℝ) / 2) := by
        field_simp
        try ring
      have e1 : 2 * N * (N / (m:ℝ)) = 2 * (N ^ 2 / (m:ℝ)) := by
        field_simp
        try ring
      have e3 : (0:ℝ) ≤ N ^ 2 / (m:ℝ) := div_nonneg hN2.le hm0.le
      rw [abs_le] at h2
      rw [e1] at h2
      rw [abs_le]
      constructor
      · linarith [h1, hidt, h2.1, h2.2, e3]
      · linarith [h1, hidt, h2.1, h2.2, e3]
    have habs : ∀ a : ℝ, (∀ m : ℕ, 1 ≤ m → |a| ≤ 3 * (N ^ 2 / (m:ℝ))) → a = 0 := by
      intro a ha
      by_contra hcon
      have hepos : 0 < |a| := abs_pos.mpr hcon
      have hane : |a| ≠ 0 := ne_of_gt hepos
      obtain ⟨m, hm⟩ := exists_nat_gt (3 * N ^ 2 / |a|)
      have hq : 0 < 3 * N ^ 2 / |a| := div_pos (by linarith) hepos
      have hm0 : (0:ℝ) < (m:ℝ) := lt_trans hq hm
      have hmne : (m:ℝ) ≠ 0 := ne_of_gt hm0
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; norm_num at hm0
        · exact h
      have hb := ha m hm1
      have h5 : |a| * (m:ℝ) ≤ 3 * (N ^ 2 / (m:ℝ)) * (m:ℝ) :=
        mul_le_mul_of_nonneg_right hb hm0.le
      have h6 : 3 * (N ^ 2 / (m:ℝ)) * (m:ℝ) = 3 * N ^ 2 := by
        field_simp
        try ring
      have h7 : 3 * N ^ 2 / |a| * |a| < (m:ℝ) * |a| := mul_lt_mul_of_pos_right hm hepos
      have h8 : 3 * N ^ 2 / |a| * |a| = 3 * N ^ 2 := by
        field_simp
        try ring
      linarith
    have hzero := habs ((∫ x in (0:ℝ)..N, f x) - N ^ 2 / 2) hfinal
    linarith [hzero]
  exact main (n : ℝ) _ (by exact_mod_cast hn) (fun x => rfl)
```
