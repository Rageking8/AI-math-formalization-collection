# Claude Opus 5.5 High (Claude AI)

Model: `Claude Opus 5.5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `200`\
Turn count: `3`

## Solution

```lean4
import Mathlib

open MeasureTheory

theorem integral_fract_ceil (n : ℕ) (hn : 0 < n) :
    ∫ x in (0 : ℝ)..(n : ℝ),
      x * Int.fract ((n : ℝ) / x) * (Int.ceil ((n : ℝ) / x) : ℝ) = ((n : ℝ) ^ 2) / 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn' : (n : ℝ) ≠ 0 := hnpos.ne'
  have h0n : (0 : ℝ) ≤ n := hnpos.le
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℝ → ℝ, ψ = fun s => Int.fract s * (1 - Int.fract s) := ⟨_, rfl⟩
  have hψc : Continuous ψ := by
    rw [hψdef]
    exact ContinuousOn.comp_fract''
      (show ContinuousOn (fun u : ℝ => u * (1 - u)) (Set.Icc 0 1) from
        (by fun_prop : Continuous (fun u : ℝ => u * (1 - u))).continuousOn) (by norm_num)
  have hψ0 : ∀ s, 0 ≤ ψ s := by
    intro s
    rw [hψdef]
    show 0 ≤ Int.fract s * (1 - Int.fract s)
    have h1 := Int.fract_nonneg s
    have h2 := Int.fract_lt_one s
    exact mul_nonneg h1 (by linarith)
  have hψ1 : ∀ s, ψ s ≤ 1 := by
    intro s
    rw [hψdef]
    show Int.fract s * (1 - Int.fract s) ≤ 1
    have h1 := Int.fract_nonneg s
    have h2 := Int.fract_lt_one s
    nlinarith
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ,
      G = fun y => ((n : ℝ) * y + y ^ 2 * ψ (-((n : ℝ) / y))) / 2 := ⟨_, rfl⟩
  have hG0 : G 0 = 0 := by rw [hG]; simp
  have hGn : G n = (n : ℝ) ^ 2 / 2 := by
    have hf1 : Int.fract (-1 : ℝ) = 0 := by
      have : ⌊(-1 : ℝ)⌋ = -1 := by
        rw [Int.floor_eq_iff]; norm_num
      unfold Int.fract
      rw [this]; norm_num
    simp only [hG, hψdef, div_self hn', hf1]
    ring
  -- continuity
  have hcont : ContinuousOn G (Set.Icc 0 (n : ℝ)) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      show Filter.Tendsto G (nhdsWithin 0 (Set.Icc 0 (n : ℝ))) (nhds (G 0))
      rw [hG0]
      have hl : Filter.Tendsto (fun y : ℝ => (n : ℝ) * y / 2)
          (nhdsWithin 0 (Set.Icc 0 (n : ℝ))) (nhds 0) := by
        have hc : Continuous (fun y : ℝ => (n : ℝ) * y / 2) := by fun_prop
        exact (hc.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      have hu : Filter.Tendsto (fun y : ℝ => ((n : ℝ) * y + y ^ 2) / 2)
          (nhdsWithin 0 (Set.Icc 0 (n : ℝ))) (nhds 0) := by
        have hc : Continuous (fun y : ℝ => ((n : ℝ) * y + y ^ 2) / 2) := by fun_prop
        exact (hc.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu ?_ ?_
      · intro y
        rw [hG]
        show (n : ℝ) * y / 2 ≤ ((n : ℝ) * y + y ^ 2 * ψ (-((n : ℝ) / y))) / 2
        have := mul_nonneg (sq_nonneg y) (hψ0 (-((n : ℝ) / y)))
        linarith
      · intro y
        rw [hG]
        show ((n : ℝ) * y + y ^ 2 * ψ (-((n : ℝ) / y))) / 2 ≤ ((n : ℝ) * y + y ^ 2) / 2
        have := mul_le_of_le_one_right (sq_nonneg y) (hψ1 (-((n : ℝ) / y)))
        linarith
    · have hx0 : x ≠ 0 := h.ne'
      apply ContinuousAt.continuousWithinAt
      rw [hG]
      have h1 : ContinuousAt (fun y : ℝ => -((n : ℝ) / y)) x :=
        (continuousAt_const.div continuousAt_id hx0).neg
      have h2 : ContinuousAt (fun y : ℝ => ψ (-((n : ℝ) / y))) x :=
        hψc.continuousAt.comp h1
      first
      | exact ((continuousAt_const.mul continuousAt_id).add
          ((continuousAt_id.pow 2).mul h2)).div_const 2
      | fun_prop (disch := assumption)
  -- derivative
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) n \ Set.range (fun j : ℤ => (n : ℝ) / j),
      HasDerivAt G (x * Int.fract ((n : ℝ) / x) * (⌈(n : ℝ) / x⌉ : ℝ)) x := by
    rintro x ⟨⟨hx0, _⟩, hxS⟩
    have hx0' : x ≠ 0 := hx0.ne'
    obtain ⟨k, hk⟩ : ∃ k : ℤ, ⌊(n : ℝ) / x⌋ = k := ⟨_, rfl⟩
    have hk1 : (k : ℝ) ≤ (n : ℝ) / x := by rw [← hk]; exact Int.floor_le _
    have h2 : (n : ℝ) / x < (k : ℝ) + 1 := by rw [← hk]; exact Int.lt_floor_add_one _
    have hne : (n : ℝ) / x ≠ (k : ℝ) := by
      intro h
      apply hxS
      refine ⟨k, ?_⟩
      show (n : ℝ) / (k : ℝ) = x
      rw [← h]
      field_simp
    have h1 : (k : ℝ) < (n : ℝ) / x := lt_of_le_of_ne hk1 (Ne.symm hne)
    have hfrx : Int.fract ((n : ℝ) / x) = (n : ℝ) / x - k := by
      unfold Int.fract; rw [hk]
    have hceil : ⌈(n : ℝ) / x⌉ = k + 1 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    have ex : x * ((n : ℝ) / x) = n := by field_simp
    have hval : x * Int.fract ((n : ℝ) / x) * (⌈(n : ℝ) / x⌉ : ℝ)
        = ((k : ℝ) + 1) * (1 - ((k : ℝ) + 1)) * x + ((k : ℝ) + 1) * n := by
      rw [hfrx, hceil]; push_cast
      linear_combination ((k : ℝ) + 1) * ex
    have hca : ContinuousAt (fun y : ℝ => (n : ℝ) / y) x :=
      continuousAt_const.div continuousAt_id hx0'
    have ev1 : ∀ᶠ y in nhds x, (k : ℝ) < (n : ℝ) / y :=
      hca.tendsto.eventually (lt_mem_nhds h1)
    have ev2 : ∀ᶠ y in nhds x, (n : ℝ) / y < (k : ℝ) + 1 :=
      hca.tendsto.eventually (gt_mem_nhds h2)
    have ev3 : ∀ᶠ y in nhds x, (0 : ℝ) < y := lt_mem_nhds hx0
    have heq : G =ᶠ[nhds x] (fun y : ℝ => ((k : ℝ) + 1) * (1 - ((k : ℝ) + 1)) / 2 * (y * y)
        + ((k : ℝ) + 1) * n * y - (n : ℝ) ^ 2 / 2) := by
      filter_upwards [ev1, ev2, ev3] with y hy1 hy2 hy3
      have hy0 : y ≠ 0 := hy3.ne'
      have hfl : ⌊-((n : ℝ) / y)⌋ = -(k + 1) := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      have hfr : Int.fract (-((n : ℝ) / y)) = -((n : ℝ) / y) + ((k : ℝ) + 1) := by
        unfold Int.fract
        rw [hfl, Int.cast_neg, Int.cast_add, Int.cast_one]
        ring
      have ey : y * ((n : ℝ) / y) = n := by field_simp
      simp only [hG, hψdef]
      rw [hfr]
      linear_combination
        (((2 * ((k : ℝ) + 1) - 1) * y - (y * ((n : ℝ) / y) + n)) / 2) * ey
    have hP : HasDerivAt (fun y : ℝ => ((k : ℝ) + 1) * (1 - ((k : ℝ) + 1)) / 2 * (y * y)
        + ((k : ℝ) + 1) * n * y - (n : ℝ) ^ 2 / 2)
        (((k : ℝ) + 1) * (1 - ((k : ℝ) + 1)) * x + ((k : ℝ) + 1) * n) x := by
      have h := ((((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul
        (((k : ℝ) + 1) * (1 - ((k : ℝ) + 1)) / 2)).add
        ((hasDerivAt_id x).const_mul (((k : ℝ) + 1) * n))).sub_const ((n : ℝ) ^ 2 / 2)
      convert h using 1 <;>
        first
        | (funext y; simp only [Pi.add_apply, Pi.mul_apply, id_eq, id]; try ring)
        | (simp only [id_eq, id]; ring)
    rw [hval]
    exact hP.congr_of_eventuallyEq heq
  -- integrability
  have hmeas : Measurable
      (fun x : ℝ => x * Int.fract ((n : ℝ) / x) * (⌈(n : ℝ) / x⌉ : ℝ)) := by
    have hd : Measurable (fun x : ℝ => (n : ℝ) / x) := by
      first
      | exact measurable_const.div measurable_id
      | fun_prop
      | measurability
    have hcast : Measurable (fun z : ℤ => (z : ℝ)) := by
      first
      | exact measurable_of_countable _
      | exact Measurable.of_discrete
      | fun_prop
      | measurability
    have hc : Measurable (fun x : ℝ => ((⌈(n : ℝ) / x⌉ : ℤ) : ℝ)) :=
      hcast.comp (Int.measurable_ceil.comp hd)
    have hf : Measurable (fun x : ℝ => Int.fract ((n : ℝ) / x)) :=
      measurable_fract.comp hd
    first
    | exact (measurable_id.mul hf).mul hc
    | fun_prop
  have hi : IntervalIntegrable
      (fun x : ℝ => x * Int.fract ((n : ℝ) / x) * (⌈(n : ℝ) / x⌉ : ℝ)) volume 0 n := by
    have hconst : IntervalIntegrable (fun _ : ℝ => 2 * (n : ℝ)) volume 0 n :=
      continuous_const.intervalIntegrable 0 n
    refine hconst.mono_fun hmeas.aestronglyMeasurable ?_
    rw [Set.uIoc_of_le h0n]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun x hx => ?_))
    simp only [Real.norm_eq_abs]
    obtain ⟨hx0, hxn⟩ := hx
    have hx0' : x ≠ 0 := hx0.ne'
    have ex : x * ((n : ℝ) / x) = n := by field_simp
    have hf0 := Int.fract_nonneg ((n : ℝ) / x)
    have hf1 := Int.fract_lt_one ((n : ℝ) / x)
    have hc1 : (n : ℝ) / x ≤ (⌈(n : ℝ) / x⌉ : ℝ) := Int.le_ceil _
    have hc2 : (⌈(n : ℝ) / x⌉ : ℝ) < (n : ℝ) / x + 1 := Int.ceil_lt_add_one _
    have ht : 0 < (n : ℝ) / x := div_pos hnpos hx0
    have hxc : 0 ≤ x * (⌈(n : ℝ) / x⌉ : ℝ) := mul_nonneg hx0.le (by linarith)
    have e : x * Int.fract ((n : ℝ) / x) * (⌈(n : ℝ) / x⌉ : ℝ)
        = (x * (⌈(n : ℝ) / x⌉ : ℝ)) * Int.fract ((n : ℝ) / x) := by ring
    have hA : 0 ≤ x * Int.fract ((n : ℝ) / x) * (⌈(n : ℝ) / x⌉ : ℝ) := by
      rw [e]; exact mul_nonneg hxc hf0
    have hB : x * Int.fract ((n : ℝ) / x) * (⌈(n : ℝ) / x⌉ : ℝ) ≤ 2 * n := by
      have e2 : (x * (⌈(n : ℝ) / x⌉ : ℝ)) * Int.fract ((n : ℝ) / x)
          ≤ x * (⌈(n : ℝ) / x⌉ : ℝ) := mul_le_of_le_one_right hxc hf1.le
      have e3 : x * (⌈(n : ℝ) / x⌉ : ℝ) ≤ x * ((n : ℝ) / x + 1) :=
        mul_le_mul_of_nonneg_left hc2.le hx0.le
      have e4 : x * ((n : ℝ) / x + 1) = n + x := by rw [mul_add, ex, mul_one]
      linarith
    rw [abs_of_nonneg hA, abs_of_nonneg (show (0 : ℝ) ≤ 2 * n by positivity)]
    exact hB
  -- FTC
  have key : ∫ x in (0 : ℝ)..(n : ℝ), x * Int.fract ((n : ℝ) / x) * (⌈(n : ℝ) / x⌉ : ℝ)
      = G n - G 0 := by
    first
    | exact integral_eq_of_hasDerivWithinAt_off_countable_of_le G
        (fun x : ℝ => x * Int.fract ((n : ℝ) / x) * (⌈(n : ℝ) / x⌉ : ℝ)) h0n
        (Set.countable_range (fun j : ℤ => (n : ℝ) / j)) hcont hderiv hi
    | exact integral_eq_of_hasDerivAt_off_countable_of_le G
        (fun x : ℝ => x * Int.fract ((n : ℝ) / x) * (⌈(n : ℝ) / x⌉ : ℝ)) h0n
        (Set.countable_range (fun j : ℤ => (n : ℝ) / j)) hcont hderiv hi
  rw [key, hGn, hG0]
  ring
```
