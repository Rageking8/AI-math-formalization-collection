# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `10 November 2026`\
Line count: `171`\
Turn count: `1`

## Solution

```lean4
import Mathlib

open MeasureTheory

theorem integral_fract_ceil (n : ℕ) (hn : 0 < n) :
    ∫ x in (0 : ℝ)..(n : ℝ),
      x * Int.fract ((n : ℝ) / x) * (Int.ceil ((n : ℝ) / x) : ℝ) = ((n : ℝ) ^ 2) / 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set f : ℝ → ℝ :=
    fun x => x * Int.fract ((n : ℝ) / x) * (Int.ceil ((n : ℝ) / x) : ℝ) with hf
  set s : ℕ → Set ℝ := fun k => Set.Ioc ((n : ℝ) / (k + 2)) ((n : ℝ) / (k + 1)) with hs
  -- On the `k`-th piece the integrand is a polynomial.
  have hpiece : ∀ k : ℕ, Set.EqOn f (fun x => ((n : ℝ) - (k + 1) * x) * (k + 2)) (s k) := by
    intro k x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hk2 : (0 : ℝ) < k + 2 := by positivity
    have hx0 : 0 < x := lt_trans (by positivity) hx1
    have h1 : ((k : ℝ) + 1) ≤ n / x := by
      rw [le_div_iff₀ hx0]
      rw [le_div_iff₀ hk1] at hx2
      linarith
    have h2 : (n : ℝ) / x < k + 2 := by
      rw [div_lt_iff₀ hx0]
      rw [div_lt_iff₀ hk2] at hx1
      linarith
    have hfloor : Int.floor ((n : ℝ) / x) = (k + 1 : ℤ) := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    have hfract : Int.fract ((n : ℝ) / x) = n / x - (k + 1) := by
      rw [Int.fract, hfloor]
      push_cast
      ring
    have hxne : x ≠ 0 := hx0.ne'
    simp only [hf]
    rw [hfract]
    rcases eq_or_lt_of_le h1 with h | h
    · have e : (n : ℝ) - (k + 1) * x = 0 := by
        rw [h]
        field_simp
        ring
      rw [e, ← h]
      simp
    · have hceil : Int.ceil ((n : ℝ) / x) = (k + 2 : ℤ) := by
        rw [Int.ceil_eq_iff]
        push_cast
        constructor <;> linarith
      rw [hceil]
      push_cast
      field_simp
  -- The integral over the `k`-th piece.
  have hint : ∀ k : ℕ,
      ∫ x in s k, f x = (n : ℝ) ^ 2 / 2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
    intro k
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hk2 : (0 : ℝ) < k + 2 := by positivity
    rw [setIntegral_congr_fun measurableSet_Ioc (hpiece k)]
    have hle : (n : ℝ) / (k + 2) ≤ n / (k + 1) := by
      apply div_le_div_of_nonneg_left hn'.le hk1
      linarith
    rw [← intervalIntegral.integral_of_le hle]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x => ((n : ℝ) * x - (k + 1) * x ^ 2 / 2) * (k + 2))]
    · field_simp
      ring
    · intro x _
      have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
      have h1 : HasDerivAt (fun y : ℝ => (n : ℝ) * y) ((n : ℝ) * 1) x :=
        HasDerivAt.const_mul (n : ℝ) hid
      have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have h3 : HasDerivAt (fun y : ℝ => ((k : ℝ) + 1) * y ^ 2) (((k : ℝ) + 1) * (2 * x)) x :=
        HasDerivAt.const_mul _ h2
      have h4 : HasDerivAt (fun y : ℝ => ((n : ℝ) * y - ((k : ℝ) + 1) * y ^ 2 / 2) * (k + 2))
          (((n : ℝ) * 1 - ((k : ℝ) + 1) * (2 * x) / 2) * (k + 2)) x :=
        (h1.sub (h3.div_const 2)).mul_const ((k : ℝ) + 2)
      refine h4.congr_deriv ?_
      ring
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  -- The pieces cover `(0, n]`.
  have hU : (⋃ k, s k) = Set.Ioc (0 : ℝ) n := by
    ext x
    simp only [Set.mem_iUnion, hs, Set.mem_Ioc]
    constructor
    · rintro ⟨k, h1, h2⟩
      refine ⟨lt_trans (by positivity) h1, h2.trans ?_⟩
      exact div_le_self hn'.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    · rintro ⟨h0, h1⟩
      have h1' : 1 ≤ (n : ℝ) / x := by
        rw [le_div_iff₀ h0]
        linarith
      obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌊(n : ℝ) / x⌋₊ = m + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by
          have := Nat.floor_pos.mpr h1'
          omega)
      refine ⟨m, ?_, ?_⟩
      · have := Nat.lt_floor_add_one ((n : ℝ) / x)
        rw [hm] at this
        push_cast at this
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ h0] at this
        linarith
      · have := Nat.floor_le (show 0 ≤ (n : ℝ) / x by positivity)
        rw [hm] at this
        push_cast at this
        rw [le_div_iff₀ (by positivity)]
        rw [le_div_iff₀ h0] at this
        linarith
  -- The pieces are pairwise disjoint.
  have hd : Pairwise (Function.onFun Disjoint s) := by
    have key : ∀ i j : ℕ, i < j → Disjoint (s i) (s j) := by
      intro i j hij
      rw [Set.disjoint_left]
      rintro x ⟨hx1, _⟩ ⟨_, hx2⟩
      have hij' : (i : ℝ) + 2 ≤ j + 1 := by exact_mod_cast (by omega : i + 2 ≤ j + 1)
      have : (n : ℝ) / (j + 1) ≤ n / (i + 2) :=
        div_le_div_of_nonneg_left hn'.le (by positivity) hij'
      linarith
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  -- The integrand is integrable on `(0, n]`.
  have hfi : IntegrableOn f (⋃ k, s k) := by
    rw [hU]
    refine Measure.integrableOn_of_bounded (M := 2 * n) measure_Ioc_lt_top.ne ?_ ?_
    · apply Measurable.aestronglyMeasurable
      have hdiv : Measurable fun x : ℝ => (n : ℝ) / x := measurable_const.div measurable_id
      exact (measurable_id.mul hdiv.fract).mul (measurable_from_top.comp hdiv.ceil)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      obtain ⟨hx0, hxn⟩ := hx
      have hq : 0 ≤ (n : ℝ) / x := by positivity
      have hfr0 : 0 ≤ Int.fract ((n : ℝ) / x) := Int.fract_nonneg _
      have hfr1 : Int.fract ((n : ℝ) / x) ≤ 1 := (Int.fract_lt_one _).le
      have hc0 : (0 : ℝ) ≤ (Int.ceil ((n : ℝ) / x) : ℝ) := by
        exact_mod_cast Int.ceil_nonneg hq
      have hc1 : (Int.ceil ((n : ℝ) / x) : ℝ) ≤ n / x + 1 := (Int.ceil_lt_add_one _).le
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc x * Int.fract ((n : ℝ) / x) * (Int.ceil ((n : ℝ) / x) : ℝ)
          ≤ x * 1 * (n / x + 1) := by gcongr
        _ = n + x := by field_simp
        _ ≤ 2 * n := by linarith
  -- Sum the pieces.
  have hsum1 := hasSum_integral_iUnion (s := s) (fun k => measurableSet_Ioc) hd hfi
  rw [hU] at hsum1
  simp_rw [hint] at hsum1
  have hsum2 : HasSum (fun k : ℕ => (n : ℝ) ^ 2 / 2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)))
      ((n : ℝ) ^ 2 / 2) := by
    have h : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) 1 := by
      rw [hasSum_iff_tendsto_nat_of_nonneg]
      · have hpart : ∀ m : ℕ,
            ∑ i ∈ Finset.range m, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2))
              = 1 - 1 / ((m : ℝ) + 1) := by
          intro m
          induction m with
          | zero => simp
          | succ m ih =>
            rw [Finset.sum_range_succ, ih]
            push_cast
            field_simp
            ring
        simp_rw [hpart]
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      · intro i
        rw [sub_nonneg]
        apply one_div_le_one_div_of_le <;> linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    simpa using h.mul_left ((n : ℝ) ^ 2 / 2)
  rw [intervalIntegral.integral_of_le hn'.le]
  exact hsum1.unique hsum2
```
