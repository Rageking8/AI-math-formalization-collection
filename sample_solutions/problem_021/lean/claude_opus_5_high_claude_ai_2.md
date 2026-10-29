# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `12 August 2026`\
Line count: `309`\
Turn count: `3`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

open MeasureTheory Set Filter Topology

set_option maxHeartbeats 1000000

/-!
# `∫₀ⁿ x * fract (n/x) * ⌈n/x⌉ dx = n²/2`

## Structure

Write `N = (n : ℝ) > 0` and `S k = Ioc (N/(k+2)) (N/(k+1))` for `k : ℕ`.

* `block_eq`      : on `S k` the integrand equals the affine map `(k+2)*N - (k+2)*(k+1)*x`.
                    This holds at *every* point of `S k`, including the right endpoint,
                    where `fract = 0` makes both sides vanish — so no null set is needed.
* `iUnion_blocks` : `⋃ k, S k = Ioc 0 N`.
* `blocks_disjoint`
* `integrableOn_f`: `|f| ≤ 2N` on `Ioc 0 N`, which has finite measure.
* `block_integral`: `∫_{S k} f = N²/2 * (1/((k+1)(k+2)))`.
* `hasSum_telescope` : `∑' k, 1/((k+1)(k+2)) = 1`.

`MeasureTheory.integral_iUnion` then turns the integral into the telescoping series.
-/

namespace FractCeil

/-! ### The pointwise identity on a block -/

theorem block_eq (N : ℝ) (hN : 0 < N) (k : ℕ) {x : ℝ}
    (hx : x ∈ Ioc (N / ((k : ℝ) + 2)) (N / ((k : ℝ) + 1))) :
    x * Int.fract (N / x) * (⌈N / x⌉ : ℝ)
      = ((k : ℝ) + 2) * N - (((k : ℝ) + 2) * ((k : ℝ) + 1)) * x := by
  obtain ⟨h1, h2⟩ := hx
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hk1' : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hk1
  have hk2' : ((k : ℝ) + 2) ≠ 0 := ne_of_gt hk2
  have hx0 : 0 < x := lt_trans (div_pos hN hk2) h1
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hxx : x * (N / x) = N := by field_simp
  -- `k + 1 ≤ N / x`
  have hlb : (k : ℝ) + 1 ≤ N / x := by
    have hcancel : ((k : ℝ) + 1) * (N / ((k : ℝ) + 1)) = N := by field_simp
    have hkey : ((k : ℝ) + 1) * x ≤ N := by
      have h := mul_le_mul_of_nonneg_left h2 hk1.le
      rwa [hcancel] at h
    rw [← sub_nonneg]
    have he : N / x - ((k : ℝ) + 1) = (N - ((k : ℝ) + 1) * x) / x := by field_simp
    rw [he]
    exact div_nonneg (by linarith) hx0.le
  -- `N / x < k + 2`
  have hub : N / x < (k : ℝ) + 2 := by
    have hcancel : ((k : ℝ) + 2) * (N / ((k : ℝ) + 2)) = N := by field_simp
    have hkey : N < ((k : ℝ) + 2) * x := by
      have h := mul_lt_mul_of_pos_left h1 hk2
      rwa [hcancel] at h
    rw [← sub_pos]
    have he : ((k : ℝ) + 2) - N / x = (((k : ℝ) + 2) * x - N) / x := by field_simp
    rw [he]
    exact div_pos (by linarith) hx0
  -- hence `⌊N/x⌋ = k + 1` and `fract (N/x) = N/x - (k+1)`
  have hfloor : ⌊N / x⌋ = (k : ℤ) + 1 := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩ <;> push_cast <;> linarith
  have hfr : Int.fract (N / x) = N / x - ((k : ℝ) + 1) := by
    have h : Int.fract (N / x) = N / x - (⌊N / x⌋ : ℝ) := rfl
    rw [hfloor] at h
    push_cast at h
    linarith
  rcases eq_or_lt_of_le hlb with heq | hlt
  · -- right endpoint: `N/x = k+1`, so `fract = 0` and both sides are `0`
    have hNx : N = ((k : ℝ) + 1) * x := (div_eq_iff hxne).1 heq.symm
    have hfract0 : Int.fract (N / x) = 0 := by rw [hfr, ← heq]; ring
    rw [hfract0]
    linear_combination (-((k : ℝ) + 2)) * hNx
  · -- interior: `⌈N/x⌉ = k + 2`
    have hceil : ⌈N / x⌉ = (k : ℤ) + 2 := by
      rw [Int.ceil_eq_iff]
      refine ⟨?_, ?_⟩ <;> push_cast <;> linarith
    rw [hfr, hceil]
    push_cast
    linear_combination ((k : ℝ) + 2) * hxx

/-! ### The blocks cover `Ioc 0 N` and are pairwise disjoint -/

theorem iUnion_blocks (N : ℝ) (hN : 0 < N) :
    (⋃ k : ℕ, Ioc (N / ((k : ℝ) + 2)) (N / ((k : ℝ) + 1))) = Ioc 0 N := by
  ext x
  simp only [mem_iUnion, mem_Ioc]
  constructor
  · rintro ⟨k, h1, h2⟩
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    refine ⟨lt_trans (div_pos hN hk2) h1, ?_⟩
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have : N / ((k : ℝ) + 1) ≤ N := div_le_self hN.le (by linarith)
    linarith
  · rintro ⟨hx0, hxN⟩
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hcx : (N / x) * x = N := by field_simp
    have hNx1 : (1 : ℝ) ≤ N / x := by
      rw [← sub_nonneg]
      have he : N / x - 1 = (N - x) / x := by field_simp
      rw [he]
      exact div_nonneg (by linarith) hx0.le
    set j : ℕ := ⌊N / x⌋₊ with hjdef
    have hj1 : 1 ≤ j := Nat.le_floor (by simpa using hNx1)
    have hj0 : (0 : ℝ) < (j : ℝ) := by
      have hjpos : 0 < j := hj1
      exact_mod_cast hjpos
    have hfl : (j : ℝ) ≤ N / x := Nat.floor_le (by positivity)
    have hfu : N / x < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hcast1 : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
      rw [Nat.cast_sub hj1]; push_cast; ring
    have hcast2 : ((j - 1 : ℕ) : ℝ) + 2 = (j : ℝ) + 1 := by
      rw [Nat.cast_sub hj1]; push_cast; ring
    refine ⟨j - 1, ?_, ?_⟩
    · -- `N / (j+1) < x`
      rw [hcast2, ← sub_pos]
      have hkey : N < ((j : ℝ) + 1) * x := by
        have h := mul_lt_mul_of_pos_right hfu hx0
        rwa [hcx] at h
      have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
      have he : x - N / ((j : ℝ) + 1) = (((j : ℝ) + 1) * x - N) / ((j : ℝ) + 1) := by
        field_simp
      rw [he]
      exact div_pos (by linarith) (by positivity)
    · -- `x ≤ N / j`
      rw [hcast1, ← sub_nonneg]
      have hkey : (j : ℝ) * x ≤ N := by
        have h := mul_le_mul_of_nonneg_right hfl hx0.le
        rwa [hcx] at h
      have hne : (j : ℝ) ≠ 0 := ne_of_gt hj0
      have he : N / (j : ℝ) - x = (N - (j : ℝ) * x) / (j : ℝ) := by field_simp
      rw [he]
      exact div_nonneg (by linarith) hj0.le

theorem blocks_disjoint (N : ℝ) (hN : 0 < N) :
    Pairwise (Function.onFun Disjoint
      (fun k : ℕ => Ioc (N / ((k : ℝ) + 2)) (N / ((k : ℝ) + 1)))) := by
  have mono : ∀ a b : ℕ, a < b → N / ((b : ℝ) + 1) ≤ N / ((a : ℝ) + 2) := by
    intro a b hab
    have h1 : ((a : ℝ) + 2) ≠ 0 := by positivity
    have h2 : ((b : ℝ) + 1) ≠ 0 := by positivity
    have hle : (a : ℝ) + 2 ≤ (b : ℝ) + 1 := by
      have : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
    rw [← sub_nonneg]
    have he : N / ((a : ℝ) + 2) - N / ((b : ℝ) + 1)
        = (N * (((b : ℝ) + 1) - ((a : ℝ) + 2))) / (((a : ℝ) + 2) * ((b : ℝ) + 1)) := by
      first
        | (field_simp; ring)
        | field_simp
        | (rw [div_sub_div _ _ h1 h2]; ring)
    rw [he]
    exact div_nonneg (mul_nonneg hN.le (by linarith)) (by positivity)
  intro k l hkl
  simp only [Function.onFun, Set.disjoint_left, mem_Ioc]
  rintro x ⟨h1, h2⟩ ⟨h3, h4⟩
  rcases lt_or_gt_of_ne hkl with h | h
  · linarith [mono k l h]
  · linarith [mono l k h]

/-! ### Integrability -/

theorem measurable_f (N : ℝ) :
    Measurable (fun x : ℝ => x * Int.fract (N / x) * (⌈N / x⌉ : ℝ)) := by
  have h1 : Measurable (fun x : ℝ => N / x) := measurable_const.div measurable_id
  have hZ : Measurable (fun z : ℤ => (z : ℝ)) := by
    first
      | exact measurable_of_countable _
      | exact measurable_from_top
      | measurability
      | fun_prop
  have h2 : Measurable (fun x : ℝ => Int.fract (N / x)) := by
    first
      | exact measurable_fract.comp h1
      | exact Int.measurable_fract.comp h1
      | exact h1.sub (hZ.comp (Int.measurable_floor.comp h1))
      | exact h1.sub (hZ.comp (measurable_floor.comp h1))
      | measurability
      | fun_prop
  have h3 : Measurable (fun x : ℝ => ((⌈N / x⌉ : ℤ) : ℝ)) := by
    first
      | exact hZ.comp (Int.measurable_ceil.comp h1)
      | exact hZ.comp (measurable_ceil.comp h1)
      | measurability
      | fun_prop
  exact (measurable_id.mul h2).mul h3

theorem integrableOn_f (N : ℝ) (hN : 0 < N) :
    IntegrableOn (fun x : ℝ => x * Int.fract (N / x) * (⌈N / x⌉ : ℝ)) (Ioc 0 N) := by
  haveI hfin : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) N)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hconst : IntegrableOn (fun _ : ℝ => 2 * N) (Ioc 0 N) volume := integrable_const _
  refine hconst.mono' (measurable_f N).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  obtain ⟨hx0, hxN⟩ := hx
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hfr0 : 0 ≤ Int.fract (N / x) := Int.fract_nonneg _
  have hfr1 : Int.fract (N / x) < 1 := Int.fract_lt_one _
  have hc0 : (0 : ℝ) ≤ (⌈N / x⌉ : ℝ) := by
    exact_mod_cast Int.ceil_nonneg (le_of_lt (div_pos hN hx0))
  have hc1 : (⌈N / x⌉ : ℝ) < N / x + 1 := Int.ceil_lt_add_one _
  have hnn : 0 ≤ x * Int.fract (N / x) * (⌈N / x⌉ : ℝ) :=
    mul_nonneg (mul_nonneg hx0.le hfr0) hc0
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have step : x * Int.fract (N / x) * (⌈N / x⌉ : ℝ) ≤ x * 1 * (N / x + 1) := by
    refine mul_le_mul ?_ hc1.le hc0 (by positivity)
    exact mul_le_mul_of_nonneg_left hfr1.le hx0.le
  have hval : x * 1 * (N / x + 1) = N + x := by field_simp
  rw [hval] at step
  linarith

/-! ### The integral over one block -/

theorem affine_integral (C D a b : ℝ) :
    (∫ x in a..b, (C - D * x)) = C * (b - a) - D * ((b ^ 2 - a ^ 2) / 2) := by
  have h1 : IntervalIntegrable (fun _ : ℝ => C) volume a b := intervalIntegrable_const
  have h2 : IntervalIntegrable (fun x : ℝ => D * x) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  have hid : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 := by
    first
      | exact integral_id
      | exact intervalIntegral.integral_id
      | simp
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, hid]
  simp only [smul_eq_mul]
  ring

theorem block_integral (N : ℝ) (hN : 0 < N) (k : ℕ) :
    (∫ x in Ioc (N / ((k : ℝ) + 2)) (N / ((k : ℝ) + 1)),
        x * Int.fract (N / x) * (⌈N / x⌉ : ℝ))
      = N ^ 2 / 2 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hk1' : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hk1
  have hk2' : ((k : ℝ) + 2) ≠ 0 := ne_of_gt hk2
  have hab : N / ((k : ℝ) + 2) ≤ N / ((k : ℝ) + 1) := by
    rw [← sub_nonneg]
    have he : N / ((k : ℝ) + 1) - N / ((k : ℝ) + 2)
        = N / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by field_simp; ring
    rw [he]
    exact div_nonneg hN.le (by positivity)
  have hcong :
      (∫ x in Ioc (N / ((k : ℝ) + 2)) (N / ((k : ℝ) + 1)),
          x * Int.fract (N / x) * (⌈N / x⌉ : ℝ))
        = ∫ x in Ioc (N / ((k : ℝ) + 2)) (N / ((k : ℝ) + 1)),
            (((k : ℝ) + 2) * N - (((k : ℝ) + 2) * ((k : ℝ) + 1)) * x) := by
    first
      | exact setIntegral_congr_fun measurableSet_Ioc (fun x hx => block_eq N hN k hx)
      | exact set_integral_congr measurableSet_Ioc (fun x hx => block_eq N hN k hx)
      | exact setIntegral_congr measurableSet_Ioc (fun x hx => block_eq N hN k hx)
  rw [hcong, ← intervalIntegral.integral_of_le hab, affine_integral]
  field_simp
  ring

/-! ### The telescoping series -/

theorem hasSum_telescope :
    HasSum (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) 1 := by
  have hpart : ∀ m : ℕ,
      (∑ k ∈ Finset.range m, (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2)))
        = 1 - 1 / ((m : ℝ) + 1) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
        have h2 : ((m : ℝ) + 2) ≠ 0 := by positivity
        push_cast
        field_simp
        ring
  have hsummable : Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
    refine summable_of_sum_range_le (c := 1) (fun n => by positivity) (fun m => ?_)
    rw [hpart m]
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  rw [hsummable.hasSum_iff_tendsto_nat]
  simp only [hpart]
  have hlim : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (nhds 0) := by
    first
      | exact tendsto_one_div_add_atTop_nhds_zero_nat
      | exact tendsto_one_div_add_atTop_nhds_0_nat
  simpa using tendsto_const_nhds.sub hlim

end FractCeil

/-! ### The theorem -/

open FractCeil in
theorem integral_fract_ceil (n : ℕ) (hn : 0 < n) :
    ∫ x in (0 : ℝ)..(n : ℝ),
      x * Int.fract ((n : ℝ) / x) * (Int.ceil ((n : ℝ) / x) : ℝ) = ((n : ℝ) ^ 2) / 2 := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsplit :=
    MeasureTheory.integral_iUnion (μ := volume)
      (s := fun k : ℕ => Ioc ((n : ℝ) / ((k : ℝ) + 2)) ((n : ℝ) / ((k : ℝ) + 1)))
      (f := fun x : ℝ => x * Int.fract ((n : ℝ) / x) * (⌈(n : ℝ) / x⌉ : ℝ))
      (fun _ => measurableSet_Ioc) (blocks_disjoint (n : ℝ) hN)
      (by rw [iUnion_blocks (n : ℝ) hN]; exact integrableOn_f (n : ℝ) hN)
  rw [iUnion_blocks (n : ℝ) hN] at hsplit
  rw [intervalIntegral.integral_of_le hN.le, hsplit,
    tsum_congr (block_integral (n : ℝ) hN),
    (hasSum_telescope.mul_left ((n : ℝ) ^ 2 / 2)).tsum_eq, mul_one]
```
