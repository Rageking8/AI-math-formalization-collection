# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `3 August 2026`\
Line count: `259`\
Turn count: `1`

## Note

The conversation contained 2 "Continue" messages not included in the turn count.

## Solution

```lean4
import Mathlib

open Real Filter Finset

theorem sum_n_arctan_eq_pi :
    tsum (fun (n : ℤ) => (n : ℝ) * Real.arctan ((4 * (n : ℝ) + 2) /
      (4 * (n : ℝ) ^ 4 + 8 * (n : ℝ) ^ 3 + 4 * (n : ℝ) ^ 2 + 1))) = Real.pi := by
  -- ## Basic arctan facts
  have arctan_sub' : ∀ a b : ℝ, -1 < a * b →
      Real.arctan a - Real.arctan b = Real.arctan ((a - b) / (1 + a * b)) := by
    intro a b h
    have h' : a * (-b) < 1 := by nlinarith
    have key := Real.arctan_add h'
    rw [Real.arctan_neg] at key
    rw [sub_eq_add_neg, key]
    congr 1
    ring
  have arctan_nonneg' : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.arctan x := by
    intro x hx
    first
      | exact Real.arctan_nonneg.mpr hx
      | simpa using hx
      | (rw [← Real.arctan_zero]; exact Real.arctan_le_arctan hx)
      | (rw [← Real.arctan_zero]; exact Real.monotone_arctan hx)
      | (rw [← Real.arctan_zero]; exact Real.arctan_strictMono.monotone hx)
      | (rw [← Real.arctan_zero]; gcongr)
  have arctan_le : ∀ x : ℝ, 0 ≤ x → Real.arctan x ≤ x := by
    intro x hx
    rcases eq_or_lt_of_le hx with h | h
    · rw [← h]; simp
    · have h1 : 0 < Real.arctan x := by
        first
          | exact Real.arctan_pos.mpr h
          | simpa using h
          | (rw [← Real.arctan_zero]; exact Real.arctan_lt_arctan h)
          | (rw [← Real.arctan_zero]; exact Real.arctan_strictMono h)
          | (rw [← Real.arctan_zero]; gcongr)
      have h2 : Real.arctan x < Real.pi / 2 := Real.arctan_lt_pi_div_two x
      have h3 : Real.arctan x < Real.tan (Real.arctan x) := by
        first
          | exact Real.lt_tan h1 h2
          | exact Real.lt_tan _ h1 h2
      rw [Real.tan_arctan] at h3
      exact le_of_lt h3
  -- ## arctan 2 + arctan (1/2) = π/2
  have hA1 : Real.arctan 1 + Real.arctan (1/3) = Real.arctan 2 := by
    rw [Real.arctan_add (show (1:ℝ) * (1/3) < 1 by norm_num)]
    norm_num
  have hA2 : Real.arctan (1/3) + Real.arctan (1/2) = Real.arctan 1 := by
    rw [Real.arctan_add (show ((1:ℝ)/3) * (1/2) < 1 by norm_num)]
    norm_num
  have harctan2 : Real.arctan 2 + Real.arctan (1/2) = Real.pi/2 := by
    have h1 := Real.arctan_one
    linarith [hA1, hA2]
  -- ## The two key telescoping identities
  have term_eq : ∀ x : ℝ, 0 < x →
      Real.arctan ((4*x+2)/(4*x^4+8*x^3+4*x^2+1))
        = Real.arctan (1/(2*x^2)) - Real.arctan (1/(2*(x+1)^2)) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hx1 : x + 1 ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < x + 1)
    have hd : (0:ℝ) < 4*x^4+8*x^3+4*x^2+1 := by nlinarith [sq_nonneg (x*(x+1))]
    have hd' : (4:ℝ)*x^4+8*x^3+4*x^2+1 ≠ 0 := ne_of_gt hd
    have hp : (0:ℝ) ≤ (1/(2*x^2)) * (1/(2*(x+1)^2)) := by positivity
    have hden : (1:ℝ) + (1/(2*x^2)) * (1/(2*(x+1)^2)) ≠ 0 := by positivity
    rw [arctan_sub' (1/(2*x^2)) (1/(2*(x+1)^2)) (by linarith)]
    congr 1
    first
      | (field_simp; ring)
      | field_simp
  have split_eq : ∀ x : ℝ, 0 ≤ x →
      Real.arctan (1/(2*(x+1)^2))
        = Real.arctan (1/(2*x+1)) - Real.arctan (1/(2*(x+1)+1)) := by
    intro x hx
    have h1 : (0:ℝ) < 2*x+1 := by linarith
    have h2 : (0:ℝ) < 2*(x+1)+1 := by linarith
    have h1' : (2:ℝ)*x+1 ≠ 0 := ne_of_gt h1
    have h2' : (2:ℝ)*(x+1)+1 ≠ 0 := ne_of_gt h2
    have hx1 : x + 1 ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < x+1)
    have hp : (0:ℝ) ≤ (1/(2*x+1)) * (1/(2*(x+1)+1)) :=
      le_of_lt (mul_pos (one_div_pos.mpr h1) (one_div_pos.mpr h2))
    have hden : (1:ℝ) + (1/(2*x+1)) * (1/(2*(x+1)+1)) ≠ 0 := ne_of_gt (by linarith)
    rw [arctan_sub' (1/(2*x+1)) (1/(2*(x+1)+1)) (by linarith)]
    congr 1
    first
      | (field_simp; ring)
      | field_simp
  -- ## Closed forms for the partial sums
  have hA : ∀ M : ℕ, (∑ n ∈ Finset.range (M+1),
      ((n:ℝ) * Real.arctan ((4*(n:ℝ)+2)/(4*(n:ℝ)^4+8*(n:ℝ)^3+4*(n:ℝ)^2+1))))
      = Real.pi/4 - Real.arctan (1/(2*(M:ℝ)+1))
        - (M:ℝ) * Real.arctan (1/(2*((M:ℝ)+1)^2)) := by
    intro M
    induction M with
    | zero =>
      first
        | norm_num [Real.arctan_one]
        | simp [Real.arctan_one]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have e1 := term_eq ((k:ℝ)+1) (by positivity)
      have e2 := split_eq (k:ℝ) (by positivity)
      push_cast
      rw [e1, e2]
      ring
  have hB : ∀ M : ℕ, (∑ n ∈ Finset.range (M+1),
      (((n:ℝ)+1) * Real.arctan ((4*(n:ℝ)+2)/(4*(n:ℝ)^4+8*(n:ℝ)^3+4*(n:ℝ)^2+1))))
      = 3*Real.pi/4 - Real.arctan (1/(2*(M:ℝ)+1))
        - ((M:ℝ)+1) * Real.arctan (1/(2*((M:ℝ)+1)^2)) := by
    intro M
    induction M with
    | zero =>
      have h2 := harctan2
      first
        | (norm_num at h2 ⊢; linarith [Real.arctan_one])
        | (norm_num at h2 ⊢)
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have e1 := term_eq ((k:ℝ)+1) (by positivity)
      have e2 := split_eq (k:ℝ) (by positivity)
      push_cast
      rw [e1, e2]
      ring
  -- ## Limits
  have hinv : Filter.Tendsto (fun M : ℕ => 1/(M:ℝ)) Filter.atTop (nhds 0) := by
    first
      | exact tendsto_one_div_atTop_nhds_zero_nat
      | exact tendsto_one_div_atTop_nhds_0_nat
      | simpa [one_div] using tendsto_inverse_atTop_nhds_zero_nat
      | simpa [one_div] using tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have lim1 : Filter.Tendsto (fun M : ℕ => Real.arctan (1/(2*(M:ℝ)+1)))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hinv
    · filter_upwards with M
      exact arctan_nonneg' _ (by positivity)
    · filter_upwards [Filter.eventually_ge_atTop 1] with M hM
      have hM' : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
      have hb : Real.arctan (1/(2*(M:ℝ)+1)) ≤ 1/(2*(M:ℝ)+1) := arctan_le _ (by positivity)
      have h2 : 1/(2*(M:ℝ)+1) ≤ 1/(M:ℝ) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      linarith
  have lim2 : Filter.Tendsto (fun M : ℕ => ((M:ℝ)+1) * Real.arctan (1/(2*((M:ℝ)+1)^2)))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hinv
    · filter_upwards with M
      exact mul_nonneg (by positivity) (arctan_nonneg' _ (by positivity))
    · filter_upwards [Filter.eventually_ge_atTop 1] with M hM
      have hM' : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
      have hne : ((M:ℝ)+1) ≠ 0 := by positivity
      have hb : Real.arctan (1/(2*((M:ℝ)+1)^2)) ≤ 1/(2*((M:ℝ)+1)^2) :=
        arctan_le _ (by positivity)
      have hmul : ((M:ℝ)+1) * Real.arctan (1/(2*((M:ℝ)+1)^2))
          ≤ ((M:ℝ)+1) * (1/(2*((M:ℝ)+1)^2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      have heq : ((M:ℝ)+1) * (1/(2*((M:ℝ)+1)^2)) = 1/(2*((M:ℝ)+1)) := by
        first
          | (field_simp; ring)
          | field_simp
      rw [heq] at hmul
      have hfin : 1/(2*((M:ℝ)+1)) ≤ 1/(M:ℝ) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      linarith
  have lim3 : Filter.Tendsto (fun M : ℕ => (M:ℝ) * Real.arctan (1/(2*((M:ℝ)+1)^2)))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ lim2
    · filter_upwards with M
      exact mul_nonneg (by positivity) (arctan_nonneg' _ (by positivity))
    · filter_upwards with M
      have hA0 := arctan_nonneg' (1/(2*((M:ℝ)+1)^2)) (by positivity)
      have hM0 : (0:ℝ) ≤ (M:ℝ) := by positivity
      nlinarith [hA0, hM0]
  -- ## Summability and HasSum for the two halves
  have hfp_nonneg : ∀ n : ℕ,
      0 ≤ (n:ℝ) * Real.arctan ((4*(n:ℝ)+2)/(4*(n:ℝ)^4+8*(n:ℝ)^3+4*(n:ℝ)^2+1)) := by
    intro n
    exact mul_nonneg (by positivity) (arctan_nonneg' _ (by positivity))
  have hfn_nonneg : ∀ n : ℕ,
      0 ≤ ((n:ℝ)+1) * Real.arctan ((4*(n:ℝ)+2)/(4*(n:ℝ)^4+8*(n:ℝ)^3+4*(n:ℝ)^2+1)) := by
    intro n
    exact mul_nonneg (by positivity) (arctan_nonneg' _ (by positivity))
  have hbdp : ∀ N : ℕ, (∑ i ∈ Finset.range N,
      ((i:ℝ) * Real.arctan ((4*(i:ℝ)+2)/(4*(i:ℝ)^4+8*(i:ℝ)^3+4*(i:ℝ)^2+1)))) ≤ Real.pi/4 := by
    intro N
    cases N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      linarith [Real.pi_pos]
    | succ k =>
      rw [hA k]
      have h1 : 0 ≤ Real.arctan (1/(2*(k:ℝ)+1)) := arctan_nonneg' _ (by positivity)
      have h2 : 0 ≤ (k:ℝ) * Real.arctan (1/(2*((k:ℝ)+1)^2)) :=
        mul_nonneg (by positivity) (arctan_nonneg' _ (by positivity))
      linarith
  have hbdn : ∀ N : ℕ, (∑ i ∈ Finset.range N,
      (((i:ℝ)+1) * Real.arctan ((4*(i:ℝ)+2)/(4*(i:ℝ)^4+8*(i:ℝ)^3+4*(i:ℝ)^2+1))))
        ≤ 3*Real.pi/4 := by
    intro N
    cases N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      linarith [Real.pi_pos]
    | succ k =>
      rw [hB k]
      have h1 : 0 ≤ Real.arctan (1/(2*(k:ℝ)+1)) := arctan_nonneg' _ (by positivity)
      have h2 : 0 ≤ ((k:ℝ)+1) * Real.arctan (1/(2*((k:ℝ)+1)^2)) :=
        mul_nonneg (by positivity) (arctan_nonneg' _ (by positivity))
      linarith
  have hsump : Summable (fun n : ℕ =>
      (n:ℝ) * Real.arctan ((4*(n:ℝ)+2)/(4*(n:ℝ)^4+8*(n:ℝ)^3+4*(n:ℝ)^2+1))) :=
    summable_of_sum_range_le hfp_nonneg hbdp
  have hsumn : Summable (fun n : ℕ =>
      ((n:ℝ)+1) * Real.arctan ((4*(n:ℝ)+2)/(4*(n:ℝ)^4+8*(n:ℝ)^3+4*(n:ℝ)^2+1))) :=
    summable_of_sum_range_le hfn_nonneg hbdn
  have hasp : HasSum (fun n : ℕ =>
      (n:ℝ) * Real.arctan ((4*(n:ℝ)+2)/(4*(n:ℝ)^4+8*(n:ℝ)^3+4*(n:ℝ)^2+1))) (Real.pi/4) := by
    rw [hsump.hasSum_iff_tendsto_nat, ← Filter.tendsto_add_atTop_iff_nat 1]
    simp only [hA]
    have h : Filter.Tendsto (fun M : ℕ => Real.pi/4 - Real.arctan (1/(2*(M:ℝ)+1))
        - (M:ℝ) * Real.arctan (1/(2*((M:ℝ)+1)^2)))
        Filter.atTop (nhds (Real.pi/4 - 0 - 0)) :=
      ((tendsto_const_nhds).sub lim1).sub lim3
    simpa using h
  have hasn : HasSum (fun n : ℕ =>
      ((n:ℝ)+1) * Real.arctan ((4*(n:ℝ)+2)/(4*(n:ℝ)^4+8*(n:ℝ)^3+4*(n:ℝ)^2+1)))
      (3*Real.pi/4) := by
    rw [hsumn.hasSum_iff_tendsto_nat, ← Filter.tendsto_add_atTop_iff_nat 1]
    simp only [hB]
    have h : Filter.Tendsto (fun M : ℕ => 3*Real.pi/4 - Real.arctan (1/(2*(M:ℝ)+1))
        - ((M:ℝ)+1) * Real.arctan (1/(2*((M:ℝ)+1)^2)))
        Filter.atTop (nhds (3*Real.pi/4 - 0 - 0)) :=
      ((tendsto_const_nhds).sub lim1).sub lim2
    simpa using h
  -- ## Transfer to the ℤ-indexed family
  have hpos_term : ∀ x y : ℝ, y = x →
      y * Real.arctan ((4*y+2)/(4*y^4+8*y^3+4*y^2+1))
        = x * Real.arctan ((4*x+2)/(4*x^4+8*x^3+4*x^2+1)) := by
    intro x y h; rw [h]
  have hneg_term : ∀ x y : ℝ, y = -x - 1 →
      y * Real.arctan ((4*y+2)/(4*y^4+8*y^3+4*y^2+1))
        = (x+1) * Real.arctan ((4*x+2)/(4*x^4+8*x^3+4*x^2+1)) := by
    intro x y hy
    subst hy
    rw [show (4:ℝ)*(-x-1)^4+8*(-x-1)^3+4*(-x-1)^2+1 = 4*x^4+8*x^3+4*x^2+1 by ring,
        show (4:ℝ)*(-x-1)+2 = -(4*x+2) by ring, neg_div, Real.arctan_neg]
    ring
  have hcongr : ∀ (f g : ℕ → ℝ) (a : ℝ), (∀ n, f n = g n) → HasSum g a → HasSum f a := by
    intro f g a h hg
    have hfg : f = g := funext h
    rw [hfg]; exact hg
  have main : HasSum (fun (n : ℤ) => (n : ℝ) * Real.arctan ((4 * (n : ℝ) + 2) /
      (4 * (n : ℝ) ^ 4 + 8 * (n : ℝ) ^ 3 + 4 * (n : ℝ) ^ 2 + 1))) Real.pi := by
    have hkey : Real.pi = Real.pi/4 + 3*Real.pi/4 := by ring
    rw [hkey]
    first
      | apply HasSum.of_nat_of_neg_add_one
      | apply HasSum.nonneg_add_neg
    · exact hcongr _ _ _ (fun n => hpos_term (n:ℝ) _ (by push_cast; try ring)) hasp
    · exact hcongr _ _ _ (fun n => hneg_term (n:ℝ) _ (by push_cast; try ring)) hasn
  exact main.tsum_eq
```
