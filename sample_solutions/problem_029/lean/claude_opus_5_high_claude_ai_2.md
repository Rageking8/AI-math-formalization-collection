# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `18 August 2026`\
Line count: `178`\
Turn count: `4`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

open Real Filter Topology Finset

/-! ## Auxiliary facts about `arctan` -/

private lemma arctan_nonneg' {x : ℝ} (hx : 0 ≤ x) : arctan x ≥ 0 := by
  rw [Real.arctan_eq_arcsin]
  exact Real.arcsin_nonneg.2 (div_nonneg hx (Real.sqrt_nonneg _))

private lemma arctan_le_self {x : ℝ} (hx : 0 ≤ x) : arctan x ≤ x := by
  rcases hx.eq_or_lt with h | h
  · simp [← h]
  · have h0 : 0 < arctan x := by
      rw [Real.arctan_eq_arcsin]
      exact Real.arcsin_pos.2 (div_pos h (Real.sqrt_pos.2 (by positivity)))
    have h1 := Real.lt_tan h0 (Real.arctan_lt_pi_div_two x)
    rw [Real.tan_arctan] at h1
    exact h1.le

/-- The summand is a difference of two arctans — no case split, valid for all reals. -/
private lemma key (x : ℝ) :
    arctan (2 * (x + 1) ^ 2) - arctan (2 * x ^ 2)
      = arctan ((4 * x + 2) / (4 * x ^ 4 + 8 * x ^ 3 + 4 * x ^ 2 + 1)) := by
  have h  : 2 * (x + 1) ^ 2 * -(2 * x ^ 2) < 1 := by nlinarith [sq_nonneg (x * (x + 1))]
  have hd : (0:ℝ) < 1 - 2 * (x + 1) ^ 2 * -(2 * x ^ 2) := by nlinarith [sq_nonneg (x * (x + 1))]
  have hd' : (0:ℝ) < 4 * x ^ 4 + 8 * x ^ 3 + 4 * x ^ 2 + 1 := by nlinarith [sq_nonneg (x * (x + 1))]
  have h2 := Real.arctan_add h
  rw [Real.arctan_neg, ← sub_eq_add_neg] at h2
  rw [h2]
  congr 1
  rw [div_eq_div_iff hd.ne' hd'.ne']
  ring

/-- Telescoping identity for the tails: `arctan (1/(2n+1))` decreases by exactly `g (n+1)`. -/
private lemma step (n : ℕ) :
    arctan (1 / (2 * (n : ℝ) + 1)) - arctan (1 / (2 * ((n : ℝ) + 1) + 1))
      = π / 2 - arctan (2 * ((n : ℝ) + 1) ^ 2) := by
  have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp : (0:ℝ) < 2 * ((n : ℝ) + 1) ^ 2 := by positivity
  have hA : (2 * ((n : ℝ) + 1) ^ 2) ≠ 0 := by positivity
  have hB : (2 * ((n : ℝ) + 1) + 1) ≠ 0 := by positivity
  have hC : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hlt : (2 * ((n : ℝ) + 1) ^ 2)⁻¹ * (1 / (2 * ((n : ℝ) + 1) + 1)) < 1 := by
    have e : (2 * ((n : ℝ) + 1) ^ 2)⁻¹ * (1 / (2 * ((n : ℝ) + 1) + 1))
        = 1 / (2 * ((n : ℝ) + 1) ^ 2 * (2 * ((n : ℝ) + 1) + 1)) := by field_simp
    rw [e, div_lt_one (by positivity)]
    nlinarith
  rw [← Real.arctan_inv_of_pos hp, sub_eq_iff_eq_add, Real.arctan_add hlt]
  congr 1
  rw [div_eq_div_iff hC (by linarith : (0:ℝ) < 1 - (2 * ((n : ℝ) + 1) ^ 2)⁻¹ *
      (1 / (2 * ((n : ℝ) + 1) + 1))).ne']
  field_simp
  ring

/-- Nonnegative telescoping series over `ℕ`. -/
private lemma tele {f F : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hF : ∀ n, 0 ≤ F n)
    (h : ∀ n, f n = F n - F (n + 1)) (hl : Tendsto F atTop (𝓝 0)) : HasSum f (F 0) := by
  have hsum : ∀ N, ∑ i ∈ range N, f i = F 0 - F N := by
    intro N; simp only [h]; exact Finset.sum_range_sub' F N
  have hs : Summable f :=
    summable_of_sum_range_le hf (fun N => by rw [hsum]; linarith [hF N])
  refine hs.hasSum_iff_tendsto_nat.2 ?_
  simpa [hsum] using (tendsto_const_nhds (x := F 0) (f := atTop)).sub hl

/-- Both halves of the two-sided sum at once: `c = 0` gives `π/4`, `c = 1` gives `3π/4`. -/
private lemma main {c : ℝ} (hc : 0 ≤ c) :
    HasSum (fun n : ℕ => ((n : ℝ) + c) * arctan ((4 * (n : ℝ) + 2) /
      (4 * (n : ℝ) ^ 4 + 8 * (n : ℝ) ^ 3 + 4 * (n : ℝ) ^ 2 + 1))) (c * (π / 2) + π / 4) := by
  have hcoe : ∀ n : ℕ, (0:ℝ) ≤ (n : ℝ) + c := fun n => add_nonneg (Nat.cast_nonneg n) hc
  -- nonnegativity of the summand
  have h1 : ∀ n : ℕ, 0 ≤ ((n : ℝ) + c) * arctan ((4 * (n : ℝ) + 2) /
      (4 * (n : ℝ) ^ 4 + 8 * (n : ℝ) ^ 3 + 4 * (n : ℝ) ^ 2 + 1)) := fun n =>
    mul_nonneg (hcoe n) (arctan_nonneg' (by positivity))
  -- nonnegativity of the telescoping function
  have h2 : ∀ n : ℕ, 0 ≤ ((n : ℝ) + c) * (π / 2 - arctan (2 * (n : ℝ) ^ 2))
      + arctan (1 / (2 * (n : ℝ) + 1)) := by
    intro n
    have ha := Real.arctan_lt_pi_div_two (2 * (n : ℝ) ^ 2)
    have hb : (0:ℝ) ≤ arctan (1 / (2 * (n : ℝ) + 1)) := arctan_nonneg' (by positivity)
    nlinarith [mul_nonneg (hcoe n) (sub_pos.2 ha).le]
  -- the telescoping identity
  have h3 : ∀ n : ℕ, ((n : ℝ) + c) * arctan ((4 * (n : ℝ) + 2) /
      (4 * (n : ℝ) ^ 4 + 8 * (n : ℝ) ^ 3 + 4 * (n : ℝ) ^ 2 + 1))
      = (((n : ℝ) + c) * (π / 2 - arctan (2 * (n : ℝ) ^ 2)) + arctan (1 / (2 * (n : ℝ) + 1)))
        - ((((n : ℕ) + 1 : ℕ) + c : ℝ) * (π / 2 - arctan (2 * (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2))
          + arctan (1 / (2 * (((n : ℕ) + 1 : ℕ) : ℝ) + 1))) := by
    intro n
    push_cast
    linear_combination (-(n : ℝ) - c) * key (n : ℝ) - step n
  -- the telescoping function tends to `0`
  have h4 : Tendsto (fun n : ℕ => ((n : ℝ) + c) * (π / 2 - arctan (2 * (n : ℝ) ^ 2))
      + arctan (1 / (2 * (n : ℝ) + 1))) atTop (𝓝 0) := by
    have hA : Tendsto (fun n : ℕ => arctan (1 / (2 * (n : ℝ) + 1))) atTop (𝓝 0) := by
      have ha : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1
          (Filter.Tendsto.const_mul_atTop two_pos tendsto_natCast_atTop_atTop)
      have hb : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp ha
      simpa [Function.comp_def] using (Real.continuous_arctan.tendsto 0).comp hb
    have hB : Tendsto (fun n : ℕ => ((n : ℝ) + c) * (π / 2 - arctan (2 * (n : ℝ) ^ 2)))
        atTop (𝓝 0) := by
      have hg : Tendsto (fun n : ℕ => (1 + c) / 2 * (1 / (n : ℝ))) atTop (𝓝 0) := by
        simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul ((1 + c) / 2)
      refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hg
      · exact mul_nonneg (hcoe n)
          (by linarith [Real.arctan_lt_pi_div_two (2 * (n : ℝ) ^ 2)])
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hp : (0:ℝ) < 2 * (n : ℝ) ^ 2 := by nlinarith
        have e1 : π / 2 - arctan (2 * (n : ℝ) ^ 2) = arctan (1 / (2 * (n : ℝ) ^ 2)) := by
          rw [one_div, Real.arctan_inv_of_pos hp]
        have e2 : arctan (1 / (2 * (n : ℝ) ^ 2)) ≤ 1 / (2 * (n : ℝ) ^ 2) :=
          arctan_le_self (by positivity)
        calc ((n : ℝ) + c) * (π / 2 - arctan (2 * (n : ℝ) ^ 2))
            = ((n : ℝ) + c) * arctan (1 / (2 * (n : ℝ) ^ 2)) := by rw [e1]
          _ ≤ ((n : ℝ) + c) * (1 / (2 * (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left e2 (hcoe n)
          _ ≤ (1 + c) / 2 * (1 / (n : ℝ)) := by
              have hnpos : (0:ℝ) < (n : ℝ) := by linarith
              have hE : (1 + c) / 2 * (1 / (n : ℝ)) - ((n : ℝ) + c) * (1 / (2 * (n : ℝ) ^ 2))
                  = c * ((n : ℝ) - 1) / (2 * (n : ℝ) ^ 2) := by
                field_simp
                ring
              have hpos : (0:ℝ) ≤ c * ((n : ℝ) - 1) / (2 * (n : ℝ) ^ 2) :=
                div_nonneg (mul_nonneg hc (by linarith)) (by positivity)
              linarith
    simpa using hB.add hA
  simpa [Real.arctan_one] using tele h1 h2 h3 h4

/-! ## The theorem -/

theorem sum_n_arctan_eq_pi :
    tsum (fun (n : ℤ) => (n : ℝ) * Real.arctan ((4 * (n : ℝ) + 2) /
      (4 * (n : ℝ) ^ 4 + 8 * (n : ℝ) ^ 3 + 4 * (n : ℝ) ^ 2 + 1))) = Real.pi := by
  -- the `n ≥ 0` half
  have hp : HasSum (fun n : ℕ => (((n : ℤ) : ℝ)) * arctan ((4 * ((n : ℤ) : ℝ) + 2) /
      (4 * ((n : ℤ) : ℝ) ^ 4 + 8 * ((n : ℤ) : ℝ) ^ 3 + 4 * ((n : ℤ) : ℝ) ^ 2 + 1)))
      (0 * (π / 2) + π / 4) := by
    have e : (fun n : ℕ => (((n : ℤ) : ℝ)) * arctan ((4 * ((n : ℤ) : ℝ) + 2) /
        (4 * ((n : ℤ) : ℝ) ^ 4 + 8 * ((n : ℤ) : ℝ) ^ 3 + 4 * ((n : ℤ) : ℝ) ^ 2 + 1)))
        = fun n : ℕ => ((n : ℝ) + 0) * arctan ((4 * (n : ℝ) + 2) /
        (4 * (n : ℝ) ^ 4 + 8 * (n : ℝ) ^ 3 + 4 * (n : ℝ) ^ 2 + 1)) := by
      funext n; push_cast; ring
    rw [e]; exact main le_rfl
  -- the `n < 0` half, reindexed by `n = -(m+1)`
  have hn : HasSum (fun m : ℕ => ((((-(m + 1) : ℤ)) : ℝ)) *
      arctan ((4 * (((-(m + 1) : ℤ)) : ℝ) + 2) /
        (4 * (((-(m + 1) : ℤ)) : ℝ) ^ 4 + 8 * (((-(m + 1) : ℤ)) : ℝ) ^ 3
          + 4 * (((-(m + 1) : ℤ)) : ℝ) ^ 2 + 1))) (1 * (π / 2) + π / 4) := by
    have e : (fun m : ℕ => ((((-(m + 1) : ℤ)) : ℝ)) *
        arctan ((4 * (((-(m + 1) : ℤ)) : ℝ) + 2) /
          (4 * (((-(m + 1) : ℤ)) : ℝ) ^ 4 + 8 * (((-(m + 1) : ℤ)) : ℝ) ^ 3
            + 4 * (((-(m + 1) : ℤ)) : ℝ) ^ 2 + 1)))
        = fun m : ℕ => ((m : ℝ) + 1) * arctan ((4 * (m : ℝ) + 2) /
          (4 * (m : ℝ) ^ 4 + 8 * (m : ℝ) ^ 3 + 4 * (m : ℝ) ^ 2 + 1)) := by
      funext m
      push_cast
      rw [show (4 * (-((m : ℝ) + 1)) + 2) / (4 * (-((m : ℝ) + 1)) ^ 4
            + 8 * (-((m : ℝ) + 1)) ^ 3 + 4 * (-((m : ℝ) + 1)) ^ 2 + 1)
          = -((4 * (m : ℝ) + 2) /
            (4 * (m : ℝ) ^ 4 + 8 * (m : ℝ) ^ 3 + 4 * (m : ℝ) ^ 2 + 1)) from by
        rw [show (4 * (-((m : ℝ) + 1)) ^ 4 + 8 * (-((m : ℝ) + 1)) ^ 3
              + 4 * (-((m : ℝ) + 1)) ^ 2 + 1)
            = 4 * (m : ℝ) ^ 4 + 8 * (m : ℝ) ^ 3 + 4 * (m : ℝ) ^ 2 + 1 from by ring]
        ring]
      rw [Real.arctan_neg]
      ring
    rw [e]; exact main zero_le_one
  have hb : HasSum (fun n : ℤ => (n : ℝ) * arctan ((4 * (n : ℝ) + 2) /
      (4 * (n : ℝ) ^ 4 + 8 * (n : ℝ) ^ 3 + 4 * (n : ℝ) ^ 2 + 1)))
      (0 * (π / 2) + π / 4 + (1 * (π / 2) + π / 4)) := by
    first
      | exact HasSum.of_nat_of_neg_add_one hp hn
      | exact HasSum.of_nat_of_neg_add_one hp (by simpa [Nat.succ_eq_add_one] using hn)
      | exact HasSum.nonneg_add_neg hp hn
      | exact HasSum.nonneg_add_neg hp (by simpa [Nat.succ_eq_add_one] using hn)
  rw [hb.tsum_eq]
  ring
```
