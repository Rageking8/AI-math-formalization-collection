# GPT-5.6 Sol xHigh (Arena AI)

Model: `gpt-5.6-sol-xhigh` (via Arena AI)\
Date: `10 August 2026`\
Line count: `138`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem positive_real_inequality (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y)
      (h_sum : x ^ 2 + y ^ 2 = 1) :
      ((x ^ (2 * x)) / (3 * y)) + ((y ^ (2 * y)) / (3 * x)) > 1 / (x ^ 2 + y ^ 2 + 4 * x * y) := by
  have hxlt : x < 1 := by
    by_contra h
    have hxge : 1 ≤ x := le_of_not_gt h
    have hfac : 0 ≤ (x - 1) * (x + 1) :=
      mul_nonneg (sub_nonneg.mpr hxge) (by linarith)
    have hy_sq_pos : 0 < y ^ 2 := by positivity
    nlinarith [hfac, h_sum]

  have hylt : y < 1 := by
    by_contra h
    have hyge : 1 ≤ y := le_of_not_gt h
    have hfac : 0 ≤ (y - 1) * (y + 1) :=
      mul_nonneg (sub_nonneg.mpr hyge) (by linarith)
    have hx_sq_pos : 0 < x ^ 2 := by positivity
    nlinarith [hfac, h_sum]

  have rpow_sq_lt (z : ℝ) (hz : 0 < z) (hz1 : z < 1) :
      z ^ (2 : ℕ) < z ^ (2 * z) := by
    have hlog : Real.log z < 0 := Real.log_neg hz hz1
    have harg : Real.log z * 2 < Real.log z * (2 * z) := by
      have hdiff : 2 * z - 2 < 0 := by nlinarith
      have hprod : 0 < Real.log z * (2 * z - 2) :=
        mul_pos_of_neg_of_neg hlog hdiff
      nlinarith
    have hsq :
        z ^ (2 : ℕ) = Real.exp (Real.log z * 2) := by
      calc
        z ^ (2 : ℕ) = z * z := by ring
        _ = Real.exp (Real.log z) * Real.exp (Real.log z) := by
          rw [Real.exp_log hz]
        _ = Real.exp (Real.log z + Real.log z) := by
          rw [Real.exp_add]
        _ = Real.exp (Real.log z * 2) := by
          congr 1 <;> ring
    rw [hsq, Real.rpow_def_of_pos hz]
    exact Real.exp_lt_exp.mpr harg

  have hrx : x ^ (2 : ℕ) < x ^ (2 * x) :=
    rpow_sq_lt x hx hxlt
  have hry : y ^ (2 : ℕ) < y ^ (2 * y) :=
    rpow_sq_lt y hy hylt

  have hxy : 0 < x * y := mul_pos hx hy
  have hxy_le : x * y ≤ (1 : ℝ) / 2 := by
    nlinarith [sq_nonneg (x - y)]

  have hs : 1 < x + y := by
    by_contra h
    have hsle : x + y ≤ 1 := le_of_not_gt h
    have hfac : 0 ≤ (1 - (x + y)) * (1 + (x + y)) :=
      mul_nonneg (sub_nonneg.mpr hsle) (by nlinarith [hx, hy])
    nlinarith [hfac, h_sum, hxy]

  have hminus : 0 ≤ 1 - 2 * (x * y) := by
    nlinarith [hxy_le]
  have hplus : 0 ≤ 1 + 2 * (x * y) := by
    nlinarith [hxy]
  have hprod : 0 ≤ (1 - 2 * (x * y)) * (1 + 2 * (x * y)) :=
    mul_nonneg hminus hplus

  have hq :
      3 * (x * y) ≤ (1 - x * y) * (1 + 4 * x * y) := by
    nlinarith [hprod]
  have hqpos : 0 < (1 - x * y) * (1 + 4 * x * y) := by
    have hthree : 0 < 3 * (x * y) := by positivity
    exact lt_of_lt_of_le hthree hq
  have hgrow :
      (1 - x * y) * (1 + 4 * x * y) <
        (x + y) * ((1 - x * y) * (1 + 4 * x * y)) := by
    simpa only [one_mul] using
      (mul_lt_mul_of_pos_right hs hqpos)
  have hmain :
      3 * (x * y) <
        (x + y) * ((1 - x * y) * (1 + 4 * x * y)) :=
    lt_of_le_of_lt hq hgrow

  have hcubes :
      x ^ 3 + y ^ 3 = (x + y) * (1 - x * y) := by
    calc
      x ^ 3 + y ^ 3 =
          (x + y) * (x ^ 2 + y ^ 2 - x * y) := by ring
      _ = (x + y) * (1 - x * y) := by rw [h_sum]

  have hpoly :
      3 * (x * y) <
        (x ^ 2 + y ^ 2 + 4 * x * y) * (x ^ 3 + y ^ 3) := by
    calc
      3 * (x * y) <
          (x + y) * ((1 - x * y) * (1 + 4 * x * y)) := hmain
      _ = (x ^ 2 + y ^ 2 + 4 * x * y) * (x ^ 3 + y ^ 3) := by
        rw [h_sum, hcubes]
        ring

  have hD : 0 < x ^ 2 + y ^ 2 + 4 * x * y := by
    rw [h_sum]
    nlinarith [hxy]
  have h3xy : 0 < 3 * x * y := by positivity

  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hlower_eq :
      x ^ 2 / (3 * y) + y ^ 2 / (3 * x) =
        (x ^ 3 + y ^ 3) / (3 * x * y) := by
    field_simp [hx0, hy0] <;> ring

  have hfrac :
      1 / (x ^ 2 + y ^ 2 + 4 * x * y) <
        (x ^ 3 + y ^ 3) / (3 * x * y) := by
    apply (div_lt_div_iff₀ hD h3xy).2
    calc
      1 * (3 * x * y) = 3 * (x * y) := by ring
      _ < (x ^ 2 + y ^ 2 + 4 * x * y) * (x ^ 3 + y ^ 3) := hpoly
      _ = (x ^ 3 + y ^ 3) * (x ^ 2 + y ^ 2 + 4 * x * y) := by ring

  have hlower :
      1 / (x ^ 2 + y ^ 2 + 4 * x * y) <
        x ^ 2 / (3 * y) + y ^ 2 / (3 * x) := by
    rw [hlower_eq]
    exact hfrac

  have hxden : 0 < 3 * y := by positivity
  have hyden : 0 < 3 * x := by positivity
  have htermx :
      x ^ 2 / (3 * y) < x ^ (2 * x) / (3 * y) := by
    apply (div_lt_div_iff₀ hxden hxden).2
    exact mul_lt_mul_of_pos_right hrx hxden
  have htermy :
      y ^ 2 / (3 * x) < y ^ (2 * y) / (3 * x) := by
    apply (div_lt_div_iff₀ hyden hyden).2
    exact mul_lt_mul_of_pos_right hry hyden

  exact lt_trans hlower (add_lt_add htermx htermy)
```
