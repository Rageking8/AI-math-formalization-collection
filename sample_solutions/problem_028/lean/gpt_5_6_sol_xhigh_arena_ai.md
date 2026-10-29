# GPT-5.6 Sol xHigh (Arena AI)

Model: `gpt-5.6-sol-xhigh` (via Arena AI)\
Date: `17 August 2026`\
Line count: `119`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem unique_real_solution_nested_radical (x : ℝ) (hx : 0 ≤ x) :
    (19 * Real.sqrt (2 * x + 1) + 34 * Real.sqrt x) ^ (1 / 3 : ℝ) =
      Real.sqrt (2 * x + 1) + Real.sqrt x ↔ x = 4 := by
  constructor
  · intro h
    let a : ℝ := Real.sqrt (2 * x + 1)
    let b : ℝ := Real.sqrt x
    change (19 * a + 34 * b) ^ (1 / 3 : ℝ) = a + b at h

    have ha_sq : a ^ 2 = 2 * x + 1 := by
      dsimp [a]
      exact Real.sq_sqrt (by nlinarith)
    have hb_sq : b ^ 2 = x := by
      dsimp [b]
      exact Real.sq_sqrt hx
    have ha_pos : 0 < a := by
      dsimp [a]
      exact Real.sqrt_pos.2 (by nlinarith)
    have hb_nonneg : 0 ≤ b := by
      dsimp [b]
      exact Real.sqrt_nonneg x
    have hbase_pos : 0 < 19 * a + 34 * b := by
      nlinarith
    have hsum_pos : 0 < a + b := by
      nlinarith

    have hcube : 19 * a + 34 * b = (a + b) ^ 3 := by
      calc
        19 * a + 34 * b =
            (19 * a + 34 * b) ^ (1 : ℝ) := by simp
        _ = (19 * a + 34 * b) ^ ((1 / 3 : ℝ) * 3) := by
          norm_num
        _ = ((19 * a + 34 * b) ^ (1 / 3 : ℝ)) ^ (3 : ℝ) := by
          rw [Real.rpow_mul hbase_pos.le]
        _ = (a + b) ^ (3 : ℝ) := by
          rw [h]
        _ = (a + b) ^ 3 := by
          simpa [Real.rpow_natCast, hsum_pos.le]

    have hcube_exp :
        (a + b) ^ 3 = a * (5 * x + 1) + b * (7 * x + 3) := by
      calc
        (a + b) ^ 3 =
            a * a ^ 2 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b * b ^ 2 := by
              ring
        _ = a * (5 * x + 1) + b * (7 * x + 3) := by
          rw [ha_sq, hb_sq]
          ring

    have hlinear :
        (5 * x - 18) * a + (7 * x - 31) * b = 0 := by
      rw [hcube_exp] at hcube
      nlinarith [hcube]

    have hx_lower : (18 : ℝ) / 5 ≤ x := by
      by_contra hlt
      have hxlt : x < (18 : ℝ) / 5 := lt_of_not_ge hlt
      have hc₁ : 5 * x - 18 < 0 := by
        nlinarith
      have hc₂ : 7 * x - 31 < 0 := by
        nlinarith
      have hp₁ : (5 * x - 18) * a < 0 :=
        mul_neg_of_neg_of_pos hc₁ ha_pos
      have hp₂ : (7 * x - 31) * b ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc₂.le hb_nonneg
      nlinarith [hlinear, hp₁, hp₂]

    have hprod :
        (5 * x - 18) * a = -((7 * x - 31) * b) := by
      nlinarith [hlinear]
    have hsq₀ := congrArg (fun t : ℝ => t ^ 2) hprod
    have hsq :
        ((5 * x - 18) * a) ^ 2 = ((7 * x - 31) * b) ^ 2 := by
      calc
        ((5 * x - 18) * a) ^ 2 =
            (-((7 * x - 31) * b)) ^ 2 := hsq₀
        _ = ((7 * x - 31) * b) ^ 2 := by ring

    have hsq_poly :
        (5 * x - 18) ^ 2 * (2 * x + 1) =
          (7 * x - 31) ^ 2 * x := by
      calc
        (5 * x - 18) ^ 2 * (2 * x + 1) =
            ((5 * x - 18) * a) ^ 2 := by
              rw [mul_pow, ha_sq]
        _ = ((7 * x - 31) * b) ^ 2 := hsq
        _ = (7 * x - 31) ^ 2 * x := by
          rw [mul_pow, hb_sq]

    have hfactor :
        (x - 4) * (x ^ 2 + 103 * x - 81) = 0 := by
      nlinarith [hsq_poly]
    have hquad_pos : 0 < x ^ 2 + 103 * x - 81 := by
      nlinarith [sq_nonneg x]

    rcases mul_eq_zero.mp hfactor with hx4 | hquad
    · nlinarith
    · nlinarith

  · intro hx4
    subst x
    have hs9 : Real.sqrt (2 * (4 : ℝ) + 1) = 3 := by
      norm_num
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      norm_num
    have hfive : (5 : ℝ) ^ (3 : ℝ) = 125 := by
      norm_num [Real.rpow_natCast]
    have hroot : (125 : ℝ) ^ (1 / 3 : ℝ) = 5 := by
      calc
        (125 : ℝ) ^ (1 / 3 : ℝ) =
            ((5 : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
              rw [hfive]
        _ = (5 : ℝ) ^ ((3 : ℝ) * (1 / 3 : ℝ)) := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
        _ = 5 := by norm_num
    rw [hs9, hs4]
    convert hroot using 1 <;> norm_num
```
