# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `14 September 2026`\
Line count: `126`\
Turn count: `3 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem min_poly_eq_max_exp_iff_eq_two (x : ℝ) :
    min (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1) = max ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x) ↔ x = 2 := by
  have hrpow3_2 : (3:ℝ) ^ (2:ℝ) = 9 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hrpow2_2 : (2:ℝ) ^ (2:ℝ) = 4 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  constructor
  · intro h
    by_cases hx1 : x ≤ (-1 : ℝ)
    · exfalso
      have hfact : x^3 - 2*x^2 + 3 - (x^2 - 1) = (x-2)^2 * (x+1) := by ring
      have hprod : (x-2)^2 * (x+1) ≤ 0 := by
        nlinarith [mul_nonneg (sq_nonneg (x-2)) (show (0:ℝ) ≤ -(x+1) by linarith)]
      have hAB : x^3 - 2*x^2 + 3 ≤ x^2 - 1 := by linarith
      have hmin : min (x^3 - 2*x^2 + 3) (x^2 - 1) = x^3 - 2*x^2 + 3 := min_eq_left hAB
      have h2xle : (2:ℝ)^x ≤ (1:ℝ)/2 := by
        have hle : (2:ℝ)^x ≤ (2:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hx1
        have heq : (2:ℝ)^(-1:ℝ) = 1/2 := by
          rw [show (-1:ℝ) = -(1:ℝ) by norm_num, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
            Real.rpow_one]
          norm_num
        rw [heq] at hle
        exact hle
      have h3xle : (3:ℝ)^x ≤ (1:ℝ)/3 := by
        have hle : (3:ℝ)^x ≤ (3:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hx1
        have heq : (3:ℝ)^(-1:ℝ) = 1/3 := by
          rw [show (-1:ℝ) = -(1:ℝ) by norm_num, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3),
            Real.rpow_one]
          norm_num
        rw [heq] at hle
        exact hle
      have hCD : (3:ℝ)^x - 6 ≤ 7 - (2:ℝ)^x := by linarith
      have hmax : max ((3:ℝ)^x - 6) (7 - (2:ℝ)^x) = 7 - (2:ℝ)^x := max_eq_right hCD
      rw [hmin, hmax] at h
      have key1 : (0:ℝ) ≤ -(x+1) * x^2 := mul_nonneg (by linarith) (sq_nonneg x)
      nlinarith [h, h2xle, key1, sq_nonneg x]
    · push_neg at hx1
      have hfact : x^3 - 2*x^2 + 3 - (x^2 - 1) = (x-2)^2 * (x+1) := by ring
      have hprod' : (0:ℝ) ≤ (x-2)^2 * (x+1) := mul_nonneg (sq_nonneg _) (by linarith)
      have hBA : x^2 - 1 ≤ x^3 - 2*x^2 + 3 := by linarith
      have hminBA : min (x^3 - 2*x^2 + 3) (x^2 - 1) = x^2 - 1 := min_eq_right hBA
      rw [hminBA] at h
      by_cases hx2 : x ≤ (2 : ℝ)
      · have h3xle : (3:ℝ)^x ≤ 9 := by
          have hle := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hx2
          rwa [hrpow3_2] at hle
        have h2xle : (2:ℝ)^x ≤ 4 := by
          have hle := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hx2
          rwa [hrpow2_2] at hle
        have hCD : (3:ℝ)^x - 6 ≤ 7 - (2:ℝ)^x := by linarith
        have hmax : max ((3:ℝ)^x - 6) (7 - (2:ℝ)^x) = 7 - (2:ℝ)^x := max_eq_right hCD
        rw [hmax] at h
        by_contra hne
        have hxlt2 : x < 2 := lt_of_le_of_ne hx2 hne
        have hx2sq : x^2 < 4 := by
          nlinarith [mul_pos (show (0:ℝ) < 2 - x by linarith) (show (0:ℝ) < x + 2 by linarith)]
        have h2xlt : (2:ℝ)^x < 4 := by
          have hlt := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hxlt2
          rwa [hrpow2_2] at hlt
        linarith [h, hx2sq, h2xlt]
      · push_neg at hx2
        exfalso
        have h2xgt : (4:ℝ) < (2:ℝ)^x := by
          have hlt := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hx2
          rwa [hrpow2_2] at hlt
        have h3xgt : (9:ℝ) < (3:ℝ)^x := by
          have hlt := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 3) hx2
          rwa [hrpow3_2] at hlt
        have hDC : 7 - (2:ℝ)^x ≤ (3:ℝ)^x - 6 := by linarith
        have hmax : max ((3:ℝ)^x - 6) (7 - (2:ℝ)^x) = (3:ℝ)^x - 6 := max_eq_left hDC
        rw [hmax] at h
        have hL1 : (1:ℝ) < Real.log 3 := by
          have hexp1 : Real.exp 1 < 3 := by nlinarith [Real.exp_one_lt_d9]
          have hlog := Real.log_lt_log (Real.exp_pos 1) hexp1
          rwa [Real.log_exp] at hlog
        have hxu : (0:ℝ) < x - 2 := by linarith
        have hlog3pos : (0:ℝ) < Real.log 3 := by linarith
        have hexp_quad : (1 + (x-2) * Real.log 3 / 2)^2 ≤ Real.exp ((x-2) * Real.log 3) := by
          have ht1 : (x-2)*Real.log 3/2 + 1 ≤ Real.exp ((x-2)*Real.log 3/2) :=
            Real.add_one_le_exp _
          have ht1' : (0:ℝ) ≤ (x-2)*Real.log 3/2 + 1 := by
            nlinarith [mul_pos hxu hlog3pos]
          have ht2' : (0:ℝ) ≤ Real.exp ((x-2)*Real.log 3/2) := (Real.exp_pos _).le
          have hmul := mul_le_mul ht1 ht1 ht1' ht2'
          rw [← Real.exp_add] at hmul
          have heqhalf : (x-2)*Real.log 3/2 + (x-2)*Real.log 3/2 = (x-2)*Real.log 3 := by ring
          rw [heqhalf] at hmul
          nlinarith [hmul]
        have hrpow_eq : (3:ℝ) ^ (x - 2) = Real.exp ((x - 2) * Real.log 3) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
          congr 1
          ring
        have hbound2 : (1 + (x-2) * Real.log 3 / 2)^2 ≤ (3:ℝ)^(x-2) := by
          rw [hrpow_eq]; exact hexp_quad
        have hxsplit0 : (3:ℝ)^x = (3:ℝ)^(2:ℝ) * (3:ℝ)^(x-2) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
          congr 1
          ring
        have hxsplit : (3:ℝ)^x = 9 * (3:ℝ)^(x-2) := by rw [hxsplit0, hrpow3_2]
        have hbound3 : 9 * (1 + (x-2) * Real.log 3 / 2)^2 ≤ (3:ℝ)^x := by
          rw [hxsplit]
          nlinarith [hbound2]
        have hcoef1 : (0:ℝ) < 9*Real.log 3 - 4 := by linarith
        have hcoef2 : (0:ℝ) < (9/4)*(Real.log 3)^2 - 1 := by
          nlinarith [mul_pos (show (0:ℝ) < Real.log 3 - 1 by linarith)
            (show (0:ℝ) < Real.log 3 + 1 by linarith)]
        have hp1 : (0:ℝ) < (x-2)*(9*Real.log 3 - 4) := mul_pos hxu hcoef1
        have hp2 : (0:ℝ) < (x-2)^2*((9/4)*(Real.log 3)^2 - 1) :=
          mul_pos (pow_pos hxu 2) hcoef2
        have hchain : x^2 + 5 + (x-2)*(9*Real.log 3 - 4) + (x-2)^2*((9/4)*(Real.log 3)^2 - 1)
            ≤ (3:ℝ)^x := by
          calc x^2 + 5 + (x-2)*(9*Real.log 3 - 4) + (x-2)^2*((9/4)*(Real.log 3)^2 - 1)
              = 9 * (1 + (x-2) * Real.log 3 / 2)^2 := by ring
            _ ≤ (3:ℝ)^x := hbound3
        have hfinal : x^2 + 5 < (3:ℝ)^x := by linarith [hchain, hp1, hp2]
        linarith [h, hfinal]
  · rintro rfl
    have e1 : (2:ℝ) ^ 3 - 2 * (2:ℝ) ^ 2 + 3 = 3 := by norm_num
    have e2 : (2:ℝ) ^ 2 - 1 = 3 := by norm_num
    have e3 : (9:ℝ) - 6 = 3 := by norm_num
    have e4 : (7:ℝ) - 4 = 3 := by norm_num
    rw [e1, e2, hrpow3_2, hrpow2_2, e3, e4, min_self, max_self]
```
