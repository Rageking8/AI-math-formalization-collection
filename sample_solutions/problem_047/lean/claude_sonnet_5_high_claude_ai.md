# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `15 September 2026`\
Line count: `146`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem sum_floor_div_eq_implies_dvd (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : ∑' (n : ℕ), ((n : ℝ) / (2 : ℝ) ^ n) * (Int.floor ((n : ℝ) * (y : ℝ) / (x : ℝ)) : ℝ) = 6 * (y : ℝ) / (x : ℝ)) :
      x ∣ y := by
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
  have hy0 : (0:ℝ) < (y:ℝ) := by exact_mod_cast hy
  set t : ℝ := (y:ℝ) / (x:ℝ) with ht_def
  have ht_pos : 0 < t := div_pos hy0 hx0
  have hnorm : ‖(1/2:ℝ)‖ < 1 := by norm_num
  have hS1 : Summable (fun n : ℕ => (n:ℝ) * (1/2:ℝ)^n) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    simpa using h1
  have hS2 : Summable (fun n : ℕ => (n:ℝ)^2 * (1/2:ℝ)^n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
  have hSG : Summable (fun n : ℕ => (1/2:ℝ)^n) := summable_geometric_of_norm_lt_one hnorm
  have hGval : (∑' n : ℕ, (1/2:ℝ)^n) = 2 := by
    rw [tsum_geometric_of_norm_lt_one hnorm]; norm_num
  -- Direct closed form for the linear sum, no shift trick needed
  have hAval : (∑' n : ℕ, (n:ℝ) * (1/2:ℝ)^n) = 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one hnorm]; norm_num
  have hG5 : (∑' n : ℕ, (1/2:ℝ) * (1/2:ℝ)^n) = (1/2:ℝ) * (∑' n : ℕ, (1/2:ℝ)^n) := by
    rw [tsum_mul_left]
  -- Shift trick still needed for the quadratic sum (no closed form in Mathlib)
  have hSpt : ∀ n : ℕ, (((n+1:ℕ):ℝ))^2 * (1/2:ℝ)^(n+1)
      = (1/2:ℝ) * ((n:ℝ)^2 * (1/2:ℝ)^n) + (n:ℝ) * (1/2:ℝ)^n + (1/2:ℝ) * (1/2:ℝ)^n := by
    intro n; rw [pow_succ]; push_cast; ring
  have hSeq2 : (∑' n : ℕ, (((n+1:ℕ):ℝ))^2 * (1/2:ℝ)^(n+1))
      = ∑' n : ℕ, ((1/2:ℝ) * ((n:ℝ)^2 * (1/2:ℝ)^n) + (n:ℝ) * (1/2:ℝ)^n + (1/2:ℝ) * (1/2:ℝ)^n) :=
    tsum_congr hSpt
  have hSeq3 : (∑' n : ℕ, ((1/2:ℝ) * ((n:ℝ)^2 * (1/2:ℝ)^n) + (n:ℝ) * (1/2:ℝ)^n + (1/2:ℝ) * (1/2:ℝ)^n))
      = ((∑' n : ℕ, (1/2:ℝ) * ((n:ℝ)^2 * (1/2:ℝ)^n)) + ∑' n : ℕ, (n:ℝ) * (1/2:ℝ)^n) + ∑' n : ℕ, (1/2:ℝ) * (1/2:ℝ)^n := by
    rw [Summable.tsum_add (Summable.add (hS2.mul_left (1/2:ℝ)) hS1) (hSG.mul_left (1/2:ℝ)),
        Summable.tsum_add (hS2.mul_left (1/2:ℝ)) hS1]
  have hSeq4 : (∑' n : ℕ, (1/2:ℝ) * ((n:ℝ)^2 * (1/2:ℝ)^n)) = (1/2:ℝ) * ∑' n : ℕ, (n:ℝ)^2 * (1/2:ℝ)^n := by
    rw [tsum_mul_left]
  have hSshift : (∑' n : ℕ, (n:ℝ)^2 * (1/2:ℝ)^n)
      = ((0:ℕ):ℝ)^2 * (1/2:ℝ)^(0:ℕ) + ∑' n : ℕ, (((n+1:ℕ):ℝ))^2 * (1/2:ℝ)^(n+1) :=
    Summable.tsum_eq_zero_add hS2
  have hSval : (∑' n : ℕ, (n:ℝ)^2 * (1/2:ℝ)^n) = 6 := by
    have key : (∑' n : ℕ, (n:ℝ)^2 * (1/2:ℝ)^n)
        = (1/2:ℝ) * (∑' n : ℕ, (n:ℝ)^2 * (1/2:ℝ)^n)
          + (∑' n : ℕ, (n:ℝ) * (1/2:ℝ)^n)
          + (1/2:ℝ) * (∑' n : ℕ, (1/2:ℝ)^n) := by
      calc (∑' n : ℕ, (n:ℝ)^2 * (1/2:ℝ)^n)
          = ((0:ℕ):ℝ)^2 * (1/2:ℝ)^(0:ℕ) + ∑' n : ℕ, (((n+1:ℕ):ℝ))^2 * (1/2:ℝ)^(n+1) := hSshift
        _ = ∑' n : ℕ, (((n+1:ℕ):ℝ))^2 * (1/2:ℝ)^(n+1) := by simp
        _ = ∑' n : ℕ, ((1/2:ℝ) * ((n:ℝ)^2 * (1/2:ℝ)^n) + (n:ℝ) * (1/2:ℝ)^n + (1/2:ℝ) * (1/2:ℝ)^n) := hSeq2
        _ = ((∑' n : ℕ, (1/2:ℝ) * ((n:ℝ)^2 * (1/2:ℝ)^n)) + ∑' n : ℕ, (n:ℝ) * (1/2:ℝ)^n) + ∑' n : ℕ, (1/2:ℝ) * (1/2:ℝ)^n := hSeq3
        _ = ((1/2:ℝ) * (∑' n : ℕ, (n:ℝ)^2 * (1/2:ℝ)^n) + ∑' n : ℕ, (n:ℝ) * (1/2:ℝ)^n) + (1/2:ℝ) * (∑' n : ℕ, (1/2:ℝ)^n) := by
              rw [hSeq4, hG5]
        _ = (1/2:ℝ) * (∑' n : ℕ, (n:ℝ)^2 * (1/2:ℝ)^n) + (∑' n : ℕ, (n:ℝ) * (1/2:ℝ)^n) + (1/2:ℝ) * (∑' n : ℕ, (1/2:ℝ)^n) := by
              ring
    rw [hAval, hGval] at key
    linarith
  -- Convert the hypothesis to the (1/2)^n form (fixed rewrite)
  have heqconv : ∀ n : ℕ, (n:ℝ) * (1/2:ℝ)^n = (n:ℝ) / (2:ℝ)^n := by
    intro n; rw [div_pow, one_pow, mul_one_div]
  have h' : (∑' (n : ℕ), (n:ℝ) * (1/2:ℝ)^n * (Int.floor ((n:ℝ) * (y:ℝ) / (x:ℝ)) : ℝ)) = 6 * t := by
    have heq2 : ∀ n : ℕ, (n:ℝ) * (1/2:ℝ)^n * (Int.floor ((n:ℝ) * (y:ℝ) / (x:ℝ)) : ℝ)
        = (n:ℝ) / (2:ℝ)^n * (Int.floor ((n:ℝ) * (y:ℝ) / (x:ℝ)) : ℝ) := by
      intro n; rw [heqconv n]
    rw [tsum_congr heq2, h, ht_def]
    ring
  -- Floor decomposition
  have hnt : ∀ n : ℕ, (n:ℝ) * (y:ℝ) / (x:ℝ) = (n:ℝ) * t := by
    intro n; rw [ht_def, mul_div_assoc]
  have hfloor : ∀ n : ℕ, (Int.floor ((n:ℝ) * t) : ℝ) = (n:ℝ) * t - Int.fract ((n:ℝ) * t) := by
    intro n
    have hfa := Int.floor_add_fract ((n:ℝ) * t)
    linarith
  have hpt_main : ∀ n : ℕ, (n:ℝ) * (1/2:ℝ)^n * (Int.floor ((n:ℝ) * (y:ℝ) / (x:ℝ)) : ℝ)
      = t * ((n:ℝ)^2 * (1/2:ℝ)^n) - (n:ℝ) * (1/2:ℝ)^n * Int.fract ((n:ℝ) * t) := by
    intro n
    have e1 : (Int.floor ((n:ℝ) * (y:ℝ) / (x:ℝ)) : ℝ) = (n:ℝ) * t - Int.fract ((n:ℝ) * t) := by
      rw [hnt n]; exact hfloor n
    rw [e1]; ring
  have hc_nonneg : ∀ n : ℕ, (0:ℝ) ≤ (n:ℝ) * (1/2:ℝ)^n * Int.fract ((n:ℝ) * t) := by
    intro n
    apply mul_nonneg
    · positivity
    · exact Int.fract_nonneg _
  have hc_le : ∀ n : ℕ, (n:ℝ) * (1/2:ℝ)^n * Int.fract ((n:ℝ) * t) ≤ (n:ℝ) * (1/2:ℝ)^n := by
    intro n
    have h1 : Int.fract ((n:ℝ) * t) ≤ 1 := le_of_lt (Int.fract_lt_one _)
    have h2 : (0:ℝ) ≤ (n:ℝ) * (1/2:ℝ)^n := by positivity
    have h3 : (0:ℝ) ≤ Int.fract ((n:ℝ) * t) := Int.fract_nonneg _
    nlinarith
  have hSc : Summable (fun n : ℕ => (n:ℝ) * (1/2:ℝ)^n * Int.fract ((n:ℝ) * t)) :=
    Summable.of_nonneg_of_le hc_nonneg hc_le hS1
  -- Build the main relation using addition instead of subtraction
  have hSfloor : Summable (fun n : ℕ => (n:ℝ) * (1/2:ℝ)^n * (Int.floor ((n:ℝ) * (y:ℝ) / (x:ℝ)) : ℝ)) := by
    have hsub : Summable (fun n : ℕ => t * ((n:ℝ)^2 * (1/2:ℝ)^n) - (n:ℝ) * (1/2:ℝ)^n * Int.fract ((n:ℝ) * t)) :=
      (hS2.mul_left t).sub hSc
    exact hsub.congr (fun n => (hpt_main n).symm)
  have hpteq2 : ∀ n : ℕ, (n:ℝ) * (1/2:ℝ)^n * (Int.floor ((n:ℝ) * (y:ℝ) / (x:ℝ)) : ℝ)
      + (n:ℝ) * (1/2:ℝ)^n * Int.fract ((n:ℝ) * t) = t * ((n:ℝ)^2 * (1/2:ℝ)^n) := by
    intro n; rw [hpt_main n]; ring
  have hadd : (∑' n : ℕ, ((n:ℝ) * (1/2:ℝ)^n * (Int.floor ((n:ℝ) * (y:ℝ) / (x:ℝ)) : ℝ)
      + (n:ℝ) * (1/2:ℝ)^n * Int.fract ((n:ℝ) * t)))
      = (∑' n : ℕ, (n:ℝ) * (1/2:ℝ)^n * (Int.floor ((n:ℝ) * (y:ℝ) / (x:ℝ)) : ℝ))
        + ∑' n : ℕ, (n:ℝ) * (1/2:ℝ)^n * Int.fract ((n:ℝ) * t) :=
    Summable.tsum_add hSfloor hSc
  have hmain : (∑' n : ℕ, (n:ℝ) * (1/2:ℝ)^n * (Int.floor ((n:ℝ) * (y:ℝ) / (x:ℝ)) : ℝ))
      + (∑' n : ℕ, (n:ℝ) * (1/2:ℝ)^n * Int.fract ((n:ℝ) * t))
      = t * (∑' n : ℕ, (n:ℝ)^2 * (1/2:ℝ)^n) := by
    rw [← hadd, tsum_congr hpteq2, tsum_mul_left]
  have hc_sum_zero : (∑' n : ℕ, (n:ℝ) * (1/2:ℝ)^n * Int.fract ((n:ℝ) * t)) = 0 := by
    have e1 := hmain
    rw [h', hSval] at e1
    ring_nf at e1 ⊢
    linarith
  -- Extract that the n=1 term vanishes, via a contradiction argument
  have hc1 : ((1:ℕ):ℝ) * (1/2:ℝ)^(1:ℕ) * Int.fract (((1:ℕ):ℝ) * t) = 0 := by
    by_contra hne
    have hpos : (0:ℝ) < ((1:ℕ):ℝ) * (1/2:ℝ)^(1:ℕ) * Int.fract (((1:ℕ):ℝ) * t) :=
      lt_of_le_of_ne (hc_nonneg 1) (Ne.symm hne)
    have hlt : (∑' _ : ℕ, (0:ℝ)) < ∑' n : ℕ, (n:ℝ) * (1/2:ℝ)^n * Int.fract ((n:ℝ) * t) :=
      Summable.tsum_lt_tsum_of_nonneg (fun _ => le_refl (0:ℝ)) hc_nonneg hpos hSc
    rw [tsum_zero, hc_sum_zero] at hlt
    exact lt_irrefl 0 hlt
  have hfract0 : Int.fract t = 0 := by
    have e : ((1:ℕ):ℝ) * (1/2:ℝ)^(1:ℕ) * Int.fract (((1:ℕ):ℝ) * t) = (1/2:ℝ) * Int.fract t := by
      simp
    rw [e] at hc1
    linarith
  have ht_int : t = (Int.floor t : ℝ) := by
    have hfa := Int.floor_add_fract t
    rw [hfract0] at hfa
    linarith
  have hk_pos : 0 < Int.floor t := by
    have hpos : (0:ℝ) < (Int.floor t : ℝ) := by rw [← ht_int]; exact ht_pos
    exact_mod_cast hpos
  have hm_nonneg : 0 ≤ Int.floor t := le_of_lt hk_pos
  set m : ℕ := (Int.floor t).toNat with hm_def
  have hm_eq : (m:ℤ) = Int.floor t := Int.toNat_of_nonneg hm_nonneg
  have hm_real0 : (m:ℝ) = (Int.floor t : ℝ) := by exact_mod_cast hm_eq
  have hm_real : (m:ℝ) = t := by rw [hm_real0, ← ht_int]
  have hxy : (y:ℝ) = (m:ℝ) * (x:ℝ) := by
    have heq : (m:ℝ) = (y:ℝ) / (x:ℝ) := by rw [hm_real, ht_def]
    rw [eq_div_iff hx0.ne'] at heq
    exact heq.symm
  have hxy_nat : y = m * x := by
    have hcast : (y:ℝ) = ((m * x : ℕ):ℝ) := by rw [hxy]; push_cast; ring
    exact_mod_cast hcast
  exact ⟨m, by rw [hxy_nat, Nat.mul_comm]⟩
```
