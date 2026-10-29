# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `8 August 2026`\
Line count: `121`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem sum_floor_div_eq_implies_dvd (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : ∑' (n : ℕ), ((n : ℝ) / (2 : ℝ) ^ n) * (Int.floor ((n : ℝ) * (y : ℝ) / (x : ℝ)) : ℝ) = 6 * (y : ℝ) / (x : ℝ)) :
      x ∣ y := by
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
  have hy0 : (0:ℝ) < (y:ℝ) := by exact_mod_cast hy
  have hxne : (x:ℝ) ≠ 0 := ne_of_gt hx0
  have hpos : 0 < 6 * (y:ℝ) / (x:ℝ) := div_pos (by linarith) hx0
  -- partial sums of ∑ n²/2ⁿ
  have key : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((i:ℝ)^2 * (1/2:ℝ)^i)
      = 6 - (2*(N:ℝ)^2 + 4*(N:ℝ) + 6) * (1/2:ℝ)^N := by
    intro N
    induction N with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hnn : ∀ i : ℕ, 0 ≤ ((i:ℝ)^2 * (1/2:ℝ)^i) := fun i => by positivity
  have hbound : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((i:ℝ)^2 * (1/2:ℝ)^i) ≤ 6 := by
    intro N
    rw [key N]
    have hE : 0 ≤ (2*(N:ℝ)^2 + 4*(N:ℝ) + 6) * (1/2:ℝ)^N := by positivity
    linarith
  have hsummable : Summable (fun i : ℕ => ((i:ℝ)^2 * (1/2:ℝ)^i)) := by
    first
      | exact summable_of_sum_range_le hnn hbound
      | exact Summable.of_sum_range_le hnn hbound
  have htend : Filter.Tendsto (fun N : ℕ => (2*(N:ℝ)^2 + 4*(N:ℝ) + 6) * (1/2:ℝ)^N)
      Filter.atTop (nhds (0:ℝ)) := by
    have h0 := hsummable.tendsto_atTop_zero
    have h12 : Filter.Tendsto (fun N : ℕ => 12 * ((N:ℝ)^2 * (1/2:ℝ)^N))
        Filter.atTop (nhds (0:ℝ)) := by simpa using h0.const_mul (12:ℝ)
    refine squeeze_zero' ?_ ?_ h12
    · filter_upwards with N
      show (0:ℝ) ≤ (2*(N:ℝ)^2 + 4*(N:ℝ) + 6) * (1/2:ℝ)^N
      positivity
    · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      show (2*(N:ℝ)^2 + 4*(N:ℝ) + 6) * (1/2:ℝ)^N ≤ 12 * ((N:ℝ)^2 * (1/2:ℝ)^N)
      have h1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      have hp : (0:ℝ) < (1/2:ℝ)^N := by positivity
      have hle2 : 2*(N:ℝ)^2 + 4*(N:ℝ) + 6 ≤ 12*(N:ℝ)^2 := by
        nlinarith [sq_nonneg ((N:ℝ) - 1)]
      calc (2*(N:ℝ)^2 + 4*(N:ℝ) + 6) * (1/2:ℝ)^N
          ≤ (12*(N:ℝ)^2) * (1/2:ℝ)^N := mul_le_mul_of_nonneg_right hle2 hp.le
        _ = 12 * ((N:ℝ)^2 * (1/2:ℝ)^N) := by ring
  have hasSum6 : HasSum (fun i : ℕ => ((i:ℝ)^2 * (1/2:ℝ)^i)) 6 := by
    have h1 := hsummable.hasSum
    have h2 := h1.tendsto_sum_nat
    have h3 : Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, ((i:ℝ)^2 * (1/2:ℝ)^i))
        Filter.atTop (nhds (6:ℝ)) := by
      have h4 : Filter.Tendsto (fun N : ℕ => 6 - (2*(N:ℝ)^2 + 4*(N:ℝ) + 6) * (1/2:ℝ)^N)
          Filter.atTop (nhds (6:ℝ)) := by simpa using htend.const_sub (6:ℝ)
      exact h4.congr (fun N => (key N).symm)
    have h5 : ∑' i : ℕ, ((i:ℝ)^2 * (1/2:ℝ)^i) = 6 := tendsto_nhds_unique h2 h3
    rwa [h5] at h1
  -- the majorant series ∑ (n/2ⁿ)·(n·y/x) = 6y/x
  have hgeq : ∀ n : ℕ, ((n:ℝ)/(2:ℝ)^n) * ((n:ℝ)*(y:ℝ)/(x:ℝ))
      = ((y:ℝ)/(x:ℝ)) * ((n:ℝ)^2 * (1/2:ℝ)^n) := by
    intro n
    have h2n : ((2:ℝ)^n) ≠ 0 := by positivity
    have h2 : (1/2:ℝ)^n = 1/(2:ℝ)^n := by rw [div_pow, one_pow]
    rw [h2]
    first
      | (field_simp; ring)
      | field_simp
      | ring
  have hg : HasSum (fun n : ℕ => ((n:ℝ)/(2:ℝ)^n) * ((n:ℝ)*(y:ℝ)/(x:ℝ)))
      (6 * (y:ℝ) / (x:ℝ)) := by
    have hfun : (fun n : ℕ => ((n:ℝ)/(2:ℝ)^n) * ((n:ℝ)*(y:ℝ)/(x:ℝ)))
        = (fun n : ℕ => ((y:ℝ)/(x:ℝ)) * ((n:ℝ)^2 * (1/2:ℝ)^n)) := funext hgeq
    rw [hfun, show 6 * (y:ℝ) / (x:ℝ) = ((y:ℝ)/(x:ℝ)) * 6 from by ring]
    exact hasSum6.mul_left _
  by_contra hdvd
  have hFsummable : Summable (fun n : ℕ =>
      ((n : ℝ) / (2 : ℝ) ^ n) * (Int.floor ((n : ℝ) * (y : ℝ) / (x : ℝ)) : ℝ)) := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at h
    linarith
  have hFhas : HasSum (fun n : ℕ =>
      ((n : ℝ) / (2 : ℝ) ^ n) * (Int.floor ((n : ℝ) * (y : ℝ) / (x : ℝ)) : ℝ))
      (6 * (y:ℝ) / (x:ℝ)) := by
    rw [← h]
    exact hFsummable.hasSum
  have hle : ∀ n : ℕ, ((n : ℝ) / (2 : ℝ) ^ n) * (Int.floor ((n : ℝ) * (y : ℝ) / (x : ℝ)) : ℝ)
      ≤ ((n:ℝ)/(2:ℝ)^n) * ((n:ℝ)*(y:ℝ)/(x:ℝ)) := by
    intro n
    have hc : (0:ℝ) ≤ (n:ℝ)/(2:ℝ)^n := by positivity
    exact mul_le_mul_of_nonneg_left (Int.floor_le _) hc
  have hD : HasSum (fun n : ℕ => ((n:ℝ)/(2:ℝ)^n) * ((n:ℝ)*(y:ℝ)/(x:ℝ))
      - ((n : ℝ) / (2 : ℝ) ^ n) * (Int.floor ((n : ℝ) * (y : ℝ) / (x : ℝ)) : ℝ)) 0 := by
    have h' := hg.sub hFhas
    rw [sub_self] at h'
    exact h'
  have hDnn : ∀ b : ℕ, b ≠ 1 → 0 ≤ ((b:ℝ)/(2:ℝ)^b) * ((b:ℝ)*(y:ℝ)/(x:ℝ))
      - ((b : ℝ) / (2 : ℝ) ^ b) * (Int.floor ((b : ℝ) * (y : ℝ) / (x : ℝ)) : ℝ) :=
    fun b _ => sub_nonneg.mpr (hle b)
  have hkey' : ((1:ℕ):ℝ)/(2:ℝ)^(1:ℕ) * (((1:ℕ):ℝ)*(y:ℝ)/(x:ℝ))
      - ((1:ℕ):ℝ)/(2:ℝ)^(1:ℕ) * ((Int.floor (((1:ℕ):ℝ)*(y:ℝ)/(x:ℝ)) : ℤ) : ℝ) ≤ 0 :=
    le_hasSum hD 1 hDnn
  have hfl : ((Int.floor ((y:ℝ)/(x:ℝ)) : ℤ) : ℝ) < (y:ℝ)/(x:ℝ) := by
    rcases eq_or_lt_of_le (Int.floor_le ((y:ℝ)/(x:ℝ))) with heq | hlt
    · exfalso
      apply hdvd
      have hmx : ((Int.floor ((y:ℝ)/(x:ℝ)) : ℤ) : ℝ) * (x:ℝ) = (y:ℝ) := by
        rw [heq]
        field_simp
      have hy' : (y:ℝ) = (x:ℝ) * ((Int.floor ((y:ℝ)/(x:ℝ)) : ℤ) : ℝ) := by
        linarith [hmx]
      have hdvdZ : (x:ℤ) ∣ (y:ℤ) := ⟨Int.floor ((y:ℝ)/(x:ℝ)), by exact_mod_cast hy'⟩
      exact_mod_cast hdvdZ
    · exact hlt
  have harg : ((1:ℕ):ℝ) * (y:ℝ) / (x:ℝ) = (y:ℝ)/(x:ℝ) := by norm_num
  have hstrict : ((1:ℕ):ℝ)/(2:ℝ)^(1:ℕ) * ((Int.floor (((1:ℕ):ℝ)*(y:ℝ)/(x:ℝ)) : ℤ) : ℝ)
      < ((1:ℕ):ℝ)/(2:ℝ)^(1:ℕ) * (((1:ℕ):ℝ)*(y:ℝ)/(x:ℝ)) := by
    have hc : (0:ℝ) < ((1:ℕ):ℝ)/(2:ℝ)^(1:ℕ) := by norm_num
    refine mul_lt_mul_of_pos_left ?_ hc
    rw [harg]
    exact hfl
  linarith [hkey', hstrict]
```
