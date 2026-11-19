# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `15 November 2026`\
Line count: `152`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem infinite_product_cos_fract :
    Filter.Tendsto (fun N => ∏ n ∈ Finset.Icc 1 N,
      (1 + 2 * Real.cos (Real.pi * Int.fract (25 / (2 * (3 : ℝ) ^ n) -
      Int.fract (16 / (2 * (3 : ℝ) ^ n))))) / 3)
      Filter.atTop (nhds ((2 * Real.sqrt 2) / (9 * Real.pi))) := by
  set f : ℕ → ℝ := fun n => (1 + 2 * Real.cos (Real.pi * Int.fract (25 / (2 * (3 : ℝ) ^ n) -
      Int.fract (16 / (2 * (3 : ℝ) ^ n))))) / 3 with hf
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  -- the first two factors are 1/3
  have h1 : f 1 = 1 / 3 := by
    have e1 : Int.fract (16 / (2 * (3 : ℝ) ^ 1)) = 2 / 3 := by
      rw [Int.fract_eq_iff]
      exact ⟨by norm_num, by norm_num, 2, by norm_num⟩
    have e2 : Int.fract (25 / (2 * (3 : ℝ) ^ 1) - 2 / 3) = 1 / 2 := by
      rw [Int.fract_eq_iff]
      exact ⟨by norm_num, by norm_num, 3, by norm_num⟩
    simp only [hf, e1, e2]
    rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.cos_pi_div_two]
    norm_num
  have h2 : f 2 = 1 / 3 := by
    have e1 : Int.fract (16 / (2 * (3 : ℝ) ^ 2)) = 8 / 9 := by
      rw [Int.fract_eq_iff]
      exact ⟨by norm_num, by norm_num, 0, by norm_num⟩
    have e2 : Int.fract (25 / (2 * (3 : ℝ) ^ 2) - 8 / 9) = 1 / 2 := by
      rw [Int.fract_eq_iff]
      exact ⟨by norm_num, by norm_num, 0, by norm_num⟩
    simp only [hf, e1, e2]
    rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.cos_pi_div_two]
    norm_num
  have hpos : ∀ k : ℕ, 0 < Real.sin (Real.pi / (4 * 3 ^ k)) := by
    intro k
    have hk : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    apply Real.sin_pos_of_pos_of_le_one (by positivity)
    rw [div_le_one (by positivity)]
    nlinarith
  -- from n = 3 on, the factor telescopes
  have h3 : ∀ k : ℕ, f (k + 3) =
      Real.sin (Real.pi / (4 * 3 ^ k)) / (3 * Real.sin (Real.pi / (4 * 3 ^ (k + 1)))) := by
    intro k
    have hk : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    have hk0 : (0 : ℝ) < 3 ^ k := by positivity
    have e1 : Int.fract (16 / (2 * (3 : ℝ) ^ (k + 3))) = 16 / (2 * (3 : ℝ) ^ (k + 3)) := by
      rw [Int.fract_eq_self]
      constructor
      · positivity
      · rw [div_lt_one (by positivity), pow_add]
        nlinarith
    have e2 : Int.fract (25 / (2 * (3 : ℝ) ^ (k + 3)) - 16 / (2 * (3 : ℝ) ^ (k + 3)))
        = 1 / (6 * 3 ^ k) := by
      have : 25 / (2 * (3 : ℝ) ^ (k + 3)) - 16 / (2 * (3 : ℝ) ^ (k + 3)) = 1 / (6 * 3 ^ k) := by
        rw [pow_add]
        field_simp
        norm_num
      rw [this, Int.fract_eq_self]
      constructor
      · positivity
      · rw [div_lt_one (by positivity)]
        linarith
    simp only [hf, e1, e2]
    have hs := hpos (k + 1)
    set x : ℝ := Real.pi / (4 * 3 ^ (k + 1)) with hx
    have a1 : Real.pi * (1 / (6 * 3 ^ k)) = 2 * x := by
      rw [hx, pow_succ]
      field_simp
      ring
    have a2 : Real.pi / (4 * 3 ^ k) = 3 * x := by
      rw [hx, pow_succ]
      field_simp
    rw [a1, a2, Real.sin_three_mul, Real.cos_two_mul_eq_one_sub]
    field_simp
    ring
  have hsin4 : Real.sin (Real.pi / 4) ≠ 0 := by
    rw [Real.sin_pi_div_four]
    positivity
  -- closed form of the partial products
  have hprod : ∀ k : ℕ, ∏ n ∈ Finset.Icc 1 (k + 2), f n =
      (1 / 9) * (Real.sin (Real.pi / 4) / (3 ^ k * Real.sin (Real.pi / (4 * 3 ^ k)))) := by
    intro k
    induction k with
    | zero =>
      have h2' : f (1 + 1) = 1 / 3 := h2
      show ∏ n ∈ Finset.Icc 1 (1 + 1), f n = _
      rw [Finset.prod_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.prod_singleton, h1, h2',
        pow_zero, mul_one, one_mul, div_self hsin4]
      norm_num
    | succ k ih =>
      have hs0 := hpos k
      have hs1 := hpos (k + 1)
      rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.prod_Icc_succ_top (by omega), ih,
        show k + 2 + 1 = k + 3 by ring, h3 k]
      field_simp
      ring
  -- 3^k sin(π / (4·3^k)) → π/4
  have hlim : Filter.Tendsto (fun k : ℕ => (3 : ℝ) ^ k * Real.sin (Real.pi / (4 * 3 ^ k)))
      Filter.atTop (nhds (Real.pi / 4)) := by
    have hz : Filter.Tendsto
        (fun k : ℕ => (3 : ℝ) ^ k * Real.sin (Real.pi / (4 * 3 ^ k)) - Real.pi / 4)
        Filter.atTop (nhds 0) := by
      apply squeeze_zero_norm (a := fun k : ℕ => ((1 : ℝ) / 9) ^ k)
      · intro k
        have hk0 : (0 : ℝ) < 3 ^ k := by positivity
        have hk : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
        set x : ℝ := Real.pi / (4 * 3 ^ k) with hx
        have hxpos : 0 < x := by positivity
        have hx1 : x ≤ 1 := by
          rw [hx, div_le_one (by positivity)]
          nlinarith
        have hb := Real.sin_bound (x := x) (by rw [abs_of_pos hxpos]; exact hx1)
        rw [abs_of_pos hxpos] at hb
        have hb' := abs_le.mp hb
        have e : (3 : ℝ) ^ k * Real.sin x - Real.pi / 4 = 3 ^ k * (Real.sin x - x) := by
          rw [hx]
          field_simp
        have hx5 : x ^ 5 ≤ x ^ 3 := pow_le_pow_of_le_one hxpos.le hx1 (by norm_num)
        have hx3 : 0 < x ^ 3 := by positivity
        have habs : |Real.sin x - x| ≤ x ^ 3 := by
          rw [abs_le]
          constructor <;> linarith [hb'.1, hb'.2]
        have hy : x ^ 3 = (Real.pi / 4) ^ 3 / (3 ^ k) ^ 3 := by
          rw [hx]
          field_simp
        have h9 : ((1 : ℝ) / 9) ^ k = 1 / (3 ^ k) ^ 2 := by
          rw [one_div_pow, ← pow_mul, mul_comm, pow_mul]
          norm_num
        have hq : (Real.pi / 4) ^ 3 ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
        rw [Real.norm_eq_abs, e, abs_mul, abs_of_pos hk0]
        calc (3 : ℝ) ^ k * |Real.sin x - x| ≤ 3 ^ k * x ^ 3 :=
              mul_le_mul_of_nonneg_left habs hk0.le
          _ = (Real.pi / 4) ^ 3 / (3 ^ k) ^ 2 := by
              rw [hy]
              field_simp
          _ ≤ 1 / (3 ^ k) ^ 2 := by gcongr
          _ = (1 / 9) ^ k := h9.symm
      · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have := hz.add_const (Real.pi / 4)
    simpa using this
  have hmain : Filter.Tendsto (fun k : ℕ => ∏ n ∈ Finset.Icc 1 (k + 2), f n) Filter.atTop
      (nhds ((2 * Real.sqrt 2) / (9 * Real.pi))) := by
    have h := (tendsto_const_nhds (x := Real.sin (Real.pi / 4))).div hlim
      (by positivity : Real.pi / 4 ≠ 0)
    have h' := h.const_mul (1 / 9 : ℝ)
    have hval : (1 / 9 : ℝ) * (Real.sin (Real.pi / 4) / (Real.pi / 4))
        = (2 * Real.sqrt 2) / (9 * Real.pi) := by
      rw [Real.sin_pi_div_four]
      field_simp
      ring
    rw [← hval]
    exact h'.congr fun k => (hprod k).symm
  exact (Filter.tendsto_add_atTop_iff_nat 2).mp hmain
```
