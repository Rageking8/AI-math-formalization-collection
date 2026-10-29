# GPT-5.5 High (Arena AI)

Model: `gpt-5.5-high` (via Arena AI)\
Date: `18 July 2026`\
Line count: `138`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem sin_mul_upper_bound
    (x y z : ℝ)
    (h : x + y + z = Real.pi) :
    Real.sin x * Real.sin y * Real.sin z ≤
      (3 * Real.sqrt 3) / 8 := by
  have hSle_trig :
      Real.sin x ^ 2 + Real.sin y ^ 2 + Real.sin z ^ 2 ≤ (9 : ℝ) / 4 := by
    have hz : z = Real.pi - (x + y) := by linarith
    rw [hz, Real.sin_pi_sub]
    let c : ℝ := Real.cos (x + y)
    let d : ℝ := Real.cos (x - y)
    have hxy : Real.sin x ^ 2 + Real.sin y ^ 2 = 1 - c * d := by
      have hcx : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
        have hx0 := Real.sin_sq_add_cos_sq x
        nlinarith
      have hcy : Real.cos y ^ 2 = 1 - Real.sin y ^ 2 := by
        have hy0 := Real.sin_sq_add_cos_sq y
        nlinarith
      dsimp [c, d]
      rw [Real.cos_add, Real.cos_sub]
      ring_nf
      rw [hcx, hcy]
      ring
    have hu : Real.sin (x + y) ^ 2 = 1 - c ^ 2 := by
      dsimp [c]
      have h0 := Real.sin_sq_add_cos_sq (x + y)
      nlinarith
    have hd : |d| ≤ 1 := by
      dsimp [d]
      exact Real.abs_cos_le_one (x - y)
    have hcd : -c * d ≤ |c| := by
      calc
        -c * d ≤ |(-c) * d| := le_abs_self _
        _ = |c| * |d| := by rw [abs_mul, abs_neg]
        _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left hd (abs_nonneg c)
        _ = |c| := by ring
    have hquad : 2 + |c| - c ^ 2 ≤ (9 : ℝ) / 4 := by
      have hsq : 0 ≤ (|c| - (1 : ℝ) / 2) ^ 2 := sq_nonneg _
      have hsqa : |c| ^ 2 = c ^ 2 := by simpa using (sq_abs c)
      nlinarith
    calc
      Real.sin x ^ 2 + Real.sin y ^ 2 + Real.sin (x + y) ^ 2
          = (1 - c * d) + (1 - c ^ 2) := by rw [hxy, hu]
      _ = 2 - c * d - c ^ 2 := by ring
      _ ≤ 2 + |c| - c ^ 2 := by nlinarith [hcd]
      _ ≤ (9 : ℝ) / 4 := hquad

  have amgm3 :
      ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
        27 * a * b * c ≤ (a + b + c) ^ 3 := by
    intro a b c ha hb hc
    let S : ℝ := a + b + c
    let Q : ℝ := a * b + b * c + c * a
    have hS : 0 ≤ S := by
      dsimp [S]
      nlinarith
    have h1 : 3 * Q ≤ S ^ 2 := by
      dsimp [S, Q]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h2 : 9 * a * b * c ≤ S * Q := by
      have hca : 0 ≤ c * (a - b) ^ 2 := mul_nonneg hc (sq_nonneg (a - b))
      have hab : 0 ≤ a * (b - c) ^ 2 := mul_nonneg ha (sq_nonneg (b - c))
      have hbc : 0 ≤ b * (c - a) ^ 2 := mul_nonneg hb (sq_nonneg (c - a))
      dsimp [S, Q]
      nlinarith [hca, hab, hbc]
    have h3 : 3 * S * Q ≤ S ^ 3 := by
      have hm := mul_le_mul_of_nonneg_left h1 hS
      nlinarith [hm]
    have h4 : 27 * a * b * c ≤ 3 * S * Q := by
      nlinarith [h2]
    exact le_trans h4 h3

  let a : ℝ := Real.sin x ^ 2
  let b : ℝ := Real.sin y ^ 2
  let c : ℝ := Real.sin z ^ 2
  let S : ℝ := a + b + c
  let p : ℝ := Real.sin x * Real.sin y * Real.sin z
  let B : ℝ := (3 * Real.sqrt 3) / 8

  have ha : 0 ≤ a := by
    dsimp [a]
    exact sq_nonneg _
  have hb : 0 ≤ b := by
    dsimp [b]
    exact sq_nonneg _
  have hc : 0 ≤ c := by
    dsimp [c]
    exact sq_nonneg _

  have hS_nonneg : 0 ≤ S := by
    dsimp [S, a, b, c]
    nlinarith [sq_nonneg (Real.sin x), sq_nonneg (Real.sin y), sq_nonneg (Real.sin z)]
  have hS_le : S ≤ (9 : ℝ) / 4 := by
    dsimp [S, a, b, c]
    exact hSle_trig
  have hS_pow_le : S ^ 3 ≤ ((9 : ℝ) / 4) ^ 3 :=
    pow_le_pow_left₀ hS_nonneg hS_le 3

  have hamgm_bound : 27 * a * b * c ≤ S ^ 3 := by
    simpa [S] using amgm3 a b c ha hb hc
  have hp2_eq : p ^ 2 = a * b * c := by
    dsimp [p, a, b, c]
    ring
  have hp2S : 27 * p ^ 2 ≤ S ^ 3 := by
    calc
      27 * p ^ 2 = 27 * a * b * c := by
        rw [hp2_eq]
        ring
      _ ≤ S ^ 3 := hamgm_bound
  have hp2_num : p ^ 2 ≤ (27 : ℝ) / 64 := by
    have htmp : 27 * p ^ 2 ≤ ((9 : ℝ) / 4) ^ 3 := le_trans hp2S hS_pow_le
    norm_num at htmp ⊢
    nlinarith

  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hB_sq : B ^ 2 = (27 : ℝ) / 64 := by
    dsimp [B]
    have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = (3 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  have hp2B : p ^ 2 ≤ B ^ 2 := by
    rw [hB_sq]
    exact hp2_num

  have hp_le_B : p ≤ B := by
    by_contra hnot
    have hlt : B < p := lt_of_not_ge hnot
    have hpos1 : 0 < p - B := sub_pos.mpr hlt
    have hpos2 : 0 < p + B := by nlinarith [hB_nonneg, hlt]
    have hprod : 0 < (p - B) * (p + B) := mul_pos hpos1 hpos2
    have hsq_lt : B ^ 2 < p ^ 2 := by nlinarith [hprod]
    exact (not_lt_of_ge hp2B) hsq_lt

  simpa [p, B] using hp_le_B
```
