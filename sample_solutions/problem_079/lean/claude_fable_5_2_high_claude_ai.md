# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `15 November 2026`\
Line count: `234`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem floor_ceil_eq_fourth_root (x : ℝ) :
    (⌊x * ⌊x⌋⌋ : ℝ) - (⌈x * ⌈x⌉⌉ : ℝ) ^ 3 = x ^ 4 - 31 ↔ x = (5 : ℝ) ^ ((1 : ℝ) / 4) := by
  -- Basic facts about the fourth root of 5.
  have hy0 : (0 : ℝ) < (5 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hy4 : ((5 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num
  -- Positive fourth roots of 5 are unique.
  have huniq : ∀ z y : ℝ, 0 < z → 0 < y → z ^ 4 = 5 → y ^ 4 = 5 → z = y := by
    intro z y hz hy hz4 hy4'
    have hfac : (z - y) * ((z + y) * (z ^ 2 + y ^ 2)) = z ^ 4 - y ^ 4 := by ring
    have h1 : (z - y) * ((z + y) * (z ^ 2 + y ^ 2)) = 0 := by rw [hfac]; linarith
    have h2 : 0 < (z + y) * (z ^ 2 + y ^ 2) :=
      mul_pos (by linarith) (by linarith [pow_pos hz 2, sq_nonneg y])
    rcases mul_eq_zero.mp h1 with h3 | h3
    · linarith
    · exfalso; linarith
  -- Forward direction, with the floors and ceilings abstracted to integers.
  have key : ∀ (m n a b : ℤ), (m : ℝ) ≤ x → x < (m : ℝ) + 1 → x ≤ (n : ℝ) → (n : ℝ) < x + 1 →
      (a : ℝ) ≤ x * (m : ℝ) → x * (m : ℝ) < (a : ℝ) + 1 →
      x * (n : ℝ) ≤ (b : ℝ) → (b : ℝ) < x * (n : ℝ) + 1 →
      (a : ℝ) - (b : ℝ) ^ 3 = x ^ 4 - 31 → x ^ 4 = 5 ∧ 0 < x := by
    intro m n a b hm1 hm2 hn1 hn2 ha1 ha2 hb1 hb2 h
    by_cases hA : 2 ≤ x
    · -- Case 2 ≤ x : b ^ 3 ≥ 64 is too large.
      exfalso
      have hn2' : (2 : ℝ) ≤ (n : ℝ) := le_trans hA hn1
      have h1 : 4 ≤ x * (n : ℝ) := by
        linarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hn2')]
      have hb4 : (4 : ℝ) ≤ (b : ℝ) := le_trans h1 hb1
      have hb3 : (64 : ℝ) ≤ (b : ℝ) ^ 3 := by
        linarith [mul_nonneg (sub_nonneg.mpr hb4) (sq_nonneg ((b : ℝ) + 2))]
      have h2 : x * (m : ℝ) ≤ x ^ 2 := by
        linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x) (sub_nonneg.mpr hm1)]
      have h3 : (4 : ℝ) ≤ x ^ 2 := by
        linarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hA)]
      have h4 : x ^ 2 + 12 ≤ x ^ 4 := by
        linarith [mul_nonneg (sub_nonneg.mpr h3) (by positivity : (0 : ℝ) ≤ x ^ 2 + 3)]
      linarith
    have hA' : x < 2 := not_le.mp hA
    by_cases hB : 1 < x
    · -- Case 1 < x < 2 : ⌊x⌋ = 1, ⌈x⌉ = 2, a = 1, b ∈ {3, 4}.
      have hm : m = 1 := by
        have h1 : (m : ℝ) < 2 := by linarith
        have h2 : (0 : ℝ) < (m : ℝ) := by linarith
        have h1' : m < 2 := by exact_mod_cast h1
        have h2' : 0 < m := by exact_mod_cast h2
        omega
      have hn : n = 2 := by
        have h1 : (n : ℝ) < 3 := by linarith
        have h2 : (1 : ℝ) < (n : ℝ) := by linarith
        have h1' : n < 3 := by exact_mod_cast h1
        have h2' : 1 < n := by exact_mod_cast h2
        omega
      have hmR : (m : ℝ) = 1 := by exact_mod_cast hm
      have hnR : (n : ℝ) = 2 := by exact_mod_cast hn
      rw [hmR] at ha1 ha2
      rw [hnR] at hb1 hb2
      have ha : a = 1 := by
        have h1 : (a : ℝ) < 2 := by linarith
        have h2 : (0 : ℝ) < (a : ℝ) := by linarith
        have h1' : a < 2 := by exact_mod_cast h1
        have h2' : 0 < a := by exact_mod_cast h2
        omega
      have hb : b = 3 ∨ b = 4 := by
        have h1 : (b : ℝ) < 5 := by linarith
        have h2 : (2 : ℝ) < (b : ℝ) := by linarith
        have h1' : b < 5 := by exact_mod_cast h1
        have h2' : 2 < b := by exact_mod_cast h2
        omega
      have haR : (a : ℝ) = 1 := by exact_mod_cast ha
      rcases hb with hb | hb
      · have hbR : (b : ℝ) = 3 := by exact_mod_cast hb
        have hb3 : (b : ℝ) ^ 3 = 27 := by rw [hbR]; norm_num
        exact ⟨by linarith, by linarith⟩
      · have hbR : (b : ℝ) = 4 := by exact_mod_cast hb
        have hb3 : (b : ℝ) ^ 3 = 64 := by rw [hbR]; norm_num
        have hpos : (0 : ℝ) ≤ x ^ 4 := by positivity
        exfalso; linarith
    have hB' : x ≤ 1 := not_lt.mp hB
    by_cases hC : 0 ≤ x
    · -- Case 0 ≤ x ≤ 1 : the left side is > -29, the right side is ≤ -30.
      exfalso
      have h1 : -(1 / 4 : ℝ) ≤ x * (m : ℝ) := by
        linarith [mul_nonneg hC (by linarith : (0 : ℝ) ≤ (m : ℝ) - x + 1),
          sq_nonneg (x - 1 / 2)]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_trans hC hn1
      have h2 : 0 ≤ x * (n : ℝ) := mul_nonneg hC hn0
      have h3 : x * (n : ℝ) ≤ 2 := by
        linarith [mul_nonneg (sub_nonneg.mpr hB') hn0]
      have hb0 : (0 : ℝ) ≤ (b : ℝ) := le_trans h2 hb1
      have hb3 : (b : ℝ) < 3 := by linarith
      have hq : (0 : ℝ) < (b : ℝ) ^ 2 + 3 * (b : ℝ) + 9 := by
        linarith [sq_nonneg ((b : ℝ) + 3 / 2)]
      have hbc : (b : ℝ) ^ 3 < 27 := by
        linarith [mul_pos (sub_pos.mpr hb3) hq]
      have hx2 : x ^ 2 ≤ 1 := by
        linarith [mul_nonneg (sub_nonneg.mpr hB') hC]
      have hx4 : x ^ 4 ≤ 1 := by
        linarith [mul_nonneg (sub_nonneg.mpr hx2) (sq_nonneg x)]
      linarith
    have hC' : x < 0 := not_le.mp hC
    by_cases hD : -1 ≤ x
    · -- Case -1 ≤ x < 0.
      exfalso
      have h1 : 0 ≤ x * (m : ℝ) := by
        linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -x) (by linarith : (0 : ℝ) ≤ -(m : ℝ))]
      have hx2 : x ^ 2 ≤ 1 := by
        linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x + 1) (by linarith : (0 : ℝ) ≤ -x)]
      have h3 : x * (n : ℝ) ≤ 1 := by
        linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -x) (sub_nonneg.mpr hn1)]
      have hb2' : (b : ℝ) < 2 := by linarith
      have hq : (0 : ℝ) < (b : ℝ) ^ 2 + 2 * (b : ℝ) + 4 := by
        linarith [sq_nonneg ((b : ℝ) + 1)]
      have hbc : (b : ℝ) ^ 3 < 8 := by
        linarith [mul_pos (sub_pos.mpr hb2') hq]
      have hx4 : x ^ 4 ≤ 1 := by
        linarith [mul_nonneg (sub_nonneg.mpr hx2) (sq_nonneg x)]
      linarith
    have hD' : x < -1 := not_le.mp hD
    by_cases hE : -2 < x
    · -- Case -2 < x < -1 : ⌈x⌉ = -1, b = 2, forcing x ^ 4 > 22.
      exfalso
      have hn : n = -1 := by
        have h1 : (n : ℝ) < 0 := by linarith
        have h2 : (-2 : ℝ) < (n : ℝ) := by linarith
        have h1' : n < 0 := by exact_mod_cast h1
        have h2' : -2 < n := by exact_mod_cast h2
        omega
      have hnR : (n : ℝ) = -1 := by exact_mod_cast hn
      rw [hnR] at hb1 hb2
      have hb : b = 2 := by
        have h1 : (b : ℝ) < 3 := by linarith
        have h2 : (1 : ℝ) < (b : ℝ) := by linarith
        have h1' : b < 3 := by exact_mod_cast h1
        have h2' : 1 < b := by exact_mod_cast h2
        omega
      have hbR : (b : ℝ) = 2 := by exact_mod_cast hb
      have hb3 : (b : ℝ) ^ 3 = 8 := by rw [hbR]; norm_num
      have h1 : 0 ≤ x * (m : ℝ) := by
        linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -x) (by linarith : (0 : ℝ) ≤ -(m : ℝ))]
      have hx2 : x ^ 2 < 4 := by
        linarith [mul_pos (by linarith : (0 : ℝ) < x + 2) (by linarith : (0 : ℝ) < -x)]
      have hx4 : x ^ 4 < 16 := by
        linarith [mul_pos (sub_pos.mpr hx2) (by positivity : (0 : ℝ) < x ^ 2 + 4)]
      linarith
    have hE' : x ≤ -2 := not_lt.mp hE
    -- Case x ≤ -2 : b ≥ 3, and b ^ 3 ≥ 27 is too large.
    exfalso
    have h1 : 2 < x * (n : ℝ) := by
      linarith [mul_pos (by linarith : (0 : ℝ) < -x) (by linarith : (0 : ℝ) < x + 1 - (n : ℝ)),
        mul_nonneg (by linarith : (0 : ℝ) ≤ -(x + 2)) (by linarith : (0 : ℝ) ≤ -(x - 1))]
    have hb3 : (3 : ℝ) ≤ (b : ℝ) := by
      have h2 : (2 : ℝ) < (b : ℝ) := lt_of_lt_of_le h1 hb1
      have h2' : (2 : ℤ) < b := by exact_mod_cast h2
      have h3 : (3 : ℤ) ≤ b := by omega
      exact_mod_cast h3
    have hq : (0 : ℝ) ≤ (b : ℝ) ^ 2 + 3 * (b : ℝ) + 9 := by
      linarith [sq_nonneg ((b : ℝ) + 3 / 2)]
    have hbc : (27 : ℝ) ≤ (b : ℝ) ^ 3 := by
      linarith [mul_nonneg (sub_nonneg.mpr hb3) hq]
    have h2 : x * (m : ℝ) < x ^ 2 - x := by
      linarith [mul_pos (by linarith : (0 : ℝ) < -x) (by linarith : (0 : ℝ) < (m : ℝ) - x + 1)]
    have hx2 : (4 : ℝ) ≤ x ^ 2 := by
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -x - 2) (by linarith : (0 : ℝ) ≤ -x + 2)]
    have hx4 : 4 * x ^ 2 ≤ x ^ 4 := by
      linarith [mul_nonneg (sub_nonneg.mpr hx2) (sq_nonneg x)]
    have h5 : 0 ≤ 3 * x ^ 2 + x - 4 := by
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -(3 * x + 4)) (by linarith : (0 : ℝ) ≤ -(x - 1))]
    linarith
  -- Reverse direction, again with the floors and ceilings abstracted.
  have key2 : ∀ (m n a b : ℤ), (m : ℝ) ≤ x → x < (m : ℝ) + 1 → x ≤ (n : ℝ) → (n : ℝ) < x + 1 →
      (a : ℝ) ≤ x * (m : ℝ) → x * (m : ℝ) < (a : ℝ) + 1 →
      x * (n : ℝ) ≤ (b : ℝ) → (b : ℝ) < x * (n : ℝ) + 1 →
      x ^ 4 = 5 → 0 < x → (a : ℝ) - (b : ℝ) ^ 3 = x ^ 4 - 31 := by
    intro m n a b hm1 hm2 hn1 hn2 ha1 ha2 hb1 hb2 hx4 hx0
    have hx1 : 1 < x := by
      by_contra hcon
      have hle : x ≤ 1 := not_lt.mp hcon
      have hx2 : x ^ 2 ≤ 1 := by
        linarith [mul_nonneg (sub_nonneg.mpr hle) hx0.le]
      linarith [mul_nonneg (sub_nonneg.mpr hx2) (sq_nonneg x)]
    have hx32 : x ≤ 3 / 2 := by
      by_contra hcon
      have hgt : 3 / 2 < x := not_le.mp hcon
      have hx2 : 9 / 4 < x ^ 2 := by
        linarith [mul_pos (sub_pos.mpr hgt) (by linarith : (0 : ℝ) < x + 3 / 2)]
      linarith [mul_pos (sub_pos.mpr hx2) (by positivity : (0 : ℝ) < x ^ 2 + 9 / 4)]
    have hm : m = 1 := by
      have h1 : (m : ℝ) < 2 := by linarith
      have h2 : (0 : ℝ) < (m : ℝ) := by linarith
      have h1' : m < 2 := by exact_mod_cast h1
      have h2' : 0 < m := by exact_mod_cast h2
      omega
    have hn : n = 2 := by
      have h1 : (n : ℝ) < 3 := by linarith
      have h2 : (1 : ℝ) < (n : ℝ) := by linarith
      have h1' : n < 3 := by exact_mod_cast h1
      have h2' : 1 < n := by exact_mod_cast h2
      omega
    have hmR : (m : ℝ) = 1 := by exact_mod_cast hm
    have hnR : (n : ℝ) = 2 := by exact_mod_cast hn
    rw [hmR] at ha1 ha2
    rw [hnR] at hb1 hb2
    have ha : a = 1 := by
      have h1 : (a : ℝ) < 2 := by linarith
      have h2 : (0 : ℝ) < (a : ℝ) := by linarith
      have h1' : a < 2 := by exact_mod_cast h1
      have h2' : 0 < a := by exact_mod_cast h2
      omega
    have hb : b = 3 := by
      have h1 : (b : ℝ) < 4 := by linarith
      have h2 : (2 : ℝ) < (b : ℝ) := by linarith
      have h1' : b < 4 := by exact_mod_cast h1
      have h2' : 2 < b := by exact_mod_cast h2
      omega
    have haR : (a : ℝ) = 1 := by exact_mod_cast ha
    have hbR : (b : ℝ) = 3 := by exact_mod_cast hb
    have hb3 : (b : ℝ) ^ 3 = 27 := by rw [hbR]; norm_num
    linarith
  constructor
  · intro h
    have hx := key ⌊x⌋ ⌈x⌉ ⌊x * ⌊x⌋⌋ ⌈x * ⌈x⌉⌉ (Int.floor_le _) (Int.lt_floor_add_one _)
      (Int.le_ceil _) (Int.ceil_lt_add_one _) (Int.floor_le _) (Int.lt_floor_add_one _)
      (Int.le_ceil _) (Int.ceil_lt_add_one _) h
    exact huniq x _ hx.2 hy0 hx.1 hy4
  · intro hx
    have hx0 : 0 < x := by rw [hx]; exact hy0
    have hx4 : x ^ 4 = 5 := by rw [hx]; exact hy4
    exact key2 ⌊x⌋ ⌈x⌉ ⌊x * ⌊x⌋⌋ ⌈x * ⌈x⌉⌉ (Int.floor_le _) (Int.lt_floor_add_one _)
      (Int.le_ceil _) (Int.ceil_lt_add_one _) (Int.floor_le _) (Int.lt_floor_add_one _)
      (Int.le_ceil _) (Int.ceil_lt_add_one _) hx4 hx0
```
