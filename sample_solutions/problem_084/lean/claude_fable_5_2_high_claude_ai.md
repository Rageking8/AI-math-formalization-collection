# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `13 November 2026`\
Line count: `294`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem floor_ceil_fract_system_unique_solution (x y : ℝ) :
    (Int.ceil (3 * (Int.floor x : ℝ) * y ^ 2) +
      (Int.floor (y * (Int.floor (x ^ 4) : ℝ))) ^ 2 = 5 ∧
      ∃ k : ℤ, Int.fract x - 3 * y ^ 2 = 5 * (k : ℝ) + 1) ↔
      (x = 1 ∧ y = 2 / Real.sqrt 3) := by
  constructor
  · rintro ⟨h1, k, h2⟩
    have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
    have hf1 : Int.fract x < 1 := Int.fract_lt_one x
    have hxf : x = (⌊x⌋ : ℝ) + Int.fract x := (Int.floor_add_fract x).symm
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ⌊x⌋ = n := ⟨_, rfl⟩
    obtain ⟨f, hf⟩ : ∃ f : ℝ, Int.fract x = f := ⟨_, rfl⟩
    obtain ⟨N, hN⟩ : ∃ N : ℤ, ⌊x ^ 4⌋ = N := ⟨_, rfl⟩
    rw [hn, hN] at h1
    rw [hf] at h2 hf0 hf1 hxf
    rw [hn] at hxf
    obtain ⟨c, hc⟩ : ∃ c : ℤ, ⌈3 * (n : ℝ) * y ^ 2⌉ = c := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : ℤ, ⌊y * (N : ℝ)⌋ = s := ⟨_, rfl⟩
    rw [hc, hs] at h1
    have hc1 : (c : ℝ) - 1 < 3 * n * y ^ 2 := (Int.ceil_eq_iff.mp hc).1
    have hc2 : 3 * (n : ℝ) * y ^ 2 ≤ c := (Int.ceil_eq_iff.mp hc).2
    have hs1 : (s : ℝ) ≤ y * N := (Int.floor_eq_iff.mp hs).1
    have hs2 : y * N < s + 1 := (Int.floor_eq_iff.mp hs).2
    have hN1 : (N : ℝ) ≤ x ^ 4 := (Int.floor_eq_iff.mp hN).1
    have hN2 : x ^ 4 < N + 1 := (Int.floor_eq_iff.mp hN).2
    have h1r : (c : ℝ) + (s : ℝ) ^ 2 = 5 := by exact_mod_cast h1
    have hk : k ≤ -1 := by
      have h : (k : ℝ) < 0 := by linarith only [h2, hf1, sq_nonneg y]
      have h' : k < 0 := by exact_mod_cast h
      omega
    have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast hk
    have hy2 : 4 ≤ 3 * y ^ 2 := by linarith
    have hx4 : x ^ 4 = x ^ 2 * x ^ 2 := by ring
    have hs0 : (0 : ℝ) ≤ (s : ℝ) ^ 2 := sq_nonneg _
    obtain hn2 | hn1 | hn0 | hnneg : 2 ≤ n ∨ n = 1 ∨ n = 0 ∨ n ≤ -1 := by omega
    · -- ⌊x⌋ ≥ 2
      exfalso
      have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have h8 : (8 : ℝ) ≤ 3 * n * y ^ 2 := by
        linarith only [mul_nonneg (sub_nonneg.2 hnr) (sub_nonneg.2 hy2), hnr, hy2]
      linarith
    · -- ⌊x⌋ = 1
      have hnr : (n : ℝ) = 1 := by exact_mod_cast hn1
      rw [hnr] at hc1 hc2 hxf
      have hx1 : 1 ≤ x := by linarith
      have hx2 : 1 ≤ x ^ 2 := by nlinarith only [hx1]
      have hx41 : 1 ≤ x ^ 4 := by nlinarith only [hx2]
      have hNr : (0 : ℝ) < N := by linarith
      have hNz : 1 ≤ N := by
        have : 0 < N := by exact_mod_cast hNr
        omega
      have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hNz
      have hcr : (4 : ℝ) ≤ c := by linarith
      have hsq1 : (s : ℝ) ^ 2 ≤ 1 := by linarith
      have hsu : (s : ℝ) ≤ 1 := by nlinarith only [hsq1]
      have hsl : (-1 : ℝ) ≤ s := by nlinarith only [hsq1]
      have hsu' : s ≤ 1 := by exact_mod_cast hsu
      have hsl' : -1 ≤ s := by exact_mod_cast hsl
      have hyabs : 1 < y ^ 2 := by linarith
      obtain hsm | hsz | hsp : s = -1 ∨ s = 0 ∨ s = 1 := by omega
      · exfalso
        have hsr : (s : ℝ) = -1 := by exact_mod_cast hsm
        rw [hsr] at hs1 hs2
        have hyneg : y < 0 := by
          by_contra hcon
          rw [not_lt] at hcon
          linarith only [mul_nonneg hcon hNr.le, hs2]
        have hylt : y < -1 := by nlinarith only [hyneg, hyabs]
        nlinarith only [hs1, hylt, hNr1]
      · exfalso
        have hsr : (s : ℝ) = 0 := by exact_mod_cast hsz
        rw [hsr] at hs1 hs2
        have hypos : 0 ≤ y := by
          by_contra hcon
          rw [not_le] at hcon
          linarith only [mul_pos (neg_pos.2 hcon) hNr, hs1]
        have hygt : 1 < y := by nlinarith only [hypos, hyabs]
        nlinarith only [hs2, hygt, hNr1]
      · have hsr : (s : ℝ) = 1 := by exact_mod_cast hsp
        rw [hsr] at hs1 hs2 h1r
        have hc4 : (c : ℝ) = 4 := by linarith
        have hy3 : 3 * y ^ 2 = 4 := by linarith
        have hfz : f = 0 := by linarith
        have hx : x = 1 := by linarith
        refine ⟨hx, ?_⟩
        rw [hx] at hN1 hN2
        have hN1' : (N : ℝ) = 1 := by
          have h1 : (N : ℝ) ≤ 1 := by linarith
          linarith
        rw [hN1'] at hs1
        have hypos : 0 < y := by linarith
        have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
        rw [eq_div_iff h3p.ne']
        have hprod : 0 < y * Real.sqrt 3 := mul_pos hypos h3p
        have hsq : (y * Real.sqrt 3) ^ 2 = 2 ^ 2 := by
          rw [mul_pow, h3]; linarith only [hy3]
        nlinarith only [hsq, hprod]
    · -- ⌊x⌋ = 0
      exfalso
      have hnr : (n : ℝ) = 0 := by exact_mod_cast hn0
      rw [hnr] at hc1 hc2 hxf
      have hx0 : 0 ≤ x := by linarith
      have hx1 : x < 1 := by linarith
      have hx2 : x ^ 2 < 1 := by nlinarith only [hx0, hx1]
      have hx20 : 0 ≤ x ^ 2 := sq_nonneg x
      have hx41 : x ^ 4 < 1 := by nlinarith only [hx2, hx20]
      have hx40 : 0 ≤ x ^ 4 := by positivity
      have hNz : N = 0 := by
        have h1 : (N : ℝ) < 1 := by linarith
        have h2 : (-1 : ℝ) < N := by linarith
        have h1' : N < 1 := by exact_mod_cast h1
        have h2' : -1 < N := by exact_mod_cast h2
        omega
      have hNr : (N : ℝ) = 0 := by exact_mod_cast hNz
      rw [hNr] at hs1 hs2
      have hsz : s = 0 := by
        have h1 : (s : ℝ) ≤ 0 := by linarith
        have h2 : (-1 : ℝ) < s := by linarith
        have h1' : s ≤ 0 := by exact_mod_cast h1
        have h2' : -1 < s := by exact_mod_cast h2
        omega
      have hcz : c = 0 := by
        have h1 : (c : ℝ) < 1 := by linarith
        have h2 : (0 : ℝ) ≤ c := by linarith
        have h1' : c < 1 := by exact_mod_cast h1
        have h2' : 0 ≤ c := by exact_mod_cast h2
        omega
      rw [hsz, hcz] at h1
      norm_num at h1
    · -- ⌊x⌋ ≤ -1
      exfalso
      have hnr : (n : ℝ) ≤ -1 := by exact_mod_cast hnneg
      have hsl : 4 - 3 * n * y ^ 2 < (s : ℝ) ^ 2 := by linarith
      have hsu : (s : ℝ) ^ 2 ≤ 5 - 3 * n * y ^ 2 := by linarith
      have hy0 : y ≠ 0 := by
        rintro rfl
        norm_num at hy2
      -- the case `N = 1`, used twice
      have key1 : (N : ℝ) = 1 → False := by
        intro hN1'
        rw [hN1'] at hs1 hs2
        have hd0 : 0 ≤ y - s := by linarith
        have hd1 : y - s < 1 := by linarith
        have hd : (y - s) ^ 2 < 1 := by nlinarith only [hd0, hd1]
        have hsl' : 4 + 3 * y ^ 2 < (s : ℝ) ^ 2 := by
          linarith only [hsl, mul_nonneg (by linarith only [hnr] : (0 : ℝ) ≤ -1 - n) (sq_nonneg y)]
        linarith only [hd, hsl', sq_nonneg (3 * y - s)]
      obtain hm1 | hm2 | hm3 : n = -1 ∨ n = -2 ∨ n ≤ -3 := by omega
      · -- ⌊x⌋ = -1
        have hnr1 : (n : ℝ) = -1 := by exact_mod_cast hm1
        rw [hnr1] at hxf hsl hsu
        have hxa : -1 ≤ x := by linarith
        have hxb : x < 0 := by linarith
        have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hxa, hxb]
        have hx20 : 0 ≤ x ^ 2 := sq_nonneg x
        have hx41 : x ^ 4 ≤ 1 := by nlinarith only [hx2, hx20]
        have hx40 : 0 ≤ x ^ 4 := by positivity
        have hNle : N ≤ 1 := by
          have h : (N : ℝ) ≤ 1 := by linarith
          exact_mod_cast h
        have hNge : 0 ≤ N := by
          have h : (-1 : ℝ) < N := by linarith
          have h' : -1 < N := by exact_mod_cast h
          omega
        obtain hNz | hNo : N = 0 ∨ N = 1 := by omega
        · have hNr : (N : ℝ) = 0 := by exact_mod_cast hNz
          rw [hNr] at hs1 hs2
          have h1 : (s : ℝ) ≤ 0 := by linarith
          have h2 : (-1 : ℝ) < s := by linarith
          have hsz : (s : ℝ) ^ 2 ≤ 1 := by nlinarith only [h1, h2]
          linarith only [hsz, hsl, hy2]
        · exact key1 (by exact_mod_cast hNo)
      · -- ⌊x⌋ = -2
        have hnr2 : (n : ℝ) = -2 := by exact_mod_cast hm2
        rw [hnr2] at hxf hsl hsu hc1 hc2
        have hxa : -2 ≤ x := by linarith
        have hxb : x < -1 := by linarith
        have hx2 : 1 < x ^ 2 := by nlinarith only [hxb]
        have hx41 : 1 < x ^ 4 := by nlinarith only [hx2]
        have hNge : 1 ≤ N := by
          have h : (0 : ℝ) < N := by linarith
          have h' : 0 < N := by exact_mod_cast h
          omega
        obtain hNa | hNb | hNc | hNd : N = 1 ∨ N = 2 ∨ N = 3 ∨ 4 ≤ N := by omega
        · exact key1 (by exact_mod_cast hNa)
        · have hNr : (N : ℝ) = 2 := by exact_mod_cast hNb
          rw [hNr] at hs1 hs2
          have hd0 : 0 ≤ 2 * y - s := by linarith
          have hd1 : 2 * y - s < 1 := by linarith
          have hd : (2 * y - s) ^ 2 < 1 := by nlinarith only [hd0, hd1]
          linarith only [hd, hsl, sq_nonneg (3 * y - s)]
        · have hNr : (N : ℝ) = 3 := by exact_mod_cast hNc
          rw [hNr] at hs1 hs2 hN1 hN2
          have hfhalf : 1 / 2 < f := by
            by_contra hcon
            rw [not_lt] at hcon
            have hx32 : x ≤ -(3 / 2) := by linarith only [hcon, hxf]
            have hx94 : 9 / 4 ≤ x ^ 2 := by nlinarith only [hx32]
            nlinarith only [hx94, hN2]
          have hck : c = 10 * k + 1 := by
            have h1 : (c : ℝ) < 10 * k + 2 := by linarith
            have h2 : (10 * k : ℝ) < c := by linarith
            have h1' : c < 10 * k + 2 := by exact_mod_cast h1
            have h2' : 10 * k < c := by exact_mod_cast h2
            omega
          have hss : s * s = 4 - 10 * k := by
            have h : s ^ 2 = 4 - 10 * k := by linarith
            rw [← h, sq]
          have hkge : -5 ≤ k := by
            have hy27 : 3 * y ^ 2 < 27 := by
              rcases lt_or_gt_of_ne hy0 with hyn | hyp
              · have h3 : (s : ℝ) ≤ 3 * y := by linarith only [hs1]
                have h4 : (3 * y) ^ 2 ≤ (s : ℝ) ^ 2 := by nlinarith only [h3, hyn]
                linarith only [h4, hsu]
              · have hy1 : 1 < y := by nlinarith only [hyp, hy2]
                have h3 : 3 * y - 1 < (s : ℝ) := by linarith only [hs2]
                have h4 : (3 * y - 1) ^ 2 < (s : ℝ) ^ 2 := by nlinarith only [h3, hy1]
                have hy3 : y < 3 := by nlinarith only [h4, hsu]
                nlinarith only [hy3, hyp]
            have h : (-6 : ℝ) < k := by linarith
            have h' : -6 < k := by exact_mod_cast h
            omega
          have hs7 : s ≤ 7 := by nlinarith only [hss, hkge]
          have hs7' : -7 ≤ s := by nlinarith only [hss, hkge]
          interval_cases k <;> interval_cases s <;> omega
        · have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hNd
          rcases lt_or_gt_of_ne hy0 with hyn | hyp
          · have h3 : (s : ℝ) ≤ 4 * y := by nlinarith only [hs1, hNr, hyn]
            have h4 : (4 * y) ^ 2 ≤ (s : ℝ) ^ 2 := by nlinarith only [h3, hyn]
            linarith only [h4, hsu, hy2]
          · have hy1 : 115 / 100 < y := by nlinarith only [hyp, hy2]
            have h3 : 4 * y - 1 < (s : ℝ) := by nlinarith only [hs2, hNr, hyp]
            have h4 : (4 * y - 1) ^ 2 < (s : ℝ) ^ 2 := by nlinarith only [h3, hy1]
            linarith only [h4, hsu, mul_pos (by linarith only [hy1] : (0 : ℝ) < y - 115 / 100)
              (by linarith only [hy1] : (0 : ℝ) < 10 * y + 35 / 10)]
      · -- ⌊x⌋ ≤ -3
        have hnr3 : (n : ℝ) ≤ -3 := by exact_mod_cast hm3
        have hxb : x < -2 := by linarith
        have hxc : x < n + 1 := by linarith
        have hx2 : 4 < x ^ 2 := by nlinarith only [hxb]
        have hx2n : -2 * (n : ℝ) - 2 < x ^ 2 := by
          linarith only [hxb, hxc, hnr3,
            mul_pos (by linarith only [hxb] : (0 : ℝ) < -2 - x)
              (by linarith only [hxc] : (0 : ℝ) < n + 1 - x),
            mul_nonneg (by linarith only [hnr3] : (0 : ℝ) ≤ -3 - n)
              (by linarith only [hxb] : (0 : ℝ) ≤ -2 - x)]
        have hx416 : 16 < x ^ 4 := by nlinarith only [hx2]
        have hx4n : -8 * (n : ℝ) - 8 < x ^ 4 := by nlinarith only [hx2, hx2n]
        have hN16 : (15 : ℝ) ≤ N - 1 := by
          have h : (15 : ℝ) < N := by linarith
          have h' : 15 < N := by exact_mod_cast h
          have h'' : 16 ≤ N := by omega
          have : (16 : ℝ) ≤ N := by exact_mod_cast h''
          linarith
        have hNn : -8 * (n : ℝ) - 10 < N - 1 := by linarith
        have hbig : y ^ 2 * ((N : ℝ) - 1) ^ 2 ≤ (s : ℝ) ^ 2 := by
          rcases lt_or_gt_of_ne hy0 with hyn | hyp
          · have h3 : (s : ℝ) ≤ y * (N - 1) := by linarith only [hs1, hyn]
            have h4 : y * ((N : ℝ) - 1) < 0 := by nlinarith only [hyn, hN16]
            rw [← mul_pow]
            nlinarith only [h3, h4]
          · have hy1 : 1 < y := by nlinarith only [hyp, hy2]
            have h3 : y * ((N : ℝ) - 1) < s := by linarith only [hs2, hy1]
            have h4 : 0 < y * ((N : ℝ) - 1) := by nlinarith only [hyp, hN16]
            rw [← mul_pow]
            nlinarith only [h3, h4]
        have hpos : 0 < ((N : ℝ) - 1) ^ 2 - 15 / 4 + 3 * n := by
          nlinarith only [hN16, hNn, hnr3]
        have hle : y ^ 2 * (((N : ℝ) - 1) ^ 2 - 15 / 4 + 3 * n) ≤ 0 := by
          linarith only [hbig, hsu, hy2]
        linarith only [hle, mul_pos hpos (by linarith only [hy2] : (0 : ℝ) < y ^ 2)]
  · rintro ⟨rfl, rfl⟩
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hy2 : (2 / Real.sqrt 3) ^ 2 = 4 / 3 := by
      rw [div_pow, h3]; norm_num
    have e1 : ⌊(1 : ℝ)⌋ = 1 := Int.floor_one
    have e2 : ⌊(1 : ℝ) ^ 4⌋ = 1 := by
      rw [one_pow]; exact Int.floor_one
    have e3 : ⌈3 * ((1 : ℤ) : ℝ) * (2 / Real.sqrt 3) ^ 2⌉ = 4 := by
      rw [hy2, Int.ceil_eq_iff]; norm_num
    have e4 : ⌊2 / Real.sqrt 3 * ((1 : ℤ) : ℝ)⌋ = 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [Int.cast_one, mul_one, le_div_iff₀ h3p]
        nlinarith only [h3, h3p]
      · rw [Int.cast_one, mul_one, div_lt_iff₀ h3p]
        nlinarith only [h3, h3p]
    refine ⟨?_, -1, ?_⟩
    · rw [e1, e2, e3, e4]; norm_num
    · rw [Int.fract_one, hy2]; norm_num
```
