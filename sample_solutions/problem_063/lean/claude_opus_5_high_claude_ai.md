# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `18 August 2026`\
Line count: `165`\
Turn count: `3`

## Solution

```lean4
import Mathlib

open Polynomial

theorem rational_expr_iff_perfect_powers (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) (hne : (x : ℝ) ^ ((2 : ℝ) / 7) ≠ (y : ℝ) ^ 6) :
      (∃ q : ℚ, (3 * (x : ℝ) + (y : ℝ) ^ ((5 : ℝ) / 3)) /
      ((x : ℝ) ^ ((2 : ℝ) / 7) - (y : ℝ) ^ 6) = (q : ℝ)) ↔
      (∃ a : ℕ, a ^ 7 = x) ∧ (∃ b : ℕ, b ^ 3 = y) := by
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by positivity
  have hy0 : (0:ℝ) ≤ (y:ℝ) := by positivity
  -- A rational `n`-th root (n odd) of a natural number is a natural number
  have hpow : ∀ (n m : ℕ) (b : ℚ), Odd n → b ^ n = (m : ℚ) → ∃ k : ℕ, k ^ n = m := by
    intro n m b hodd hb
    have hn : 0 < n := by rcases hodd with ⟨j, hj⟩; omega
    have hR : ((b:ℝ)) ^ n = ((m:ℤ) : ℝ) := by exact_mod_cast hb
    have hint : ∃ z : ℤ, (b:ℝ) = (z:ℝ) := by
      by_contra hcon
      exact (Rat.not_irrational b) (irrational_nrt_of_notint_nrt n (m:ℤ) hR hcon hn)
    obtain ⟨z, hz⟩ := hint
    have hzb : (z:ℚ) = b := by exact_mod_cast hz.symm
    have hzn : z ^ n = (m:ℤ) := by
      have h1 : ((z:ℚ)) ^ n = (m:ℚ) := by rw [hzb]; exact hb
      exact_mod_cast h1
    have hz0 : 0 ≤ z := by
      by_contra hlt
      push_neg at hlt
      have h2 : (0:ℤ) < (-z) ^ n := pow_pos (by omega) n
      rw [hodd.neg_pow, hzn] at h2
      omega
    refine ⟨z.toNat, ?_⟩
    have h1 : ((z.toNat : ℤ)) ^ n = (m:ℤ) := by rw [Int.toNat_of_nonneg hz0]; exact hzn
    exact_mod_cast h1
  -- if `m^3 = y^5` then `y` is a cube
  have cube : ∀ m : ℕ, m ^ 3 = y ^ 5 → ∃ b : ℕ, b ^ 3 = y := by
    intro m hm
    have hdvd : y ^ 3 ∣ m ^ 2 := by
      have h1 : (y ^ 3) ^ 3 ∣ (m ^ 2) ^ 3 := by
        refine ⟨y, ?_⟩
        calc (m ^ 2) ^ 3 = (m ^ 3) ^ 2 := by ring
          _ = (y ^ 5) ^ 2 := by rw [hm]
          _ = (y ^ 3) ^ 3 * y := by ring
      first
        | exact (Nat.pow_dvd_pow_iff (by norm_num)).mp h1
        | exact (pow_dvd_pow_iff (by norm_num)).mp h1
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k, ?_⟩
    have h2 : y ^ 9 * k ^ 3 = y ^ 9 * y := by
      calc y ^ 9 * k ^ 3 = (y ^ 3 * k) ^ 3 := by ring
        _ = (m ^ 2) ^ 3 := by rw [← hk]
        _ = (m ^ 3) ^ 2 := by ring
        _ = (y ^ 5) ^ 2 := by rw [hm]
        _ = y ^ 9 * y := by ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hy 9) h2
  -- computing the powers when `x`, `y` are perfect powers
  have hApow : ∀ a : ℕ, a ^ 7 = x → (x:ℝ) ^ ((2:ℝ)/7) = (a:ℝ) ^ (2:ℕ) := by
    intro a ha
    rw [← ha]
    push_cast
    rw [← Real.rpow_natCast (a:ℝ) 7, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (a:ℝ)),
      show ((7:ℕ):ℝ) * ((2:ℝ)/7) = ((2:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
  have hBpow : ∀ b : ℕ, b ^ 3 = y → (y:ℝ) ^ ((5:ℝ)/3) = (b:ℝ) ^ (5:ℕ) := by
    intro b hb
    rw [← hb]
    push_cast
    rw [← Real.rpow_natCast (b:ℝ) 3, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (b:ℝ)),
      show ((3:ℕ):ℝ) * ((5:ℝ)/3) = ((5:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
  obtain ⟨t, ht7, htA⟩ : ∃ t : ℝ, t ^ (7:ℕ) = (x:ℝ) ∧ t ^ (2:ℕ) = (x:ℝ) ^ ((2:ℝ)/7) := by
    refine ⟨(x:ℝ) ^ ((1:ℝ)/7), ?_, ?_⟩
    · rw [← Real.rpow_natCast ((x:ℝ) ^ ((1:ℝ)/7)) 7, ← Real.rpow_mul hx0,
        show (1:ℝ)/7 * ((7:ℕ):ℝ) = 1 by push_cast; ring, Real.rpow_one]
    · rw [← Real.rpow_natCast ((x:ℝ) ^ ((1:ℝ)/7)) 2, ← Real.rpow_mul hx0,
        show (1:ℝ)/7 * ((2:ℕ):ℝ) = (2:ℝ)/7 by push_cast; ring]
  have hB3 : ((y:ℝ) ^ ((5:ℝ)/3)) ^ (3:ℕ) = (y:ℝ) ^ (5:ℕ) := by
    rw [← Real.rpow_natCast ((y:ℝ) ^ ((5:ℝ)/3)) 3, ← Real.rpow_mul hy0,
      show (5:ℝ)/3 * ((3:ℕ):ℝ) = ((5:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
  have hCC : ∀ c : ℚ, (Polynomial.aeval t) (C c) = (c:ℝ) := by intro c; simp
  constructor
  · rintro ⟨q, hq⟩
    have hden : (x:ℝ) ^ ((2:ℝ)/7) - (y:ℝ) ^ 6 ≠ 0 := sub_ne_zero.mpr hne
    have heq : 3 * (x:ℝ) + (y:ℝ) ^ ((5:ℝ)/3) = (q:ℝ) * ((x:ℝ) ^ ((2:ℝ)/7) - (y:ℝ) ^ 6) :=
      (div_eq_iff hden).mp hq
    have hxpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
    have hBpos : (0:ℝ) < (y:ℝ) ^ ((5:ℝ)/3) := Real.rpow_pos_of_pos (by exact_mod_cast hy) _
    have hq0 : q ≠ 0 := by
      intro h
      rw [h, Rat.cast_zero, zero_mul] at heq
      linarith
    obtain ⟨r, hrdef⟩ : ∃ r : ℚ, (r:ℝ) = -((q:ℝ) * (y:ℝ) ^ 6 + 3 * (x:ℝ)) :=
      ⟨-(q * (y:ℚ) ^ 6 + 3 * (x:ℚ)), by push_cast; ring⟩
    have hBr : (y:ℝ) ^ ((5:ℝ)/3) = (q:ℝ) * t ^ (2:ℕ) + (r:ℝ) := by
      rw [htA, hrdef]
      linear_combination heq
    by_cases hxa : ∃ a : ℕ, a ^ 7 = x
    · obtain ⟨a, ha⟩ := hxa
      refine ⟨⟨a, ha⟩, ?_⟩
      have hA := hApow a ha
      have hBQ : (y:ℝ) ^ ((5:ℝ)/3) = ((q * (a:ℚ) ^ 2 + r : ℚ) : ℝ) := by
        rw [hBr, htA, hA]
        push_cast
        ring
      have h5 : (q * (a:ℚ) ^ 2 + r) ^ (3:ℕ) = ((y ^ 5 : ℕ) : ℚ) := by
        have h6 : (((q * (a:ℚ) ^ 2 + r : ℚ)) : ℝ) ^ (3:ℕ) = (y:ℝ) ^ (5:ℕ) := by
          rw [← hBQ]; exact hB3
        exact_mod_cast h6
      obtain ⟨k, hk⟩ := hpow 3 (y ^ 5) (q * (a:ℚ) ^ 2 + r) ⟨1, by norm_num⟩ h5
      exact cube k hk
    · exfalso
      have hcube : ((q:ℝ) * t ^ (2:ℕ) + (r:ℝ)) ^ (3:ℕ) = (y:ℝ) ^ (5:ℕ) := by
        rw [← hBr]; exact hB3
      have hnb : ∀ b : ℚ, b ^ 7 ≠ (x:ℚ) := by
        intro b hb
        obtain ⟨k, hk⟩ := hpow 7 x b ⟨3, by norm_num⟩ hb
        exact hxa ⟨k, hk⟩
      have hirr : Irreducible ((X:ℚ[X]) ^ 7 - C (x:ℚ)) :=
        X_pow_sub_C_irreducible_of_prime (by norm_num) hnb
      have hmonic : ((X:ℚ[X]) ^ 7 - C (x:ℚ)).Monic := by
        first
          | exact monic_X_pow_sub_C _ (by norm_num)
          | monicity!
      have hroot : (Polynomial.aeval t) ((X:ℚ[X]) ^ 7 - C (x:ℚ)) = 0 := by
        simp only [map_sub, map_pow, map_natCast, map_ofNat, Polynomial.aeval_X, hCC]
        rw [ht7]
        push_cast
        ring
      have hmin : ((X:ℚ[X]) ^ 7 - C (x:ℚ)) = minpoly ℚ t :=
        minpoly.eq_of_irreducible_of_monic hirr hroot hmonic
      obtain ⟨P, hPa, hPne, hPdeg⟩ :
          ∃ P : ℚ[X], (Polynomial.aeval t) P = 0 ∧ P ≠ 0 ∧ P.natDegree ≤ 6 := by
        refine ⟨C (q ^ 3) * X ^ 6 + C (3 * q ^ 2 * r) * X ^ 4 + C (3 * q * r ^ 2) * X ^ 2 +
          C (r ^ 3 - (y:ℚ) ^ 5), ?_, ?_, ?_⟩
        · simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast,
            Polynomial.aeval_X, hCC]
          push_cast
          linear_combination hcube
        · intro h
          apply hq0
          have hc : (C (q ^ 3) * (X:ℚ[X]) ^ 6 + C (3 * q ^ 2 * r) * X ^ 4 +
              C (3 * q * r ^ 2) * X ^ 2 + C (r ^ 3 - (y:ℚ) ^ 5)).coeff 6 = q ^ 3 := by
            simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
              Polynomial.coeff_C]
            norm_num
          rw [h, Polynomial.coeff_zero] at hc
          simpa using hc.symm
        · compute_degree!
      have hdvd : minpoly ℚ t ∣ P := by
        first
          | exact minpoly.dvd ℚ t hPa
          | exact minpoly.dvd ℚ hPa
          | exact minpoly.dvd hPa
          | exact minpoly.dvd (A := ℚ) (x := t) hPa
      have h2 : (minpoly ℚ t).natDegree ≤ P.natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hPne
      have hnd : ((X:ℚ[X]) ^ 7 - C (x:ℚ)).natDegree = 7 := by compute_degree!
      rw [← hmin, hnd] at h2
      first
        | omega
        | exact absurd (le_trans h2 hPdeg) (by norm_num)
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hA := hApow a ha
    have hB := hBpow b hb
    refine ⟨(3 * (x:ℚ) + (b:ℚ) ^ 5) / ((a:ℚ) ^ 2 - (y:ℚ) ^ 6), ?_⟩
    rw [hA, hB]
    push_cast
    ring
```
