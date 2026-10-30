# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `3 September 2026`\
Line count: `123`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

open Polynomial

theorem rational_expr_iff_perfect_powers (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) (hne : (x : ℝ) ^ ((2 : ℝ) / 7) ≠ (y : ℝ) ^ 6) :
      (∃ q : ℚ, (3 * (x : ℝ) + (y : ℝ) ^ ((5 : ℝ) / 3)) /
      ((x : ℝ) ^ ((2 : ℝ) / 7) - (y : ℝ) ^ 6) = (q : ℝ)) ↔
      (∃ a : ℕ, a ^ 7 = x) ∧ (∃ b : ℕ, b ^ 3 = y) := by
  have hX : (0:ℝ) < x := by exact_mod_cast hx
  have hY : (0:ℝ) < y := by exact_mod_cast hy
  have inj7 : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u ^ 7 = v ^ 7 → u = v := by
    have e : ∀ w : ℝ, 0 ≤ w → (w ^ 7) ^ ((1:ℝ)/7) = w := by
      intro w hw; rw [← Real.rpow_natCast w 7, ← Real.rpow_mul hw]; norm_num
    intro u v hu hv h; rw [← e u hu, ← e v hv, h]
  set α : ℝ := (x:ℝ) ^ ((2:ℝ)/7) with hαd
  set β : ℝ := (y:ℝ) ^ ((5:ℝ)/3) with hβd
  have hα0 : 0 ≤ α := by rw [hαd]; positivity
  have hβ0 : 0 ≤ β := by rw [hβd]; positivity
  have hα7 : α ^ 7 = (x:ℝ) ^ 2 := by
    rw [hαd, ← Real.rpow_natCast ((x:ℝ) ^ ((2:ℝ)/7)) 7, ← Real.rpow_mul hX.le,
      ← Real.rpow_natCast (x:ℝ) 2]; norm_num
  have hβ3 : β ^ 3 = (y:ℝ) ^ 5 := by
    rw [hβd, ← Real.rpow_natCast ((y:ℝ) ^ ((5:ℝ)/3)) 3, ← Real.rpow_mul hY.le,
      ← Real.rpow_natCast (y:ℝ) 5]; norm_num
  constructor
  · rintro ⟨q, hq⟩
    have h1 : 3 * (x:ℝ) + β = (q:ℝ) * (α - (y:ℝ)^6) := (div_eq_iff (sub_ne_zero.mpr hne)).mp hq
    have hq0 : q ≠ 0 := by intro h; rw [h] at h1; push_cast at h1; linarith
    obtain ⟨r, hβr⟩ : ∃ r : ℚ, β = (q:ℝ) * α + (r:ℝ) :=
      ⟨-(q * (y:ℚ)^6) - 3 * (x:ℚ), by push_cast; linear_combination h1⟩
    have h3 : ((q:ℝ) * α + (r:ℝ)) ^ 3 = (y:ℝ)^5 := by rw [← hβr]; exact hβ3
    have hαint : ∃ n : ℤ, α = (n:ℝ) := by
      by_contra hcon
      have hirr : Irrational α :=
        irrational_nrt_of_notint_nrt 7 ((x:ℤ)^2) (by push_cast; exact hα7) hcon (by norm_num)
      have hnp : ∀ b : ℚ, b ^ 7 ≠ (x:ℚ)^2 := by
        intro b hb
        have hbb : (b:ℝ)^7 = (x:ℝ)^2 := by
          have h' : ((b^7 : ℚ) : ℝ) = (((x:ℚ)^2 : ℚ) : ℝ) := by rw [hb]
          push_cast at h'; exact h'
        refine hirr ⟨|b|, ?_⟩
        rw [Rat.cast_abs]
        refine inj7 _ _ (abs_nonneg _) hα0 ?_
        rw [← abs_pow, hbb, hα7, abs_of_nonneg (by positivity : (0:ℝ) ≤ (x:ℝ)^2)]
      have hroot : (aeval α) (X ^ 7 - C ((x:ℚ)^2)) = 0 := by
        simp only [map_sub, map_pow, aeval_X, aeval_C, eq_ratCast]
        push_cast; rw [hα7, sub_self]
      have hmin : minpoly ℚ α = X ^ 7 - C ((x:ℚ)^2) :=
        (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime (by norm_num) hnp)
          hroot (monic_X_pow_sub_C _ (by norm_num))).symm
      have hP : (aeval α) (C (q^3) * X^3 + C (3*q^2*r) * X^2 + C (3*q*r^2) * X
          + C (r^3 - (y:ℚ)^5)) = 0 := by
        simp only [map_add, map_mul, map_pow, map_sub, aeval_X, aeval_C, eq_ratCast]
        push_cast; linear_combination h3
      have hPdeg : (C (q^3) * X^3 + C (3*q^2*r) * X^2 + C (3*q*r^2) * X
          + C (r^3 - (y:ℚ)^5)).natDegree = 3 := natDegree_cubic (pow_ne_zero 3 hq0)
      have hPne : (C (q^3) * X^3 + C (3*q^2*r) * X^2 + C (3*q*r^2) * X
          + C (r^3 - (y:ℚ)^5)) ≠ 0 := by
        intro h; rw [h, natDegree_zero] at hPdeg; exact absurd hPdeg (by norm_num)
      have hle := natDegree_le_of_dvd (minpoly.dvd ℚ α hP) hPne
      rw [hmin, natDegree_X_pow_sub_C, hPdeg] at hle
      omega
    obtain ⟨n, hn⟩ := hαint
    have hn7 : n^7 = (x:ℤ)^2 := by
      have h' : ((n^7 : ℤ):ℝ) = (((x:ℤ)^2 : ℤ):ℝ) := by push_cast; rw [← hn]; exact hα7
      exact_mod_cast h'
    have hn0 : (0:ℤ) ≤ n := by
      have h' : (0:ℝ) ≤ (n:ℝ) := by rw [← hn]; exact hα0
      exact_mod_cast h'
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (a:ℤ) = n := ⟨n.toNat, Int.toNat_of_nonneg hn0⟩
    have ha7 : a^7 = x^2 := by
      have h' : (a:ℤ)^7 = (x:ℤ)^2 := by rw [ha]; exact hn7
      exact_mod_cast h'
    have hβint : ∃ m : ℤ, β = (m:ℝ) := by
      by_contra hcon
      exact (irrational_nrt_of_notint_nrt 3 ((y:ℤ)^5) (by push_cast; exact hβ3) hcon
        (by norm_num)) ⟨q * (n:ℚ) + r, by push_cast; rw [hβr, hn]⟩
    obtain ⟨m, hm⟩ := hβint
    have hm0 : (0:ℤ) ≤ m := by
      have h' : (0:ℝ) ≤ (m:ℝ) := by rw [← hm]; exact hβ0
      exact_mod_cast h'
    obtain ⟨c, hcm⟩ : ∃ c : ℕ, (c:ℤ) = m := ⟨m.toNat, Int.toNat_of_nonneg hm0⟩
    have hc3 : c^3 = y^5 := by
      have h' : (c:ℤ)^3 = (y:ℤ)^5 := by
        rw [hcm]
        have h'' : ((m^3 : ℤ):ℝ) = (((y:ℤ)^5 : ℤ):ℝ) := by push_cast; rw [← hm]; exact hβ3
        exact_mod_cast h''
      exact_mod_cast h'
    constructor
    · obtain ⟨t, ht⟩ : a^3 ∣ x := by
        have h6 : (a^3)^7 = x^6 := by
          calc (a^3)^7 = (a^7)^3 := by ring
          _ = (x^2)^3 := by rw [ha7]
          _ = x^6 := by ring
        refine (Nat.pow_dvd_pow_iff (n := 7) (by norm_num)).mp ?_
        rw [h6]; exact pow_dvd_pow x (by norm_num)
      refine ⟨t, Nat.eq_of_mul_eq_mul_left (pow_pos hx 6) ?_⟩
      calc x^6 * t^7 = (x^2)^3 * t^7 := by ring
      _ = (a^7)^3 * t^7 := by rw [ha7]
      _ = (a^3 * t)^7 := by ring
      _ = x^7 := by rw [← ht]
      _ = x^6 * x := by ring
    · obtain ⟨s, hs⟩ : c ∣ y^2 := by
        have h6 : (y^2)^3 = y^6 := by ring
        refine (Nat.pow_dvd_pow_iff (n := 3) (by norm_num)).mp ?_
        rw [hc3, h6]; exact pow_dvd_pow y (by norm_num)
      refine ⟨s, Nat.eq_of_mul_eq_mul_left (pow_pos hy 5) ?_⟩
      calc y^5 * s^3 = c^3 * s^3 := by rw [hc3]
      _ = (c * s)^3 := by ring
      _ = (y^2)^3 := by rw [← hs]
      _ = y^5 * y := by ring
  · rintro ⟨⟨a, ha⟩, b, hb⟩
    have hA : α = (a:ℝ)^2 := by
      rw [hαd, ← ha]; push_cast
      rw [← Real.rpow_natCast (a:ℝ) 7, ← Real.rpow_mul (Nat.cast_nonneg a),
        ← Real.rpow_natCast (a:ℝ) 2]; norm_num
    have hB : β = (b:ℝ)^5 := by
      rw [hβd, ← hb]; push_cast
      rw [← Real.rpow_natCast (b:ℝ) 3, ← Real.rpow_mul (Nat.cast_nonneg b),
        ← Real.rpow_natCast (b:ℝ) 5]; norm_num
    have hY6 : (y:ℝ)^6 = (b:ℝ)^18 := by rw [← hb]; push_cast; ring
    exact ⟨(3*(x:ℚ) + (b:ℚ)^5)/((a:ℚ)^2 - (b:ℚ)^18), by rw [hA, hB, hY6]; push_cast; ring⟩
```
