# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `11 November 2026`\
Line count: `165`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem rational_expr_iff_perfect_powers (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) (hne : (x : ℝ) ^ ((2 : ℝ) / 7) ≠ (y : ℝ) ^ 6) :
      (∃ q : ℚ, (3 * (x : ℝ) + (y : ℝ) ^ ((5 : ℝ) / 3)) /
      ((x : ℝ) ^ ((2 : ℝ) / 7) - (y : ℝ) ^ 6) = (q : ℝ)) ↔
      (∃ a : ℕ, a ^ 7 = x) ∧ (∃ b : ℕ, b ^ 3 = y) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  -- Powers are injective on nonnegative reals.
  have pow_inj : ∀ n : ℕ, n ≠ 0 → ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s ^ n = t ^ n → s = t := by
    intro n hn s t hs ht h
    first
      | exact (pow_left_inj₀ hs ht hn).mp h
      | exact (pow_left_inj hs ht hn).mp h
  -- A rational real whose n-th power is a natural number is a natural number.
  have int_root : ∀ n : ℕ, 0 < n → ∀ (t : ℝ) (w : ℚ) (m : ℕ),
      t = (w : ℝ) → t ^ n = (m : ℝ) → ∃ k : ℕ, k ^ n = m := by
    intro n hn t w m htw htm
    have hint : ∃ k : ℤ, t = (k : ℝ) := by
      by_contra hv
      have hirr : Irrational t :=
        irrational_nrt_of_notint_nrt n (m : ℤ) (by exact_mod_cast htm) hv hn
      exact hirr (Set.mem_range.mpr ⟨w, htw.symm⟩)
    obtain ⟨k, hk⟩ := hint
    have hk1 : (k : ℝ) ^ n = (m : ℝ) := by rw [← hk]; exact htm
    have hk2 : k ^ n = (m : ℤ) := by exact_mod_cast hk1
    have hk3 := congrArg Int.natAbs hk2
    exact ⟨k.natAbs, by simpa [Int.natAbs_pow] using hk3⟩
  -- α = x^(1/7) and β = y^(1/3); rewrite everything in terms of them.
  obtain ⟨α, hαpos, hα7, hx27⟩ :
      ∃ α : ℝ, 0 < α ∧ α ^ 7 = (x : ℝ) ∧ (x : ℝ) ^ ((2 : ℝ) / 7) = α ^ 2 := by
    refine ⟨(x : ℝ) ^ ((1 : ℝ) / 7), Real.rpow_pos_of_pos hx0 _, ?_, ?_⟩
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      first
        | norm_num
        | (congr 1; norm_num)
  obtain ⟨β, hβpos, hβ3, hy53⟩ :
      ∃ β : ℝ, 0 < β ∧ β ^ 3 = (y : ℝ) ∧ (y : ℝ) ^ ((5 : ℝ) / 3) = β ^ 5 := by
    refine ⟨(y : ℝ) ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hy0 _, ?_, ?_⟩
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
      norm_num
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
      first
        | norm_num
        | (congr 1; norm_num)
  rw [hx27] at hne
  rw [hx27, hy53]
  have hd : α ^ 2 - (y : ℝ) ^ 6 ≠ 0 := sub_ne_zero.mpr hne
  constructor
  · -- (→) rationality forces x to be a 7th power and y a cube
    rintro ⟨q, hq⟩
    have h1 : 3 * (x : ℝ) + β ^ 5 = (q : ℝ) * (α ^ 2 - (y : ℝ) ^ 6) :=
      (div_eq_iff hd).mp hq
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [Rat.cast_zero, zero_mul] at h1
      have hpos : 0 < 3 * (x : ℝ) + β ^ 5 :=
        add_pos (mul_pos (by norm_num) hx0) (pow_pos hβpos 5)
      linarith
    obtain ⟨r, hr⟩ : ∃ r : ℚ, (r : ℝ) = -((q : ℝ) * (y : ℝ) ^ 6) - 3 * (x : ℝ) :=
      ⟨-(q * (y : ℚ) ^ 6) - 3 * (x : ℚ), by push_cast; try ring⟩
    -- the key linear relation between β² and α²
    have hmain : (y : ℝ) * β ^ 2 = (q : ℝ) * α ^ 2 + (r : ℝ) := by
      have h2 : β ^ 5 = (y : ℝ) * β ^ 2 := by rw [← hβ3]; ring
      rw [hr]
      linear_combination h1 - h2
    -- x² is a 7th power in ℚ: otherwise X⁷ - x² is the minimal polynomial of α²,
    -- but α² is a root of a cubic.
    obtain ⟨s, hs⟩ : ∃ s : ℚ, s ^ 7 = (x : ℚ) ^ 2 := by
      by_contra hno
      have hno' : ∀ b : ℚ, b ^ 7 ≠ (x : ℚ) ^ 2 := fun b hb => hno ⟨b, hb⟩
      obtain ⟨P, hP⟩ : ∃ P : Polynomial ℚ,
          P = Polynomial.X ^ 7 - Polynomial.C ((x : ℚ) ^ 2) := ⟨_, rfl⟩
      obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℚ,
          Q = (Polynomial.C q * Polynomial.X + Polynomial.C r) ^ 3
            - Polynomial.C ((y : ℚ) ^ 5) := ⟨_, rfl⟩
      have hirr : Irreducible P := by
        rw [hP]
        first
          | exact X_pow_sub_C_irreducible_of_prime (by norm_num) hno'
          | exact (X_pow_sub_C_irreducible_iff_of_prime (by norm_num)).mpr hno'
      have hPmonic : P.Monic := by
        rw [hP]; exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
      have hPdeg : P.natDegree = 7 := by
        rw [hP]
        first
          | rw [Polynomial.natDegree_X_pow_sub_C]
          | apply Polynomial.natDegree_X_pow_sub_C
          | simp
      have hPα : Polynomial.aeval (α ^ 2) P = 0 := by
        have h3 : Polynomial.aeval (α ^ 2) P = (α ^ 2) ^ 7 - (x : ℝ) ^ 2 := by
          rw [hP]
          first
            | simp
            | simp [Polynomial.aeval_def]
        rw [h3, ← hα7]; ring
      have hQα : Polynomial.aeval (α ^ 2) Q = 0 := by
        have h3 : Polynomial.aeval (α ^ 2) Q
            = ((q : ℝ) * α ^ 2 + (r : ℝ)) ^ 3 - (y : ℝ) ^ 5 := by
          rw [hQ]
          first
            | simp
            | simp [Polynomial.aeval_def]
        have h4 : ((y : ℝ) * β ^ 2) ^ 3 = (y : ℝ) ^ 3 * (β ^ 3) ^ 2 := by ring
        rw [h3, ← hmain, h4, hβ3]; ring
      have hQdeg : Q.natDegree = 3 * 1 := by
        rw [hQ, Polynomial.natDegree_sub_C, Polynomial.natDegree_pow,
          Polynomial.natDegree_linear hq0]
      have hQ0 : Q ≠ 0 := by
        intro h
        rw [h, Polynomial.natDegree_zero] at hQdeg
        omega
      have hPmin : P = minpoly ℚ (α ^ 2) :=
        minpoly.eq_of_irreducible_of_monic hirr hPα hPmonic
      have hdvd : P ∣ Q := by
        rw [hPmin]; exact minpoly.dvd ℚ (α ^ 2) hQα
      have hle := Polynomial.natDegree_le_of_dvd hdvd hQ0
      omega
    -- hence α² = s is rational
    have hsR : (s : ℝ) ^ 7 = (x : ℝ) ^ 2 := by exact_mod_cast hs
    have hspos : (0 : ℝ) < (s : ℝ) := by
      by_contra hneg
      have hneg' : (s : ℝ) ≤ 0 := not_lt.mp hneg
      have h3 : (0 : ℝ) < (x : ℝ) ^ 2 := pow_pos hx0 2
      have h4 : 0 ≤ (-(s : ℝ)) * ((s : ℝ) ^ 3) ^ 2 :=
        mul_nonneg (neg_nonneg.mpr hneg') (sq_nonneg _)
      nlinarith [h3, h4, hsR]
    have hαs : α ^ 2 = (s : ℝ) :=
      pow_inj 7 (by norm_num) (α ^ 2) s (by positivity) hspos.le
        (by rw [hsR, ← hα7]; ring)
    -- α = x / s³ is rational, so it is a natural number
    have hαrat : α = (((x : ℚ) / s ^ 3 : ℚ) : ℝ) := by
      have h5 : α * (s : ℝ) ^ 3 = (x : ℝ) := by rw [← hαs, ← hα7]; ring
      push_cast
      rw [eq_div_iff (pow_ne_zero 3 hspos.ne')]
      exact h5
    obtain ⟨a, ha⟩ := int_root 7 (by norm_num) α _ x hαrat hα7
    -- β² = (q s + r) / y is rational, so β = y / β² is rational, hence natural
    have hβ2 : β ^ 2 = (((q * s + r) / (y : ℚ) : ℚ) : ℝ) := by
      push_cast
      rw [eq_div_iff hy0.ne', ← hαs]
      linear_combination hmain
    obtain ⟨w, hw⟩ : ∃ w : ℚ, β ^ 2 = (w : ℝ) := ⟨_, hβ2⟩
    have hβrat : β = (((y : ℚ) / w : ℚ) : ℝ) := by
      have h6 : β * β ^ 2 = (y : ℝ) := by rw [← hβ3]; ring
      push_cast
      rw [← hw, eq_div_iff (pow_ne_zero 2 hβpos.ne')]
      exact h6
    obtain ⟨b, hb⟩ := int_root 3 (by norm_num) β _ y hβrat hβ3
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  · -- (←) if x = a⁷ and y = b³ the expression is visibly rational
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have haα : α = (a : ℝ) :=
      pow_inj 7 (by norm_num) α a hαpos.le (Nat.cast_nonneg a)
        (by rw [hα7]; exact_mod_cast ha.symm)
    have hbβ : β = (b : ℝ) :=
      pow_inj 3 (by norm_num) β b hβpos.le (Nat.cast_nonneg b)
        (by rw [hβ3]; exact_mod_cast hb.symm)
    refine ⟨(3 * (x : ℚ) + (b : ℚ) ^ 5) / ((a : ℚ) ^ 2 - (y : ℚ) ^ 6), ?_⟩
    rw [haα, hbβ]
    push_cast
    try ring
```
