# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `8 August 2026`\
Line count: `663`\
Turn count: `3`

## Solution

```lean4
/-
  cos (100 π x²) = 2.01 x² - 1  has exactly 198 real solutions.

  STRATEGY
  ========
  Substitute t = x².  Let

      f t = cos (100 π t) - (2.01 t - 1),     f' t = -(100 π sin (100 π t)) - 2.01.

  At the grid points t_k = k/100 we have cos (100 π t_k) = (-1)^k, so

      f t_k = (-1)^k + 1 - (2.01 k)/100,

  which is > 0 for even k ≤ 98 (worst case k = 98: 2 - 1.9698 = 0.0302) and < 0 for
  odd k ≥ 1.  So f alternates sign across each of the 99 intervals [t_k, t_{k+1}],
  k = 0, …, 98.

  Uniqueness on each interval:
    * k even: sin (100 π t) ≥ 0 there, so f' ≤ -2.01 < 0.  Strictly decreasing.
    * k odd:  sin (100 π t) ≤ 0.  Writing 100 π t = θ + k π with θ ∈ [0, π], we get
              f' = 100 π sin θ - 2.01, which is negative for θ ∈ (0, α), positive for
              θ ∈ (α, π - α), negative for θ ∈ (π - α, π), where α = arcsin (2.01/(100π)).
              In t-coordinates the switch points are a k = k/100 + d, b k = (k+1)/100 - d
              with d = α/(100π) < 1/200.
              f is < 0 on [t_k, a k] (decreasing from a negative value), > 0 on
              [b k, t_{k+1}] (decreasing to a positive value), and strictly increasing
              on [a k, b k].  Exactly one root, and it lies in (a k, b k).

  Nothing beyond:  for t ≥ 0.99 the left side is ≤ sin(π/402) ≈ 0.008 while the right
  side is ≥ 0.9899 (crudely: cos θ > cos (2π/3) = -1/2 suffices); for t < 0 the right
  side is < -1.

  So the t-equation has exactly 99 roots, all in (0, 0.99), none equal to 0.  Each pulls
  back to exactly two reals ±√t, giving 2 · 99 = 198.

  STATUS: this file has NOT been compiled.  See the notes at the bottom.
-/

import Mathlib

open Real Set

noncomputable section

namespace CosCount

/-! ## 0.  Constants and elementary numeric facts -/

/-- The slope constant `2.01`. -/
def c : ℝ := 201 / 100

lemma c_pos : (0 : ℝ) < c := by norm_num [c]

lemma pi_lb : (3 : ℝ) < π := Real.pi_gt_three

lemma hundred_pi_pos : (0 : ℝ) < 100 * π := by
  have := Real.pi_pos; linarith

lemma hundred_pi_gt : (300 : ℝ) < 100 * π := by
  have := pi_lb; linarith

lemma hundred_pi_ne : (100 : ℝ) * π ≠ 0 := ne_of_gt hundred_pi_pos

/-- `ε = 2.01 / (100 π)`: the value of `|sin|` at which `f'` changes sign. -/
def ε : ℝ := c / (100 * π)

lemma eps_pos : 0 < ε := div_pos c_pos hundred_pi_pos

lemma eps_lt_one : ε < 1 := by
  rw [ε, div_lt_one hundred_pi_pos]
  have := hundred_pi_gt
  simp only [c]
  linarith

/-- `α = arcsin ε ∈ (0, π/2)`. -/
def α : ℝ := arcsin ε

lemma alpha_pos : 0 < α := Real.arcsin_pos.mpr eps_pos

lemma alpha_lt_pi_div_two : α < π / 2 := Real.arcsin_lt_pi_div_two.mpr eps_lt_one

lemma sin_alpha : sin α = ε :=
  Real.sin_arcsin (by linarith [eps_pos]) (le_of_lt eps_lt_one)

/-- `d = α / (100 π)`: half-width, in `t`-units, of the rising window. -/
def d : ℝ := α / (100 * π)

lemma d_pos : 0 < d := div_pos alpha_pos hundred_pi_pos

lemma d_mul : d * (100 * π) = α := by
  simp only [d]
  field_simp

lemma d_lt : d < 1 / 200 := by
  have hπ := hundred_pi_pos
  by_contra hcon
  push_neg at hcon
  have h := mul_le_mul_of_nonneg_right hcon (le_of_lt hπ)
  rw [d_mul] at h
  have := alpha_lt_pi_div_two
  linarith

/-! ## 1.  The function `f`, its derivative, and monotonicity wrappers -/

/-- `f t = cos (100 π t) - (2.01 t - 1)`.  The original equation is `f (x^2) = 0`. -/
def f (t : ℝ) : ℝ := cos (100 * π * t) - (c * t - 1)

/-- The derivative of `f`. -/
def f' (t : ℝ) : ℝ := -(100 * π * sin (100 * π * t)) - c

lemma continuous_f : Continuous f := by
  unfold f
  fun_prop

lemma hasDerivAt_f (t : ℝ) : HasDerivAt f (f' t) t := by
  have h1 : HasDerivAt (fun s : ℝ => 100 * π * s) (100 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (100 * π)
  have h2 : HasDerivAt (fun s : ℝ => cos (100 * π * s))
      (-sin (100 * π * t) * (100 * π)) t := (Real.hasDerivAt_cos _).comp t h1
  have h3 : HasDerivAt (fun s : ℝ => c * s - 1) c t := by
    simpa using ((hasDerivAt_id t).const_mul c).sub_const 1
  have h := h2.sub h3
  have hEq : -sin (100 * π * t) * (100 * π) - c = f' t := by
    simp only [f']; ring
  rw [hEq] at h
  exact h

lemma deriv_f (t : ℝ) : deriv f t = f' t := (hasDerivAt_f t).deriv

lemma antiOn_of_f'_neg {s : Set ℝ} (hs : Convex ℝ s) (h : ∀ t ∈ interior s, f' t < 0) :
    StrictAntiOn f s :=
  strictAntiOn_of_deriv_neg hs continuous_f.continuousOn
    (fun t ht => by rw [deriv_f]; exact h t ht)

lemma monoOn_of_f'_pos {s : Set ℝ} (hs : Convex ℝ s) (h : ∀ t ∈ interior s, 0 < f' t) :
    StrictMonoOn f s :=
  strictMonoOn_of_deriv_pos hs continuous_f.continuousOn
    (fun t ht => by rw [deriv_f]; exact h t ht)

/-! ## 2.  Shifting by multiples of `π` -/

lemma sin_add_nat_mul_pi (x : ℝ) (n : ℕ) : sin (x + n * π) = (-1) ^ n * sin x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hx : x + ((n : ℝ) + 1) * π = (x + (n : ℝ) * π) + π := by ring
      push_cast
      rw [hx, Real.sin_add_pi, ih]
      ring

lemma cos_add_nat_mul_pi (x : ℝ) (n : ℕ) : cos (x + n * π) = (-1) ^ n * cos x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hx : x + ((n : ℝ) + 1) * π = (x + (n : ℝ) * π) + π := by ring
      push_cast
      rw [hx, Real.cos_add_pi, ih]
      ring

lemma sin_shift (k : ℕ) (t : ℝ) :
    sin (100 * π * t) = (-1) ^ k * sin (100 * π * t - k * π) := by
  have h := sin_add_nat_mul_pi (100 * π * t - (k : ℝ) * π) k
  have hx : 100 * π * t - (k : ℝ) * π + (k : ℝ) * π = 100 * π * t := by ring
  rw [hx] at h
  exact h

lemma cos_shift (k : ℕ) (t : ℝ) :
    cos (100 * π * t) = (-1) ^ k * cos (100 * π * t - k * π) := by
  have h := cos_add_nat_mul_pi (100 * π * t - (k : ℝ) * π) k
  have hx : 100 * π * t - (k : ℝ) * π + (k : ℝ) * π = 100 * π * t := by ring
  rw [hx] at h
  exact h

/-! ## 3.  Values of `f` at the grid points `k/100` -/

lemma cos_grid (k : ℕ) : cos (100 * π * ((k : ℝ) / 100)) = (-1) ^ k := by
  have h : (100 : ℝ) * π * ((k : ℝ) / 100) = 0 + (k : ℝ) * π := by ring
  rw [h, cos_add_nat_mul_pi]
  simp

lemma f_grid (k : ℕ) : f ((k : ℝ) / 100) = (-1) ^ k + 1 - c * k / 100 := by
  simp only [f, cos_grid]
  ring

lemma f_grid_even_pos {k : ℕ} (hk : Even k) (hk98 : k ≤ 98) : 0 < f ((k : ℝ) / 100) := by
  rw [f_grid, hk.neg_one_pow]
  have hkR : (k : ℝ) ≤ 98 := by exact_mod_cast hk98
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  simp only [c]
  linarith

lemma f_grid_odd_neg {k : ℕ} (hk : Odd k) : f ((k : ℝ) / 100) < 0 := by
  rw [f_grid, hk.neg_one_pow]
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simpa using hk)
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  simp only [c]
  linarith

lemma f_grid_ne (k : ℕ) (hk : k ≤ 99) : f ((k : ℝ) / 100) ≠ 0 := by
  rcases Nat.even_or_odd k with he | ho
  · have hk98 : k ≤ 98 := by
      have := Nat.even_iff.mp he
      omega
    exact ne_of_gt (f_grid_even_pos he hk98)
  · exact ne_of_lt (f_grid_odd_neg ho)

/-! ## 4.  The angle `θ = 100 π t - k π` and its range -/

lemma theta_nonneg {k : ℕ} {t : ℝ} (h : (k : ℝ) / 100 ≤ t) : 0 ≤ 100 * π * t - (k : ℝ) * π := by
  have hπ := Real.pi_pos
  nlinarith [h, hπ]

lemma theta_le_pi {k : ℕ} {t : ℝ} (h : t ≤ ((k : ℝ) + 1) / 100) :
    100 * π * t - (k : ℝ) * π ≤ π := by
  have hπ := Real.pi_pos
  nlinarith [h, hπ]

/-! ## 5.  Sine comparisons against `ε = sin α` -/

lemma sin_lt_sin_of_lt {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ π / 2) (h : x < y) : sin x < sin y := by
  have hπ := Real.pi_pos
  exact Real.strictMonoOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, hy⟩ h

/-- Just inside either end of `[0, π]`, `sin` is below `ε`. -/
lemma sin_lt_eps {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) (h : θ < α ∨ π - α < θ) : sin θ < ε := by
  rw [← sin_alpha]
  rcases h with h | h
  · exact sin_lt_sin_of_lt h0 (le_of_lt alpha_lt_pi_div_two) h
  · have hsub : sin θ = sin (π - θ) := (Real.sin_pi_sub θ).symm
    rw [hsub]
    exact sin_lt_sin_of_lt (by linarith) (le_of_lt alpha_lt_pi_div_two) (by linarith)

/-- Strictly between the two switch angles, `sin` exceeds `ε`. -/
lemma eps_lt_sin {θ : ℝ} (h1 : α < θ) (h2 : θ < π - α) : ε < sin θ := by
  rw [← sin_alpha]
  rcases le_total θ (π - θ) with hle | hle
  · -- θ ≤ π/2, compare directly
    have hhalf : θ ≤ π / 2 := by linarith
    exact sin_lt_sin_of_lt (le_of_lt alpha_pos) hhalf h1
  · -- θ ≥ π/2, reflect
    have hhalf : π - θ ≤ π / 2 := by linarith
    have hsub : sin θ = sin (π - θ) := (Real.sin_pi_sub θ).symm
    rw [hsub]
    exact sin_lt_sin_of_lt (le_of_lt alpha_pos) hhalf (by linarith)

/-! ## 6.  Sign of `f'` on the grid intervals -/

lemma f'_neg_even {k : ℕ} (hk : Even k) {t : ℝ}
    (h1 : (k : ℝ) / 100 ≤ t) (h2 : t ≤ ((k : ℝ) + 1) / 100) : f' t < 0 := by
  have hs : 0 ≤ sin (100 * π * t) := by
    rw [sin_shift k, hk.neg_one_pow, one_mul]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (theta_nonneg h1) (theta_le_pi h2)
  have hπ := Real.pi_pos
  have hprod : 0 ≤ 100 * π * sin (100 * π * t) := by positivity
  simp only [f']
  linarith [c_pos]

lemma f'_odd_eq {k : ℕ} (hk : Odd k) (t : ℝ) :
    f' t = 100 * π * sin (100 * π * t - (k : ℝ) * π) - c := by
  have hs : sin (100 * π * t) = -sin (100 * π * t - (k : ℝ) * π) := by
    rw [sin_shift k, hk.neg_one_pow]; ring
  simp only [f', hs]
  ring

/-! ## 7.  The switch points `a k` and `b k` -/

def a (k : ℕ) : ℝ := (k : ℝ) / 100 + d
def b (k : ℕ) : ℝ := ((k : ℝ) + 1) / 100 - d

lemma left_lt_a (k : ℕ) : (k : ℝ) / 100 < a k := by
  simp only [a]; linarith [d_pos]

lemma a_lt_b (k : ℕ) : a k < b k := by
  simp only [a, b]; linarith [d_lt]

lemma b_lt_right (k : ℕ) : b k < ((k : ℝ) + 1) / 100 := by
  simp only [b]; linarith [d_pos]

lemma theta_a (k : ℕ) : 100 * π * a k - (k : ℝ) * π = α := by
  simp only [a, d]
  field_simp
  ring

lemma theta_b (k : ℕ) : 100 * π * b k - (k : ℝ) * π = π - α := by
  simp only [b, d]
  field_simp
  ring

lemma theta_lt_alpha {k : ℕ} {t : ℝ} (h : t < a k) : 100 * π * t - (k : ℝ) * π < α := by
  have hmul : 100 * π * t < 100 * π * a k := mul_lt_mul_of_pos_left h hundred_pi_pos
  have := theta_a k
  linarith

lemma alpha_lt_theta {k : ℕ} {t : ℝ} (h : a k < t) : α < 100 * π * t - (k : ℝ) * π := by
  have hmul : 100 * π * a k < 100 * π * t := mul_lt_mul_of_pos_left h hundred_pi_pos
  have := theta_a k
  linarith

lemma theta_lt_pi_sub_alpha {k : ℕ} {t : ℝ} (h : t < b k) :
    100 * π * t - (k : ℝ) * π < π - α := by
  have hmul : 100 * π * t < 100 * π * b k := mul_lt_mul_of_pos_left h hundred_pi_pos
  have := theta_b k
  linarith

lemma pi_sub_alpha_lt_theta {k : ℕ} {t : ℝ} (h : b k < t) :
    π - α < 100 * π * t - (k : ℝ) * π := by
  have hmul : 100 * π * b k < 100 * π * t := mul_lt_mul_of_pos_left h hundred_pi_pos
  have := theta_b k
  linarith

/-! ## 8.  Sign of `f'` on the three pieces of an odd interval -/

lemma f'_neg_odd_left {k : ℕ} (hk : Odd k) {t : ℝ}
    (h1 : (k : ℝ) / 100 ≤ t) (h2 : t < a k) : f' t < 0 := by
  have hlt : sin (100 * π * t - (k : ℝ) * π) < ε := by
    refine sin_lt_eps (theta_nonneg h1) ?_ (Or.inl (theta_lt_alpha h2))
    refine theta_le_pi ?_
    have := (a_lt_b k).trans (b_lt_right k)
    linarith
  rw [f'_odd_eq hk]
  have hε : 100 * π * ε = c := by
    simp only [ε]
    field_simp
  nlinarith [hundred_pi_pos, hlt]

lemma f'_neg_odd_right {k : ℕ} (hk : Odd k) {t : ℝ}
    (h1 : b k < t) (h2 : t ≤ ((k : ℝ) + 1) / 100) : f' t < 0 := by
  have h0 : (k : ℝ) / 100 ≤ t := by
    have := (left_lt_a k).trans (a_lt_b k)
    linarith
  have hlt : sin (100 * π * t - (k : ℝ) * π) < ε :=
    sin_lt_eps (theta_nonneg h0) (theta_le_pi h2) (Or.inr (pi_sub_alpha_lt_theta h1))
  rw [f'_odd_eq hk]
  have hε : 100 * π * ε = c := by
    simp only [ε]; field_simp
  nlinarith [hundred_pi_pos, hlt]

lemma f'_pos_odd_mid {k : ℕ} (hk : Odd k) {t : ℝ}
    (h1 : a k < t) (h2 : t < b k) : 0 < f' t := by
  have hgt : ε < sin (100 * π * t - (k : ℝ) * π) :=
    eps_lt_sin (alpha_lt_theta h1) (theta_lt_pi_sub_alpha h2)
  rw [f'_odd_eq hk]
  have hε : 100 * π * ε = c := by
    simp only [ε]; field_simp
  nlinarith [hundred_pi_pos, hgt]

/-! ## 9.  Exactly one root in each grid interval `[k/100, (k+1)/100]`, `k ≤ 98` -/

lemma cast_succ (k : ℕ) : ((k : ℝ) + 1) / 100 = ((k + 1 : ℕ) : ℝ) / 100 := by
  push_cast; ring

theorem root_unique (k : ℕ) (hk : k ≤ 98) :
    ∃! t : ℝ, t ∈ Icc ((k : ℝ) / 100) (((k : ℝ) + 1) / 100) ∧ f t = 0 := by
  have hle : (k : ℝ) / 100 ≤ ((k : ℝ) + 1) / 100 := by linarith
  have hcont : ContinuousOn f (Icc ((k : ℝ) / 100) (((k : ℝ) + 1) / 100)) :=
    continuous_f.continuousOn
  rcases Nat.even_or_odd k with he | ho
  · ---------------------------------------------------------------- k even
    have hpos : 0 < f ((k : ℝ) / 100) := f_grid_even_pos he hk
    have hneg : f (((k : ℝ) + 1) / 100) < 0 := by
      rw [cast_succ k]
      exact f_grid_odd_neg (Even.add_one he)
    have hanti : StrictAntiOn f (Icc ((k : ℝ) / 100) (((k : ℝ) + 1) / 100)) := by
      refine antiOn_of_f'_neg (convex_Icc _ _) ?_
      intro t ht
      rw [interior_Icc] at ht
      exact f'_neg_even he (le_of_lt ht.1) (le_of_lt ht.2)
    have h0 : (0 : ℝ) ∈ Icc (f (((k : ℝ) + 1) / 100)) (f ((k : ℝ) / 100)) :=
      ⟨le_of_lt hneg, le_of_lt hpos⟩
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hle hcont h0
    refine ⟨t, ⟨ht, hft⟩, ?_⟩
    rintro y ⟨hy, hfy⟩
    exact hanti.injOn hy ht (hfy.trans hft.symm)
  · ---------------------------------------------------------------- k odd
    have hka : (k : ℝ) / 100 < a k := left_lt_a k
    have hab : a k < b k := a_lt_b k
    have hbk : b k < ((k : ℝ) + 1) / 100 := b_lt_right k
    have hstart : f ((k : ℝ) / 100) < 0 := f_grid_odd_neg ho
    have hend : 0 < f (((k : ℝ) + 1) / 100) := by
      rw [cast_succ k]
      refine f_grid_even_pos (Odd.add_one ho) ?_
      have := Nat.odd_iff.mp ho
      omega
    -- (i) strictly decreasing on [k/100, a k]
    have hanti1 : StrictAntiOn f (Icc ((k : ℝ) / 100) (a k)) := by
      refine antiOn_of_f'_neg (convex_Icc _ _) ?_
      intro t ht
      rw [interior_Icc] at ht
      exact f'_neg_odd_left ho (le_of_lt ht.1) ht.2
    -- (ii) strictly increasing on [a k, b k]
    have hmono : StrictMonoOn f (Icc (a k) (b k)) := by
      refine monoOn_of_f'_pos (convex_Icc _ _) ?_
      intro t ht
      rw [interior_Icc] at ht
      exact f'_pos_odd_mid ho ht.1 ht.2
    -- (iii) strictly decreasing on [b k, (k+1)/100]
    have hanti2 : StrictAntiOn f (Icc (b k) (((k : ℝ) + 1) / 100)) := by
      refine antiOn_of_f'_neg (convex_Icc _ _) ?_
      intro t ht
      rw [interior_Icc] at ht
      exact f'_neg_odd_right ho ht.1 (le_of_lt ht.2)
    -- f is negative on the whole left piece
    have hleft : ∀ y ∈ Icc ((k : ℝ) / 100) (a k), f y < 0 := by
      intro y hy
      rcases eq_or_lt_of_le hy.1 with h | h
      · rw [← h]; exact hstart
      · exact lt_trans (hanti1 (left_mem_Icc.mpr (le_of_lt hka)) hy h) hstart
    -- f is positive on the whole right piece
    have hright : ∀ y ∈ Icc (b k) (((k : ℝ) + 1) / 100), 0 < f y := by
      intro y hy
      rcases eq_or_lt_of_le hy.2 with h | h
      · rw [h]; exact hend
      · exact lt_trans hend (hanti2 hy (right_mem_Icc.mpr (le_of_lt hbk)) h)
    have hfa : f (a k) < 0 := hleft _ (right_mem_Icc.mpr (le_of_lt hka))
    have hfb : 0 < f (b k) := hright _ (left_mem_Icc.mpr (le_of_lt hbk))
    -- existence, by IVT on the increasing piece
    have hcont' : ContinuousOn f (Icc (a k) (b k)) := continuous_f.continuousOn
    have h0 : (0 : ℝ) ∈ Icc (f (a k)) (f (b k)) := ⟨le_of_lt hfa, le_of_lt hfb⟩
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (le_of_lt hab) hcont' h0
    have htmem : t ∈ Icc ((k : ℝ) / 100) (((k : ℝ) + 1) / 100) :=
      ⟨le_trans (le_of_lt hka) ht.1, le_trans ht.2 (le_of_lt hbk)⟩
    refine ⟨t, ⟨htmem, hft⟩, ?_⟩
    rintro y ⟨hy, hfy⟩
    rcases le_or_gt y (a k) with hy1 | hy1
    · exact absurd hfy (ne_of_lt (hleft y ⟨hy.1, hy1⟩))
    rcases le_or_gt (b k) y with hy2 | hy2
    · exact absurd hfy (ne_of_gt (hright y ⟨hy2, hy.2⟩))
    · exact hmono.injOn ⟨le_of_lt hy1, le_of_lt hy2⟩ ht (hfy.trans hft.symm)

/-! ## 10.  No roots outside `[0, 0.99)` -/

lemma f_pos_of_neg {t : ℝ} (ht : t < 0) : 0 < f t := by
  have h1 : -1 ≤ cos (100 * π * t) := Real.neg_one_le_cos _
  have h2 : c * t - 1 < -1 := by
    have : c * t < 0 := mul_neg_of_pos_of_neg c_pos ht
    linarith
  simp only [f]
  linarith

lemma cos_two_pi_div_three : cos (2 * π / 3) = -(1 / 2) := by
  have h : (2 * π / 3) = π - π / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]

lemma f_neg_of_tail {t : ℝ} (ht : 99 / 100 ≤ t) : f t < 0 := by
  have hπ := Real.pi_pos
  rcases le_or_gt t (200 / 201) with hup | hup
  · -- 0.99 ≤ t ≤ 200/201 : cos is near -1 · (something small)
    set θ : ℝ := 100 * π * t - 99 * π with hθ
    have hθ0 : 0 ≤ θ := by rw [hθ]; nlinarith
    have hθ1 : θ < 2 * π / 3 := by
      rw [hθ]; nlinarith
    have hcosθ : -(1 / 2) < cos θ := by
      rw [← cos_two_pi_div_three]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi hθ0 (by linarith) hθ1
    have hshift : cos (100 * π * t) = -cos θ := by
      have := cos_shift 99 t
      rw [hθ]
      push_cast at this ⊢
      rw [this]
      norm_num
    have hrhs : (9899 : ℝ) / 10000 ≤ c * t - 1 := by
      simp only [c]; linarith
    simp only [f, hshift]
    linarith
  · -- t > 200/201 : the line has already left [-1, 1]
    have h1 : cos (100 * π * t) ≤ 1 := Real.cos_le_one _
    have h2 : (1 : ℝ) < c * t - 1 := by
      simp only [c]; linarith
    simp only [f]
    linarith

lemma f_ne_of_ge {t : ℝ} (ht : 99 / 100 ≤ t) : f t ≠ 0 := ne_of_lt (f_neg_of_tail ht)

/-! ## 11.  The root set in `t`, and its cardinality -/

def T : Set ℝ := {t : ℝ | f t = 0}

lemma fin99_le (k : Fin 99) : k.val ≤ 98 := by
  have := k.isLt; omega

def r (k : Fin 99) : ℝ := (root_unique k.val (fin99_le k)).choose

lemma r_spec (k : Fin 99) :
    r k ∈ Icc ((k.val : ℝ) / 100) (((k.val : ℝ) + 1) / 100) ∧ f (r k) = 0 :=
  (root_unique k.val (fin99_le k)).choose_spec.1

lemma r_uniq (k : Fin 99) {y : ℝ}
    (hy : y ∈ Icc ((k.val : ℝ) / 100) (((k.val : ℝ) + 1) / 100)) (hfy : f y = 0) :
    y = r k :=
  (root_unique k.val (fin99_le k)).choose_spec.2 y ⟨hy, hfy⟩

lemma r_mem_Ioo (k : Fin 99) : r k ∈ Ioo ((k.val : ℝ) / 100) (((k.val : ℝ) + 1) / 100) := by
  obtain ⟨⟨h1, h2⟩, h0⟩ := r_spec k
  constructor
  · rcases eq_or_lt_of_le h1 with h | h
    · exfalso
      refine f_grid_ne k.val (by have := k.isLt; omega) ?_
      rw [h]; exact h0
    · exact h
  · rcases eq_or_lt_of_le h2 with h | h
    · exfalso
      refine f_grid_ne (k.val + 1) (by have := k.isLt; omega) ?_
      rw [← cast_succ k.val, ← h]; exact h0
    · exact h

lemma r_injective : Function.Injective r := by
  intro i j hij
  by_contra hne
  have h : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have h1 := (r_mem_Ioo i).2
    have h2 := (r_mem_Ioo j).1
    rw [hij] at h1
    have hcast : ((i.val : ℝ) + 1) ≤ (j.val : ℝ) := by
      have : i.val + 1 ≤ j.val := hlt
      exact_mod_cast this
    linarith
  · have h1 := (r_mem_Ioo j).2
    have h2 := (r_mem_Ioo i).1
    rw [← hij] at h1
    have hcast : ((j.val : ℝ) + 1) ≤ (i.val : ℝ) := by
      have : j.val + 1 ≤ i.val := hlt
      exact_mod_cast this
    linarith

lemma T_eq_range : T = Set.range r := by
  ext t
  constructor
  · intro ht
    have hft : f t = 0 := ht
    have h0 : 0 ≤ t := by
      by_contra h
      push_neg at h
      exact absurd hft (ne_of_gt (f_pos_of_neg h))
    have h99 : t < 99 / 100 := by
      by_contra h
      push_neg at h
      exact f_ne_of_ge h hft
    have h100 : (0 : ℝ) ≤ 100 * t := by linarith
    set k := ⌊100 * t⌋₊ with hk
    have hk99 : k < 99 := by
      rw [hk]
      refine (Nat.floor_lt h100).mpr ?_
      push_cast
      linarith
    have hlow : (k : ℝ) / 100 ≤ t := by
      have := Nat.floor_le h100
      rw [← hk] at this
      linarith
    have hhigh : t ≤ ((k : ℝ) + 1) / 100 := by
      have := Nat.lt_floor_add_one (100 * t)
      rw [← hk] at this
      linarith
    exact ⟨⟨k, hk99⟩, (r_uniq ⟨k, hk99⟩ ⟨hlow, hhigh⟩ hft).symm⟩
  · rintro ⟨k, rfl⟩
    exact (r_spec k).2

lemma T_finite : T.Finite := by
  rw [T_eq_range]; exact Set.finite_range r

lemma T_ncard : T.ncard = 99 := by
  rw [T_eq_range, ← Set.image_univ, Set.ncard_image_of_injective _ r_injective,
      Set.ncard_univ]
  simp

lemma T_pos {t : ℝ} (ht : t ∈ T) : 0 < t := by
  rw [T_eq_range] at ht
  obtain ⟨k, rfl⟩ := ht
  have h1 := (r_mem_Ioo k).1
  have h2 : (0 : ℝ) ≤ (k.val : ℝ) / 100 := by positivity
  linarith

/-! ## 12.  Transfer along `x ↦ x²` and conclude -/

lemma f_eq_zero_iff (t : ℝ) : f t = 0 ↔ cos (100 * π * t) = 2.01 * t - 1 := by
  rw [f, sub_eq_zero]
  norm_num [c]

lemma sqrt_injOn : Set.InjOn Real.sqrt T := by
  intro x hx y hy h
  have hx' : Real.sqrt x ^ 2 = x := Real.sq_sqrt (T_pos hx).le
  have hy' : Real.sqrt y ^ 2 = y := Real.sq_sqrt (T_pos hy).le
  rw [← hx', ← hy', h]

lemma neg_sqrt_injOn : Set.InjOn (fun t => -Real.sqrt t) T := by
  intro x hx y hy h
  simp only [neg_inj] at h
  exact sqrt_injOn hx hy h

lemma S_eq :
    {x : ℝ | Real.cos (100 * Real.pi * x ^ 2) = 2.01 * x ^ 2 - 1}
      = Real.sqrt '' T ∪ (fun t => -Real.sqrt t) '' T := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image, ← f_eq_zero_iff]
  constructor
  · intro hx
    have hT : x ^ 2 ∈ T := hx
    have hs : Real.sqrt (x ^ 2) = |x| := Real.sqrt_sq_eq_abs x
    rcases le_or_gt 0 x with h1 | h1
    · exact Or.inl ⟨x ^ 2, hT, by rw [hs, abs_of_nonneg h1]⟩
    · exact Or.inr ⟨x ^ 2, hT, by rw [hs, abs_of_neg h1]; ring⟩
  · rintro (⟨t, htT, rfl⟩ | ⟨t, htT, rfl⟩)
    · rwa [Real.sq_sqrt (T_pos htT).le]
    · rwa [neg_sq, Real.sq_sqrt (T_pos htT).le]

lemma S_disjoint : Disjoint (Real.sqrt '' T) ((fun t => -Real.sqrt t) '' T) := by
  rw [Set.disjoint_left]
  rintro x ⟨t, htT, rfl⟩ ⟨s, hsT, hs⟩
  have h1 : 0 < Real.sqrt t := Real.sqrt_pos.mpr (T_pos htT)
  have h2 : 0 < Real.sqrt s := Real.sqrt_pos.mpr (T_pos hsT)
  simp only at hs
  linarith

end CosCount

open CosCount in
theorem cos_eq_solutions_count :
    Set.ncard { x : ℝ | Real.cos (100 * Real.pi * x ^ 2) = 2.01 * x ^ 2 - 1 } = 198 := by
  rw [S_eq,
      Set.ncard_union_eq S_disjoint (T_finite.image _) (T_finite.image _),
      Set.ncard_image_of_injOn sqrt_injOn,
      Set.ncard_image_of_injOn neg_sqrt_injOn,
      T_ncard]

/-
  KNOWN RISK POINTS (unverified — this file has not been through the elaborator)
  =============================================================================

  1.  `StrictAntiOn_of_deriv_neg` / `StrictMonoOn_of_deriv_pos`.  These have been
      renamed at least once; on recent Mathlib try `strictAntiOn_of_deriv_neg` and
      `strictMonoOn_of_deriv_pos`, or the `inner_le_nnorm`-style `StrictAntiOn` API
      via `StrictAntiOn.of_deriv_neg`.

  2.  `Real.arcsin_lt_pi_div_two`, `Real.arcsin_pos`, `Real.strictMonoOn_sin`,
      `Real.cos_lt_cos_of_nonneg_of_le_pi`, `Real.sin_add_pi`, `Real.cos_add_pi`,
      `Real.sin_pi_sub`, `Real.cos_pi_sub`, `Real.cos_pi_div_three`, `Real.sq_sqrt`,
      `Real.sqrt_sq_eq_abs` — all believed to exist with these exact names, but worth
      a `exact?` if any fails.

  3.  The `nlinarith` calls in `theta_nonneg`, `theta_le_pi`, `f_neg_of_tail`, and the
      three `f'_*` lemmas are the most likely to need hand-holding.  Each is a
      multiplication of a hypothesis by `100 * π > 0`; if `nlinarith` stalls, replace
      with an explicit `mul_le_mul_of_nonneg_left` / `mul_lt_mul_of_pos_left` step
      followed by `linarith`.

  4.  `hshift` in `f_neg_of_tail` does `cos_shift 99` and then needs `(-1)^99 = -1`.
      The `push_cast`/`norm_num` combination there is the shakiest line in the file;
      the clean version is
        `have h99 : ((-1 : ℝ)) ^ (99 : ℕ) = -1 := Odd.neg_one_pow (by decide)`
      and then rewriting explicitly.

  5.  `f_eq_zero_iff` relies on `norm_num` identifying the scientific literal `2.01`
      with `201 / 100`.  If it does not, `show (201 : ℝ)/100 = 2.01 by norm_num` first,
      or restate the top-level theorem with `c`.

  6.  `Set.ncard_union_eq` argument order (disjointness first, then the two finiteness
      proofs) has varied; check the signature.

  MATHEMATICAL CONTENT: I believe the argument itself is airtight.  The numeric margins
  are comfortable everywhere except one place — `f (98/100) = 2 - 1.9698 = 0.0302 > 0`
  is what makes the 99th interval work, and it is the reason the answer is 198 rather
  than 196.  If you perturb 2.01 upward past roughly 2.0202, that interval dies.
-/
```
