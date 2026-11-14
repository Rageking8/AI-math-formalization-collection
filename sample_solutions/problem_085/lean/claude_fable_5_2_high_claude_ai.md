# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `14 November 2026`\
Line count: `185`\
Turn count: `2`

## Solution

```lean4
import Mathlib

def C : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | p.1 > 0 ∧ p.1 * p.2 ^ 13 - 4 * p.2 = p.1 ^ (5 * p.1) - 3 * p.1 - 1 }

def verticalLine (x₀ : ℝ) : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | p.1 = x₀ }

theorem max_vertical_intersections_xy13_4y :
    (∀ x₀ : ℝ, Set.encard (C ∩ verticalLine x₀) ≤ 3) ∧
      (∃ x₀ : ℝ, Set.encard (C ∩ verticalLine x₀) = 3) := by
  -- Step 1 (Rolle twice): for a > 0, `a y¹³ - 4 y = c` has at most 3 real solutions.
  -- NB: `C` is the curve here, so the polynomial constant map is written `Polynomial.C`.
  have key : ∀ a c : ℝ, 0 < a →
      ∃ R : Finset ℝ, R.card ≤ 3 ∧ ∀ y : ℝ, a * y ^ 13 - 4 * y = c → y ∈ R := by
    intro a c ha
    obtain ⟨p, hp⟩ : ∃ p : Polynomial ℝ,
        p = Polynomial.C a * Polynomial.X ^ 13 - Polynomial.C (4 : ℝ) * Polynomial.X
          - Polynomial.C c := ⟨_, rfl⟩
    -- values of p, p', p''
    have e0 : ∀ y : ℝ, Polynomial.eval y p = a * y ^ 13 - 4 * y - c := by
      intro y
      rw [hp]
      first
        | (simp; done)
        | (simp; ring1)
        | (simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_pow, Polynomial.eval_X]; done)
        | (simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_pow, Polynomial.eval_X]; ring1)
    have e1 : ∀ y : ℝ,
        Polynomial.eval y (Polynomial.derivative p) = 13 * a * y ^ 12 - 4 := by
      intro y
      rw [hp]
      first
        | (simp [Polynomial.derivative_X_pow]; done)
        | (simp [Polynomial.derivative_X_pow]; ring1)
        | (simp only [Polynomial.derivative_sub, Polynomial.derivative_C_mul,
            Polynomial.derivative_X_pow, Polynomial.derivative_C, Polynomial.derivative_X,
            Polynomial.derivative_one, Polynomial.derivative_zero,
            Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
            Polynomial.eval_zero]
           norm_num <;> ring1)
    have e2 : ∀ y : ℝ,
        Polynomial.eval y (Polynomial.derivative (Polynomial.derivative p))
          = 156 * a * y ^ 11 := by
      intro y
      rw [hp]
      first
        | (simp [Polynomial.derivative_X_pow]; done)
        | (simp [Polynomial.derivative_X_pow]; ring1)
        | (simp only [Polynomial.derivative_sub, Polynomial.derivative_C_mul,
            Polynomial.derivative_X_pow, Polynomial.derivative_C, Polynomial.derivative_X,
            Polynomial.derivative_one, Polynomial.derivative_zero,
            Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
            Polynomial.eval_zero]
           norm_num <;> ring1)
    -- p ≠ 0 and p'' ≠ 0
    have hp0 : p ≠ 0 := by
      intro h
      have h0 := e0 0
      have h1 := e0 1
      have h2 := e0 2
      rw [h, Polynomial.eval_zero] at h0 h1 h2
      linarith
    have hdd0 : Polynomial.derivative (Polynomial.derivative p) ≠ 0 := by
      intro h
      have h1 := e2 1
      rw [h, Polynomial.eval_zero] at h1
      linarith
    -- p'' has at most one root (namely 0)
    have c2 : (Polynomial.derivative (Polynomial.derivative p)).roots.toFinset.card ≤ 1 := by
      have z : ∀ y ∈ (Polynomial.derivative (Polynomial.derivative p)).roots.toFinset,
          y = 0 := by
        intro y hy
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hdd0, Polynomial.IsRoot.def, e2] at hy
        have h156 : (156 : ℝ) * a ≠ 0 := (mul_pos (by norm_num) ha).ne'
        have hy11 : y ^ 11 = 0 := (mul_eq_zero.mp hy).resolve_left h156
        first
          | exact (pow_eq_zero_iff (by norm_num)).mp hy11
          | simpa using hy11
      rw [Finset.card_le_one]
      intro x hx y hy
      rw [z x hx, z y hy]
    -- Rolle: #roots p ≤ #roots p' + 1 ≤ #roots p'' + 2 ≤ 3
    have c1 := Polynomial.card_roots_toFinset_le_derivative (Polynomial.derivative p)
    have c0 := Polynomial.card_roots_toFinset_le_derivative p
    refine ⟨p.roots.toFinset, by omega, ?_⟩
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def, e0]
    linarith
  -- Step 2: the upper bound for every vertical line.
  have part1 : ∀ x₀ : ℝ, Set.encard (C ∩ verticalLine x₀) ≤ 3 := by
    intro x₀
    by_cases hx : 0 < x₀
    · obtain ⟨R, hR3, hR⟩ := key x₀ (x₀ ^ (5 * x₀) - 3 * x₀ - 1) hx
      have hsub : C ∩ verticalLine x₀ ⊆
          (fun y : ℝ => ((x₀, y) : ℝ × ℝ)) '' (R : Set ℝ) := by
        intro q hq
        have hq1 : q.1 > 0 ∧
            q.1 * q.2 ^ 13 - 4 * q.2 = q.1 ^ (5 * q.1) - 3 * q.1 - 1 := hq.1
        have hq2 : q.1 = x₀ := hq.2
        rw [hq2] at hq1
        exact ⟨q.2, Finset.mem_coe.mpr (hR q.2 hq1.2), Prod.ext hq2.symm rfl⟩
      have s1 : (C ∩ verticalLine x₀).encard ≤
          ((fun y : ℝ => ((x₀, y) : ℝ × ℝ)) '' (R : Set ℝ)).encard := Set.encard_mono hsub
      have s2 : ((fun y : ℝ => ((x₀, y) : ℝ × ℝ)) '' (R : Set ℝ)).encard ≤
          (R : Set ℝ).encard := Set.encard_image_le _ _
      have s3 : (R : Set ℝ).encard = (R.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard R
      have s4 : (R.card : ℕ∞) ≤ 3 := by exact_mod_cast hR3
      exact s1.trans (s2.trans (s3.le.trans s4))
    · have hempty : C ∩ verticalLine x₀ = ∅ := by
        apply Set.eq_empty_of_subset_empty
        intro q hq
        have hq1 : q.1 > 0 ∧
            q.1 * q.2 ^ 13 - 4 * q.2 = q.1 ^ (5 * q.1) - 3 * q.1 - 1 := hq.1
        have hq2 : q.1 = x₀ := hq.2
        exact absurd (lt_of_lt_of_eq hq1.1 hq2) hx
      rw [hempty, Set.encard_empty]
      exact zero_le
  -- Step 3: the line x = 1 meets the curve in exactly 3 points.
  -- On x = 1 the equation reads y¹³ - 4y = -3, with roots in [-2,-1], in [0, 9/10], and y = 1.
  refine ⟨part1, 1, ?_⟩
  have hcont : Continuous (fun y : ℝ => y ^ 13 - 4 * y) := by
    first
      | fun_prop
      | continuity
      | exact (continuous_pow 13).sub (continuous_const.mul continuous_id)
  have h1 : (-3 : ℝ) ∈ (fun y : ℝ => y ^ 13 - 4 * y) '' Set.Icc (-2 : ℝ) (-1) := by
    have hab : (-2 : ℝ) ≤ -1 := by norm_num
    have hI := intermediate_value_Icc hab (f := fun y : ℝ => y ^ 13 - 4 * y)
      hcont.continuousOn
    apply hI
    rw [Set.mem_Icc]
    constructor <;> norm_num
  have h2 : (-3 : ℝ) ∈ (fun y : ℝ => y ^ 13 - 4 * y) '' Set.Icc (0 : ℝ) (9 / 10) := by
    have hab : (0 : ℝ) ≤ 9 / 10 := by norm_num
    have hI := intermediate_value_Icc' hab (f := fun y : ℝ => y ^ 13 - 4 * y)
      hcont.continuousOn
    apply hI
    rw [Set.mem_Icc]
    constructor <;> norm_num
  obtain ⟨r₁, hr₁, hr₁eq⟩ := h1
  obtain ⟨r₂, hr₂, hr₂eq⟩ := h2
  have hr₁eq' : r₁ ^ 13 - 4 * r₁ = -3 := hr₁eq
  have hr₂eq' : r₂ ^ 13 - 4 * r₂ = -3 := hr₂eq
  have hr₁b : r₁ ≤ -1 := hr₁.2
  have hr₂a : 0 ≤ r₂ := hr₂.1
  have hr₂b : r₂ ≤ 9 / 10 := hr₂.2
  -- every root of y¹³ - 4y = -3 gives a point of the curve on the line x = 1
  have mem : ∀ r : ℝ, r ^ 13 - 4 * r = -3 → ((1 : ℝ), r) ∈ C ∩ verticalLine 1 := by
    intro r hr
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show (1 : ℝ) > 0
      norm_num
    · show (1 : ℝ) * r ^ 13 - 4 * r = (1 : ℝ) ^ (5 * (1 : ℝ)) - 3 * 1 - 1
      rw [Real.one_rpow]
      linarith
    · show ((1 : ℝ), r).1 = 1
      rfl
  have h12 : ((1 : ℝ), r₁) ≠ ((1 : ℝ), r₂) := by
    intro h
    have h' : r₁ = r₂ := congrArg Prod.snd h
    linarith
  have h13 : ((1 : ℝ), r₁) ≠ ((1 : ℝ), (1 : ℝ)) := by
    intro h
    have h' : r₁ = 1 := congrArg Prod.snd h
    linarith
  have h23 : ((1 : ℝ), r₂) ≠ ((1 : ℝ), (1 : ℝ)) := by
    intro h
    have h' : r₂ = 1 := congrArg Prod.snd h
    linarith
  have h3 : ({((1 : ℝ), r₁), ((1 : ℝ), r₂), ((1 : ℝ), (1 : ℝ))} : Set (ℝ × ℝ)).encard = 3 :=
    Set.encard_eq_three.mpr ⟨_, _, _, h12, h13, h23, rfl⟩
  have hsub3 : ({((1 : ℝ), r₁), ((1 : ℝ), r₂), ((1 : ℝ), (1 : ℝ))} : Set (ℝ × ℝ)) ⊆
      C ∩ verticalLine 1 := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact mem r₁ hr₁eq'
    · exact mem r₂ hr₂eq'
    · exact mem 1 (by norm_num)
  exact le_antisymm (part1 1) (h3.symm.le.trans (Set.encard_mono hsub3))
```
