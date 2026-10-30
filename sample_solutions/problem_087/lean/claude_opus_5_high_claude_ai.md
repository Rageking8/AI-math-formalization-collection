# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `2 September 2026`\
Line count: `495`\
Turn count: `5`

## Note

The conversation contained 1 "Continue" message not included in the turn count.

## Solution

```lean4
import Mathlib

open Finset Filter Topology

namespace DoubleSumSgnFactorial

/-! ## Reindexed summand

With `m = a+1`, `n = b+1` the summand becomes
`(sign (2a - b - 4) + (-1)^(min a b)) / (max a b + 2)!`. -/

noncomputable def F (a b : ℕ) : ℝ :=
  (((Int.sign (2 * (a : ℤ) - (b : ℤ) - 4) : ℤ) : ℝ) + (-1 : ℝ) ^ (min a b)) /
    (Nat.factorial (max a b + 2) : ℝ)

/-- Correction to the generic block constant, supported on `{0, 2, 3}`. -/
noncomputable def Cc (M : ℕ) : ℝ :=
  if M = 0 then 3 else if M = 2 then -2 else if M = 3 then -1 else 0

/-- Total contribution of the `L`-shaped block `max a b = M`, times `(M+2)!`. -/
noncomputable def C (M : ℕ) : ℝ := ((M : ℝ) - 3) + Cc M

lemma F_def (a b : ℕ) :
    F a b = (((Int.sign (2 * (a : ℤ) - (b : ℤ) - 4) : ℤ) : ℝ) + (-1 : ℝ) ^ (min a b)) /
      (Nat.factorial (max a b + 2) : ℝ) := rfl

/-! ## Sign helpers -/

lemma sgn_neg' {x : ℤ} (h : x < 0) : ((Int.sign x : ℤ) : ℝ) = -1 := by
  rw [Int.sign_eq_neg_one_of_neg h]; norm_num

lemma sgn_pos' {x : ℤ} (h : 0 < x) : ((Int.sign x : ℤ) : ℝ) = 1 := by
  rw [Int.sign_eq_one_of_pos h]; norm_num

lemma sgn_zero' {x : ℤ} (h : x = 0) : ((Int.sign x : ℤ) : ℝ) = 0 := by
  subst h; simp

/-- Decidable-friendly form, used to evaluate the small cases. -/
lemma sign_real (x : ℤ) :
    ((Int.sign x : ℤ) : ℝ) = if x = 0 then 0 else if 0 < x then 1 else -1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [sgn_neg' h, if_neg (by omega), if_neg (by omega)]
  · rw [sgn_zero' h, if_pos h]
  · rw [sgn_pos' h, if_neg (by omega), if_pos h]

lemma fact_ne_zero (k : ℕ) : (Nat.factorial k : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)

lemma fact_pos' (k : ℕ) : (0 : ℝ) < Nat.factorial k :=
  Nat.cast_pos.mpr (Nat.factorial_pos k)

/-! ## Alternating sums -/

lemma alt_sum (N : ℕ) : ∑ k ∈ range N, (-1 : ℝ) ^ k = (1 - (-1) ^ N) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/-! ## The two sign sums along an `L` -/

lemma sign_row (N : ℕ) (hN : 5 ≤ N) :
    ∑ b ∈ range N, ((Int.sign (2 * (N : ℤ) - (b : ℤ) - 4) : ℤ) : ℝ) = (N : ℝ) := by
  have hcongr : ∀ b ∈ range N,
      ((Int.sign (2 * (N : ℤ) - (b : ℤ) - 4) : ℤ) : ℝ) = 1 := by
    intro b hb
    have hb' : (b : ℤ) < (N : ℤ) := by exact_mod_cast Finset.mem_range.1 hb
    have hN' : (5 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    exact sgn_pos' (by omega)
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]

lemma sign_col (N : ℕ) (hN : 5 ≤ N) :
    ∑ a ∈ range N, ((Int.sign (2 * (a : ℤ) - (N : ℤ) - 4) : ℤ) : ℝ) = -5 := by
  rcases Nat.even_or_odd N with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- `N = j + j`, so `N ≥ 6` and `j ≥ 3`
    subst hj
    have hj3 : 3 ≤ j := by omega
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (j + 2)) (by omega : j + 2 ≤ j + j),
      ← Finset.sum_Ico_consecutive _ (by omega : j + 2 ≤ j + 3) (by omega : j + 3 ≤ j + j)]
    have h1 : ∑ a ∈ Ico 0 (j + 2),
        ((Int.sign (2 * (a : ℤ) - ((j + j : ℕ) : ℤ) - 4) : ℤ) : ℝ) = -((j : ℝ) + 2) := by
      have hall : ∀ a ∈ Ico 0 (j + 2),
          ((Int.sign (2 * (a : ℤ) - ((j + j : ℕ) : ℤ) - 4) : ℤ) : ℝ) = -1 := by
        intro a ha
        have ha0 : a < j + 2 := (Finset.mem_Ico.1 ha).2
        have ha' : (a : ℤ) < (j : ℤ) + 2 := by
          have hc : ((a : ℕ) : ℤ) < ((j + 2 : ℕ) : ℤ) := by exact_mod_cast ha0
          push_cast at hc; omega
        refine sgn_neg' ?_
        push_cast
        omega
      rw [Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      push_cast
      ring
    have h2 : ∑ a ∈ Ico (j + 2) (j + 3),
        ((Int.sign (2 * (a : ℤ) - ((j + j : ℕ) : ℤ) - 4) : ℤ) : ℝ) = 0 := by
      have hall : ∀ a ∈ Ico (j + 2) (j + 3),
          ((Int.sign (2 * (a : ℤ) - ((j + j : ℕ) : ℤ) - 4) : ℤ) : ℝ) = 0 := by
        intro a ha
        obtain ⟨hl, hr⟩ := Finset.mem_Ico.1 ha
        have hae : a = j + 2 := by omega
        subst hae
        refine sgn_zero' ?_
        push_cast
        ring
      rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero]
    have h3 : ∑ a ∈ Ico (j + 3) (j + j),
        ((Int.sign (2 * (a : ℤ) - ((j + j : ℕ) : ℤ) - 4) : ℤ) : ℝ) = (j : ℝ) - 3 := by
      have hall : ∀ a ∈ Ico (j + 3) (j + j),
          ((Int.sign (2 * (a : ℤ) - ((j + j : ℕ) : ℤ) - 4) : ℤ) : ℝ) = 1 := by
        intro a ha
        have hl : j + 3 ≤ a := (Finset.mem_Ico.1 ha).1
        have hl' : (j : ℤ) + 3 ≤ (a : ℤ) := by
          have hc : ((j + 3 : ℕ) : ℤ) ≤ (a : ℤ) := by exact_mod_cast hl
          push_cast at hc; omega
        refine sgn_pos' ?_
        push_cast
        omega
      rw [Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
        Nat.cast_sub (by omega : j + 3 ≤ j + j)]
      push_cast
      ring
    rw [h1, h2, h3]
    ring
  · -- `N = 2 * j + 1`, so `j ≥ 2`
    subst hj
    have hj2 : 2 ≤ j := by omega
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (j + 3)) (by omega : j + 3 ≤ 2 * j + 1)]
    have h1 : ∑ a ∈ Ico 0 (j + 3),
        ((Int.sign (2 * (a : ℤ) - ((2 * j + 1 : ℕ) : ℤ) - 4) : ℤ) : ℝ) = -((j : ℝ) + 3) := by
      have hall : ∀ a ∈ Ico 0 (j + 3),
          ((Int.sign (2 * (a : ℤ) - ((2 * j + 1 : ℕ) : ℤ) - 4) : ℤ) : ℝ) = -1 := by
        intro a ha
        have ha0 : a < j + 3 := (Finset.mem_Ico.1 ha).2
        have ha' : (a : ℤ) < (j : ℤ) + 3 := by
          have hc : ((a : ℕ) : ℤ) < ((j + 3 : ℕ) : ℤ) := by exact_mod_cast ha0
          push_cast at hc; omega
        refine sgn_neg' ?_
        push_cast
        omega
      rw [Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      push_cast
      ring
    have h2 : ∑ a ∈ Ico (j + 3) (2 * j + 1),
        ((Int.sign (2 * (a : ℤ) - ((2 * j + 1 : ℕ) : ℤ) - 4) : ℤ) : ℝ) = (j : ℝ) - 2 := by
      have hall : ∀ a ∈ Ico (j + 3) (2 * j + 1),
          ((Int.sign (2 * (a : ℤ) - ((2 * j + 1 : ℕ) : ℤ) - 4) : ℤ) : ℝ) = 1 := by
        intro a ha
        have hl : j + 3 ≤ a := (Finset.mem_Ico.1 ha).1
        have hl' : (j : ℤ) + 3 ≤ (a : ℤ) := by
          have hc : ((j + 3 : ℕ) : ℤ) ≤ (a : ℤ) := by exact_mod_cast hl
          push_cast at hc; omega
        refine sgn_pos' ?_
        push_cast
        omega
      rw [Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
        Nat.cast_sub (by omega : j + 3 ≤ 2 * j + 1)]
      push_cast
      ring
    rw [h1, h2]
    ring

/-! ## The `L`-shaped block sums to `C N / (N+2)!` -/

lemma Lshape_big (N : ℕ) (hN : 5 ≤ N) :
    (∑ b ∈ range N, F N b) + (∑ a ∈ range N, F a N) + F N N
      = C N / (Nat.factorial (N + 2) : ℝ) := by
  have hfac : (Nat.factorial (N + 2) : ℝ) ≠ 0 := fact_ne_zero _
  have hrow : ∀ b ∈ range N,
      F N b = ((Int.sign (2 * (N : ℤ) - (b : ℤ) - 4) : ℤ) : ℝ) / (Nat.factorial (N + 2) : ℝ)
              + (-1 : ℝ) ^ b / (Nat.factorial (N + 2) : ℝ) := by
    intro b hb
    have hb' : b < N := Finset.mem_range.1 hb
    have hmin : min N b = b := min_eq_right hb'.le
    have hmax : max N b = N := max_eq_left hb'.le
    rw [F_def, hmin, hmax, add_div]
  have hcol : ∀ a ∈ range N,
      F a N = ((Int.sign (2 * (a : ℤ) - (N : ℤ) - 4) : ℤ) : ℝ) / (Nat.factorial (N + 2) : ℝ)
              + (-1 : ℝ) ^ a / (Nat.factorial (N + 2) : ℝ) := by
    intro a ha
    have ha' : a < N := Finset.mem_range.1 ha
    have hmin : min a N = a := min_eq_left ha'.le
    have hmax : max a N = N := max_eq_right ha'.le
    rw [F_def, hmin, hmax, add_div]
  have hrowsum : ∑ b ∈ range N, F N b
      = ((N : ℝ) + (1 - (-1 : ℝ) ^ N) / 2) / (Nat.factorial (N + 2) : ℝ) := by
    rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
      sign_row N hN, alt_sum N, ← add_div]
  have hcolsum : ∑ a ∈ range N, F a N
      = ((-5 : ℝ) + (1 - (-1 : ℝ) ^ N) / 2) / (Nat.factorial (N + 2) : ℝ) := by
    rw [Finset.sum_congr rfl hcol, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
      sign_col N hN, alt_sum N, ← add_div]
  have hdiag : F N N = (1 + (-1 : ℝ) ^ N) / (Nat.factorial (N + 2) : ℝ) := by
    have hN' : (5 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    rw [F_def, min_self, max_self,
      sgn_pos' (by omega : (0 : ℤ) < 2 * (N : ℤ) - (N : ℤ) - 4)]
  have hCc : Cc N = 0 := by
    simp only [Cc]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [hrowsum, hcolsum, hdiag]
  simp only [C, hCc, add_zero]
  field_simp
  ring

lemma Lshape (N : ℕ) :
    (∑ b ∈ range N, F N b) + (∑ a ∈ range N, F a N) + F N N
      = C N / (Nat.factorial (N + 2) : ℝ) := by
  by_cases hN : 5 ≤ N
  · exact Lshape_big N hN
  · push_neg at hN
    interval_cases N <;>
      norm_num [F_def, C, Cc, sign_real, Finset.sum_range_succ, Nat.factorial]

/-! ## Square partial sums -/

lemma square_sum (N : ℕ) :
    ∑ a ∈ range N, ∑ b ∈ range N, F a b
      = ∑ M ∈ range N, C M / (Nat.factorial (M + 2) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hsplit :
          ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), F a b
            = (∑ a ∈ range N, ∑ b ∈ range N, F a b)
              + ((∑ b ∈ range N, F N b) + (∑ a ∈ range N, F a N) + F N N) := by
        rw [Finset.sum_range_succ]
        have hinner : ∀ a ∈ range N,
            ∑ b ∈ range (N + 1), F a b = (∑ b ∈ range N, F a b) + F a N := by
          intro a _; exact Finset.sum_range_succ _ _
        rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib,
          Finset.sum_range_succ (fun b => F N b)]
        ring
      rw [hsplit, ih, Lshape N, Finset.sum_range_succ]

/-! ## Summability -/

lemma four_pow_le_factorial : ∀ M : ℕ, 4 ^ M ≤ Nat.factorial (M + 2)
  | 0 => by norm_num [Nat.factorial]
  | 1 => by norm_num [Nat.factorial]
  | (M + 2) => by
      have ih := four_pow_le_factorial (M + 1)
      calc 4 ^ (M + 2) = 4 * 4 ^ (M + 1) := by ring
        _ ≤ (M + 4) * Nat.factorial (M + 3) := Nat.mul_le_mul (by omega) ih
        _ = Nat.factorial (M + 4) := (Nat.factorial_succ (M + 3)).symm

lemma num_bound (a b : ℕ) :
    |((Int.sign (2 * (a : ℤ) - (b : ℤ) - 4) : ℤ) : ℝ) + (-1 : ℝ) ^ (min a b)| ≤ 2 := by
  have hs : ((Int.sign (2 * (a : ℤ) - (b : ℤ) - 4) : ℤ) : ℝ) = -1
      ∨ ((Int.sign (2 * (a : ℤ) - (b : ℤ) - 4) : ℤ) : ℝ) = 0
      ∨ ((Int.sign (2 * (a : ℤ) - (b : ℤ) - 4) : ℤ) : ℝ) = 1 := by
    rcases lt_trichotomy (2 * (a : ℤ) - (b : ℤ) - 4) 0 with h | h | h
    · exact Or.inl (sgn_neg' h)
    · exact Or.inr (Or.inl (sgn_zero' h))
    · exact Or.inr (Or.inr (sgn_pos' h))
  have hp : (-1 : ℝ) ^ (min a b) = 1 ∨ (-1 : ℝ) ^ (min a b) = -1 := by
    rcases Nat.even_or_odd (min a b) with he | ho
    · exact Or.inl he.neg_one_pow
    · exact Or.inr ho.neg_one_pow
  rcases hs with h | h | h <;> rcases hp with h' | h' <;> rw [h, h'] <;> norm_num

lemma two_pow_le_fact (a b : ℕ) :
    (2 : ℝ) ^ (a + b) ≤ (Nat.factorial (max a b + 2) : ℝ) := by
  have hnat : 2 ^ (a + b) ≤ Nat.factorial (max a b + 2) := by
    have hab : a + b ≤ 2 * max a b := by
      rcases le_total a b with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    calc 2 ^ (a + b) ≤ 2 ^ (2 * max a b) := Nat.pow_le_pow_right (by norm_num) hab
      _ = 4 ^ (max a b) := by rw [pow_mul]; norm_num
      _ ≤ Nat.factorial (max a b + 2) := four_pow_le_factorial _
  exact_mod_cast hnat

lemma half_mul_two (k : ℕ) : ((1 : ℝ) / 2) ^ k * (2 : ℝ) ^ k = 1 := by
  rw [← mul_pow]
  norm_num

lemma norm_F_le (a b : ℕ) :
    ‖F a b‖ ≤ 2 * ((1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ b) := by
  have hpos : (0 : ℝ) < (Nat.factorial (max a b + 2) : ℝ) := fact_pos' _
  have hcnn : (0 : ℝ) ≤ 2 * ((1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ b) := by positivity
  have hcoef : (2 : ℝ) * ((1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ b) * (2 : ℝ) ^ (a + b) = 2 := by
    rw [pow_add]
    calc (2 : ℝ) * ((1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ b) * ((2 : ℝ) ^ a * (2 : ℝ) ^ b)
        = 2 * (((1 / 2 : ℝ) ^ a * (2 : ℝ) ^ a) * ((1 / 2 : ℝ) ^ b * (2 : ℝ) ^ b)) := by ring
      _ = 2 := by rw [half_mul_two a, half_mul_two b]; ring
  rw [Real.norm_eq_abs, F_def, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |((Int.sign (2 * (a : ℤ) - (b : ℤ) - 4) : ℤ) : ℝ) + (-1 : ℝ) ^ (min a b)|
      ≤ 2 := num_bound a b
    _ = 2 * ((1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ b) * (2 : ℝ) ^ (a + b) := hcoef.symm
    _ ≤ 2 * ((1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ b) * (Nat.factorial (max a b + 2) : ℝ) :=
        mul_le_mul_of_nonneg_left (two_pow_le_fact a b) hcnn

lemma summable_half : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

lemma summable_F : Summable (fun p : ℕ × ℕ => F p.1 p.2) := by
  have hprod : Summable (fun p : ℕ × ℕ => (1 / 2 : ℝ) ^ p.1 * (1 / 2 : ℝ) ^ p.2) :=
    summable_half.mul_of_nonneg summable_half (fun n => by positivity) (fun n => by positivity)
  refine Summable.of_norm_bounded (hprod.mul_left 2) ?_
  rintro ⟨a, b⟩
  exact norm_F_le a b

lemma summable_fiber (a : ℕ) : Summable (fun b : ℕ => F a b) := by
  refine Summable.of_norm_bounded (summable_half.mul_left (2 * (1 / 2 : ℝ) ^ a)) ?_
  intro b
  have h := norm_F_le a b
  rwa [← mul_assoc] at h

lemma tendsto_square :
    Tendsto (fun N : ℕ => ∑ p ∈ range N ×ˢ range N, F p.1 p.2) atTop
      (𝓝 (∑' p : ℕ × ℕ, F p.1 p.2)) := by
  have hmono : Monotone (fun N : ℕ => range N ×ˢ range N) := by
    intro m n hmn p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  have hcof : ∀ p : ℕ × ℕ, ∃ N, p ∈ range N ×ˢ range N := by
    intro p
    refine ⟨max p.1 p.2 + 1, ?_⟩
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (le_max_left _ _), Nat.lt_succ_of_le (le_max_right _ _)⟩
  exact summable_F.hasSum.comp (tendsto_atTop_finset_of_monotone hmono hcof)

/-! ## The one-dimensional series, at the level of partial sums -/

lemma hasSum_inv_factorial : HasSum (fun n : ℕ => 1 / (Nat.factorial n : ℝ)) (Real.exp 1) := by
  have h : HasSum (fun n : ℕ => (1 : ℝ) ^ n / (Nat.factorial n : ℝ))
      (NormedSpace.exp (1 : ℝ)) := NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
  rw [← Real.exp_eq_exp_ℝ] at h
  simpa using h

lemma tendsto_partial_exp :
    Tendsto (fun N : ℕ => ∑ i ∈ range N, 1 / (Nat.factorial i : ℝ)) atTop (𝓝 (Real.exp 1)) :=
  hasSum_inv_factorial.comp tendsto_finset_range

/-- Partial sums of a shifted sequence, purely combinatorially. -/
lemma sum_shift (g : ℕ → ℝ) (k N : ℕ) :
    ∑ i ∈ range N, g (i + k) = (∑ i ∈ range (N + k), g i) - ∑ i ∈ range k, g i := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, show N + 1 + k = (N + k) + 1 from by omega,
        Finset.sum_range_succ]
      ring

lemma tendsto_shift (g : ℕ → ℝ) (a : ℝ) (k : ℕ)
    (h : Tendsto (fun N : ℕ => ∑ i ∈ range N, g i) atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => ∑ i ∈ range N, g (i + k)) atTop
      (𝓝 (a - ∑ i ∈ range k, g i)) := by
  have h1 : Tendsto (fun N : ℕ => ∑ i ∈ range (N + k), g i) atTop (𝓝 a) :=
    h.comp (tendsto_add_atTop_nat k)
  have hc : Tendsto (fun _ : ℕ => ∑ i ∈ range k, g i) atTop (𝓝 (∑ i ∈ range k, g i)) :=
    tendsto_const_nhds
  refine (h1.sub hc).congr ?_
  intro N
  exact (sum_shift g k N).symm

lemma tendsto_A :
    Tendsto (fun N : ℕ => ∑ M ∈ range N, 1 / (Nat.factorial (M + 1) : ℝ)) atTop
      (𝓝 (Real.exp 1 - 1)) := by
  have h := tendsto_shift (fun n : ℕ => 1 / (Nat.factorial n : ℝ)) (Real.exp 1) 1
    tendsto_partial_exp
  have hval : ∑ i ∈ range 1, 1 / (Nat.factorial i : ℝ) = 1 := by
    norm_num [Nat.factorial]
  rwa [hval] at h

lemma tendsto_B :
    Tendsto (fun N : ℕ => ∑ M ∈ range N, 1 / (Nat.factorial (M + 2) : ℝ)) atTop
      (𝓝 (Real.exp 1 - 2)) := by
  have h := tendsto_shift (fun n : ℕ => 1 / (Nat.factorial n : ℝ)) (Real.exp 1) 2
    tendsto_partial_exp
  have hval : ∑ i ∈ range 2, 1 / (Nat.factorial i : ℝ) = 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rwa [hval] at h

lemma sum_Cc (N : ℕ) (hN : 4 ≤ N) :
    ∑ M ∈ range N, Cc M / (Nat.factorial (M + 2) : ℝ) = 169 / 120 := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [Finset.sum_range_succ, Cc, Nat.factorial]
  | succ N hN ih =>
      have hz : Cc N = 0 := by
        simp only [Cc]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [Finset.sum_range_succ, ih, hz]
      norm_num

lemma tendsto_corr :
    Tendsto (fun N : ℕ => ∑ M ∈ range N, Cc M / (Nat.factorial (M + 2) : ℝ)) atTop
      (𝓝 (169 / 120)) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop 4] with N hN
  exact (sum_Cc N hN).symm

lemma term_split (M : ℕ) :
    ((M : ℝ) - 3) / (Nat.factorial (M + 2) : ℝ)
      = 1 / (Nat.factorial (M + 1) : ℝ) - 5 * (1 / (Nat.factorial (M + 2) : ℝ)) := by
  have hfs : (Nat.factorial (M + 2) : ℝ) = ((M : ℝ) + 2) * (Nat.factorial (M + 1) : ℝ) := by
    rw [show M + 2 = (M + 1) + 1 from rfl, Nat.factorial_succ]
    push_cast
    ring
  have h1 : (Nat.factorial (M + 1) : ℝ) ≠ 0 := fact_ne_zero _
  have h2 : ((M : ℝ) + 2) ≠ 0 := by positivity
  rw [hfs]
  field_simp
  ring

lemma sum_C_decomp (N : ℕ) :
    ∑ M ∈ range N, C M / (Nat.factorial (M + 2) : ℝ)
      = (∑ M ∈ range N, 1 / (Nat.factorial (M + 1) : ℝ))
        - 5 * (∑ M ∈ range N, 1 / (Nat.factorial (M + 2) : ℝ))
        + (∑ M ∈ range N, Cc M / (Nat.factorial (M + 2) : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      have hts := term_split N
      simp only [C, add_div]
      rw [hts]
      ring

lemma tendsto_C :
    Tendsto (fun N : ℕ => ∑ M ∈ range N, C M / (Nat.factorial (M + 2) : ℝ)) atTop
      (𝓝 (1249 / 120 - 4 * Real.exp 1)) := by
  have h := (tendsto_A.sub (tendsto_B.const_mul 5)).add tendsto_corr
  have hval : (Real.exp 1 - 1) - 5 * (Real.exp 1 - 2) + 169 / 120
      = 1249 / 120 - 4 * Real.exp 1 := by ring
  rw [hval] at h
  refine h.congr ?_
  intro N
  exact (sum_C_decomp N).symm

/-! ## The double sum over `ℕ × ℕ` -/

lemma tsum_F : (∑' p : ℕ × ℕ, F p.1 p.2) = 1249 / 120 - 4 * Real.exp 1 := by
  refine tendsto_nhds_unique tendsto_square ?_
  have heq : ∀ N : ℕ,
      ∑ p ∈ range N ×ˢ range N, F p.1 p.2
        = ∑ M ∈ range N, C M / (Nat.factorial (M + 2) : ℝ) := by
    intro N
    rw [Finset.sum_product']
    exact square_sum N
  simp only [heq]
  exact tendsto_C

lemma tsum_F_iterated : (∑' (a : ℕ) (b : ℕ), F a b) = 1249 / 120 - 4 * Real.exp 1 := by
  rw [← tsum_F]
  exact (summable_F.tsum_prod' (fun a => summable_fiber a)).symm

/-! ## Back to `ℕ+` -/

lemma pnat_tsum (g : ℕ → ℝ) : (∑' (m : ℕ+), g m.natPred) = ∑' (a : ℕ), g a :=
  Equiv.pnatEquivNat.tsum_eq g

lemma term_eq (m n : ℕ+) :
    (((Int.sign (2 * (m : ℤ) - (n : ℤ) - 5) : ℤ) : ℝ)
        + (-1 : ℝ) ^ ((min (m : ℕ) (n : ℕ)) + 3)) /
      (Nat.factorial ((max (m : ℕ) (n : ℕ)) + 1) : ℝ)
      = F m.natPred n.natPred := by
  set a := m.natPred with hadef
  set b := n.natPred with hbdef
  have ha : (m : ℕ) = a + 1 := (PNat.natPred_add_one m).symm
  have hb : (n : ℕ) = b + 1 := (PNat.natPred_add_one n).symm
  have h1 : ((m : ℕ) : ℤ) = (a : ℤ) + 1 := by rw [ha]; push_cast; ring
  have h2 : ((n : ℕ) : ℤ) = (b : ℤ) + 1 := by rw [hb]; push_cast; ring
  have hsign : 2 * ((m : ℕ) : ℤ) - ((n : ℕ) : ℤ) - 5 = 2 * (a : ℤ) - (b : ℤ) - 4 := by
    rw [h1, h2]; ring
  have hmin : min (m : ℕ) (n : ℕ) + 3 = min a b + 4 := by omega
  have hmax : max (m : ℕ) (n : ℕ) + 1 = max a b + 2 := by omega
  have hpow : (-1 : ℝ) ^ (min a b + 4) = (-1 : ℝ) ^ (min a b) := by
    rw [pow_add]; norm_num
  rw [F_def, hsign, hmin, hmax, hpow]

end DoubleSumSgnFactorial

open DoubleSumSgnFactorial in
theorem double_infinite_sum_sgn_factorial_eq :
    (∑' (m : ℕ+) (n : ℕ+),
      ((Int.sign (2 * (m : ℤ) - (n : ℤ) - 5) : ℝ) + (-1 : ℝ) ^ ((min (m : ℕ) (n : ℕ)) + 3)) /
      (Nat.factorial ((max (m : ℕ) (n : ℕ)) + 1) : ℝ)) =
      (1249 : ℝ) / 120 - 4 * Real.exp 1 := by
  have hinner : ∀ m : ℕ+,
      (∑' (n : ℕ+),
        (((Int.sign (2 * (m : ℤ) - (n : ℤ) - 5) : ℤ) : ℝ)
            + (-1 : ℝ) ^ ((min (m : ℕ) (n : ℕ)) + 3)) /
        (Nat.factorial ((max (m : ℕ) (n : ℕ)) + 1) : ℝ))
        = ∑' b : ℕ, F m.natPred b := by
    intro m
    rw [tsum_congr (fun n => term_eq m n)]
    exact pnat_tsum (fun b => F m.natPred b)
  rw [tsum_congr hinner, pnat_tsum (fun a => ∑' b : ℕ, F a b)]
  exact tsum_F_iterated
```
