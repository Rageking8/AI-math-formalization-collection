# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `8 August 2026`\
Line count: `463`\
Turn count: `6`

## Solution

```lean4
import Mathlib

open Real MeasureTheory Filter Topology Set

set_option maxHeartbeats 4000000

noncomputable section

namespace DigitIntegral

/-!
# `∫_{x ≥ 1} S(⌊x²⌋)/x⁵ dx = 5π²/132`

* `S n + 9 * Σ_{k ≥ 1} ⌊n/10ᵏ⌋ = n`               (induction on the digit expansion)
* `⌊y⌋ = Σ_{m ≥ 1} 𝟙[m ≤ y]`, hence for `c ≥ 1`
  `∫_{Ioi 1} ⌊x²/c⌋ x⁻⁵ = Σ_{m ≥ 1} 1/(4(cm)²) = π²/(24c²)`
* package the integrand as one signed family `F : ℕ → ℝ → ℝ`, so only a single
  `∫ Σ' = Σ' ∫` interchange is needed
* `π²/24 - 9 * (π²/24) * (1/99) = 5π²/132`
-/

/-- The base-10 digit sum, as a real number. -/
def S (n : ℕ) : ℝ := ((Nat.digits 10 n).sum : ℝ)

/-! ## 1. The arithmetic identity -/

lemma sum_digits_add (m : ℕ) : ∀ n : ℕ, n < 10 ^ m →
    (Nat.digits 10 n).sum + 9 * ∑ k ∈ Finset.range m, n / 10 ^ (k + 1) = n := by
  induction m with
  | zero =>
      intro n hn
      simp only [pow_zero, Nat.lt_one_iff] at hn
      subst hn
      simp
  | succ m ih =>
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      have hdiv : n / 10 < 10 ^ m := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        calc n < 10 ^ (m + 1) := hn
          _ = 10 ^ m * 10 := by ring
      have key := ih (n / 10) hdiv
      have hsplit : ∑ k ∈ Finset.range (m + 1), n / 10 ^ (k + 1)
          = (∑ k ∈ Finset.range m, (n / 10) / 10 ^ (k + 1)) + n / 10 := by
        rw [Finset.sum_range_succ']
        simp only [zero_add, pow_one]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Nat.div_div_eq_div_mul]
        congr 1
        ring
      rw [Nat.digits_def' (by norm_num : 1 < 10) hn0, List.sum_cons, hsplit]
      have hmod := Nat.mod_add_div n 10
      omega

lemma div_pow_eq_zero_of_le {n k : ℕ} (h : n ≤ k) : n / 10 ^ (k + 1) = 0 := by
  refine Nat.div_eq_of_lt ?_
  calc n ≤ k := h
    _ < 10 ^ k := Nat.lt_pow_self (by norm_num)
    _ ≤ 10 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)

/-- `Tr n = Σ_{k ≥ 1} ⌊n / 10ᵏ⌋`, as a (finitely supported) sum over all `k`. -/
def Tr (n : ℕ) : ℝ := ∑' k : ℕ, ((n / 10 ^ (k + 1) : ℕ) : ℝ)

lemma Tr_eq (n : ℕ) : Tr n = ∑ k ∈ Finset.range n, ((n / 10 ^ (k + 1) : ℕ) : ℝ) := by
  refine tsum_eq_sum ?_
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  simp [div_pow_eq_zero_of_le hk]

lemma S_add_Tr (n : ℕ) : S n + 9 * Tr n = n := by
  have h0 := sum_digits_add n n (Nat.lt_pow_self (by norm_num))
  have h2 := congrArg (fun t : ℕ => (t : ℝ)) h0
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] at h2
  rw [S, Tr_eq]
  exact h2

/-! ## 2. `ζ(2)` and elementary integrals -/

lemma hasSum_inv_succ_sq : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) := hasSum_zeta_two
  have h2 : HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6) :=
    (hasSum_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2 (by simpa using h)
  simpa using h2

lemma hasSum_scaled {c : ℝ} (hc : 0 < c) :
    HasSum (fun m : ℕ => 1 / (4 * (c * ((m : ℝ) + 1)) ^ 2)) (π ^ 2 / (24 * c ^ 2)) := by
  have h := hasSum_inv_succ_sq.mul_left (1 / (4 * c ^ 2))
  have heq : (fun m : ℕ => 1 / (4 * c ^ 2) * (1 / ((m : ℝ) + 1) ^ 2))
      = fun m : ℕ => 1 / (4 * (c * ((m : ℝ) + 1)) ^ 2) := by
    funext m
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hc' : c ≠ 0 := ne_of_gt hc
    field_simp <;> ring
  rw [heq] at h
  have hval : 1 / (4 * c ^ 2) * (π ^ 2 / 6) = π ^ 2 / (24 * c ^ 2) := by
    have hc' : c ≠ 0 := ne_of_gt hc
    field_simp <;> ring
  rwa [hval] at h

lemma rpow_neg_five {x : ℝ} (hx : 0 < x) : x ^ (-5 : ℝ) = 1 / x ^ 5 := by
  rw [Real.rpow_neg hx.le, ← Real.rpow_natCast x 5]
  norm_num

lemma rpow_neg_three {x : ℝ} (hx : 0 < x) : x ^ (-3 : ℝ) = 1 / x ^ 3 := by
  rw [Real.rpow_neg hx.le, ← Real.rpow_natCast x 3]
  norm_num

lemma integrableOn_inv_pow_five {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => 1 / x ^ 5) (Ioi a) := by
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 : ℝ) < -1) ha).congr_fun ?_
    measurableSet_Ioi
  intro x hx
  exact rpow_neg_five (ha.trans hx)

lemma integral_inv_pow_five {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi a, 1 / x ^ 5 = 1 / (4 * a ^ 4) := by
  have hrw : EqOn (fun x : ℝ => 1 / x ^ 5) (fun x : ℝ => x ^ (-5 : ℝ)) (Ioi a) := by
    intro x hx
    exact (rpow_neg_five (ha.trans hx)).symm
  rw [setIntegral_congr_fun measurableSet_Ioi hrw,
    integral_Ioi_rpow_of_lt (by norm_num : (-5 : ℝ) < -1) ha]
  have h4 : a ^ ((-5 : ℝ) + 1) = 1 / a ^ 4 := by
    rw [show ((-5 : ℝ) + 1) = -4 by norm_num, Real.rpow_neg ha.le, ← Real.rpow_natCast a 4]
    norm_num
  have ha' : a ≠ 0 := ne_of_gt ha
  rw [h4]
  field_simp <;> ring

/-! ## 3. The floor as a sum of indicators -/

lemma floor_eq_tsum (c : ℕ) (hc : 1 ≤ c) {x : ℝ} (hx : 1 ≤ x) :
    (⌊x ^ 2 / (c : ℝ)⌋₊ : ℝ)
      = ∑' m : ℕ, Set.indicator (Ici (Real.sqrt ((c : ℝ) * ((m : ℝ) + 1))))
          (fun _ => (1 : ℝ)) x := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  set N := ⌊x ^ 2 / (c : ℝ)⌋₊ with hN
  have key : ∀ m : ℕ,
      Set.indicator (Ici (Real.sqrt ((c : ℝ) * ((m : ℝ) + 1)))) (fun _ => (1 : ℝ)) x
        = if m < N then 1 else 0 := by
    intro m
    have hA : (0 : ℝ) ≤ (c : ℝ) * ((m : ℝ) + 1) := by positivity
    have h1 : Real.sqrt ((c : ℝ) * ((m : ℝ) + 1)) ≤ x ↔ (c : ℝ) * ((m : ℝ) + 1) ≤ x ^ 2 := by
      constructor
      · intro h
        have h2 := mul_self_le_mul_self (Real.sqrt_nonneg _) h
        rwa [Real.mul_self_sqrt hA, ← pow_two] at h2
      · intro h
        have h2 : Real.sqrt ((c : ℝ) * ((m : ℝ) + 1)) ≤ Real.sqrt (x ^ 2) :=
          Real.sqrt_le_sqrt h
        rwa [Real.sqrt_sq hx0] at h2
    have h3 : (c : ℝ) * ((m : ℝ) + 1) ≤ x ^ 2 ↔ ((m : ℝ) + 1) ≤ x ^ 2 / (c : ℝ) := by
      rw [le_div_iff₀ hc0, mul_comm ((m : ℝ) + 1) (c : ℝ)]
    have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
    have h4 : (((m + 1 : ℕ) : ℝ) ≤ x ^ 2 / (c : ℝ)) ↔ m + 1 ≤ N := by
      rw [hN]
      exact (Nat.le_floor_iff (by positivity)).symm
    have hiff : Real.sqrt ((c : ℝ) * ((m : ℝ) + 1)) ≤ x ↔ m < N := by
      rw [h1, h3, ← hcast, h4]
      omega
    by_cases hm : m < N
    · rw [Set.indicator_of_mem (by simpa only [mem_Ici] using hiff.2 hm), if_pos hm]
    · rw [Set.indicator_of_notMem
        (by simp only [mem_Ici]; exact fun h => hm (hiff.1 h)), if_neg hm]
  simp_rw [key]
  rw [tsum_eq_sum (s := Finset.range N) (by
    intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    simp [Nat.not_lt.mpr hm])]
  rw [show (∑ m ∈ Finset.range N, (if m < N then (1 : ℝ) else 0))
      = ∑ _m ∈ Finset.range N, (1 : ℝ) from
    Finset.sum_congr rfl fun m hm => if_pos (Finset.mem_range.mp hm)]
  simp

/-! ## 4. The master integral `∫_{Ioi 1} ⌊x²/c⌋ x⁻⁵ = π²/(24c²)` -/

lemma integrableOn_indicator_piece (a : ℝ) :
    IntegrableOn (fun x => Set.indicator (Ici a) (fun y : ℝ => 1 / y ^ 5) x) (Ioi (1 : ℝ)) :=
  (integrableOn_inv_pow_five (by norm_num : (0 : ℝ) < 1)).indicator measurableSet_Ici

lemma integral_indicator_piece {a : ℝ} (ha : 1 ≤ a) :
    ∫ x in Ioi (1 : ℝ), Set.indicator (Ici a) (fun y : ℝ => 1 / y ^ 5) x
      = 1 / (4 * a ^ 4) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  rw [MeasureTheory.integral_indicator measurableSet_Ici,
    MeasureTheory.Measure.restrict_restrict measurableSet_Ici]
  have hset : ((Ici a ∩ Ioi (1 : ℝ) : Set ℝ)) =ᵐ[volume] (Ioi a : Set ℝ) := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (measure_singleton a)
      rintro y ⟨⟨hy1, -⟩, hy2⟩
      simp only [mem_Ioi, not_lt] at hy2
      simp [le_antisymm hy2 hy1]
    · have hempty : (Ioi a \ (Ici a ∩ Ioi (1 : ℝ)) : Set ℝ) = ∅ := by
        rw [Set.diff_eq_empty]
        intro y hy
        have hy' : a < y := hy
        exact ⟨le_of_lt hy', lt_of_le_of_lt ha hy'⟩
      rw [hempty]
      exact measure_empty
  rw [setIntegral_congr_set hset, integral_inv_pow_five ha0]

lemma one_le_sqrt_threshold {c : ℕ} (hc : 1 ≤ c) (m : ℕ) :
    1 ≤ Real.sqrt ((c : ℝ) * ((m : ℝ) + 1)) := by
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hA : (1 : ℝ) ≤ (c : ℝ) * ((m : ℝ) + 1) := by nlinarith
  simpa using Real.sqrt_le_sqrt hA

lemma integral_floor_div (c : ℕ) (hc : 1 ≤ c) :
    ∫ x in Ioi (1 : ℝ), (⌊x ^ 2 / (c : ℝ)⌋₊ : ℝ) / x ^ 5 = π ^ 2 / (24 * (c : ℝ) ^ 2) := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  -- (a) pointwise expansion into indicators
  have hpt : EqOn (fun x : ℝ => (⌊x ^ 2 / (c : ℝ)⌋₊ : ℝ) / x ^ 5)
      (fun x : ℝ => ∑' m : ℕ,
        Set.indicator (Ici (Real.sqrt ((c : ℝ) * ((m : ℝ) + 1)))) (fun y : ℝ => 1 / y ^ 5) x)
      (Ioi (1 : ℝ)) := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have h := floor_eq_tsum c hc hx1
    have hind : ∀ m : ℕ,
        Set.indicator (Ici (Real.sqrt ((c : ℝ) * ((m : ℝ) + 1)))) (fun y : ℝ => 1 / y ^ 5) x
          = Set.indicator (Ici (Real.sqrt ((c : ℝ) * ((m : ℝ) + 1)))) (fun _ => (1 : ℝ)) x
              * (1 / x ^ 5) := by
      intro m
      by_cases hm : x ∈ Ici (Real.sqrt ((c : ℝ) * ((m : ℝ) + 1)))
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, one_mul]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul]
    show (⌊x ^ 2 / (c : ℝ)⌋₊ : ℝ) / x ^ 5
        = ∑' m : ℕ,
          Set.indicator (Ici (Real.sqrt ((c : ℝ) * ((m : ℝ) + 1)))) (fun y : ℝ => 1 / y ^ 5) x
    simp_rw [hind]
    rw [tsum_mul_right, ← h]
    ring
  -- (b) the value of each piece
  have hpiece : ∀ m : ℕ,
      (∫ x in Ioi (1 : ℝ),
        Set.indicator (Ici (Real.sqrt ((c : ℝ) * ((m : ℝ) + 1)))) (fun y : ℝ => 1 / y ^ 5) x)
        = 1 / (4 * ((c : ℝ) * ((m : ℝ) + 1)) ^ 2) := by
    intro m
    have hA : (0 : ℝ) ≤ (c : ℝ) * ((m : ℝ) + 1) := by positivity
    rw [integral_indicator_piece (one_le_sqrt_threshold hc m)]
    congr 2
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hA]
  -- (c) norms coincide with the integrands (everything is nonnegative)
  have hnorm : ∀ m : ℕ,
      (∫ x in Ioi (1 : ℝ),
        ‖Set.indicator (Ici (Real.sqrt ((c : ℝ) * ((m : ℝ) + 1)))) (fun y : ℝ => 1 / y ^ 5) x‖)
        = 1 / (4 * ((c : ℝ) * ((m : ℝ) + 1)) ^ 2) := by
    intro m
    rw [← hpiece m]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hnn : 0 ≤ Set.indicator (Ici (Real.sqrt ((c : ℝ) * ((m : ℝ) + 1))))
        (fun y : ℝ => 1 / y ^ 5) x := by
      refine Set.indicator_nonneg ?_ x
      intro y hy
      have hy0 : (0 : ℝ) < y := lt_of_lt_of_le
        (lt_of_lt_of_le zero_lt_one (one_le_sqrt_threshold hc m)) hy
      positivity
    exact Real.norm_of_nonneg hnn
  have hsummable : Summable fun m : ℕ =>
      ∫ x in Ioi (1 : ℝ),
        ‖Set.indicator (Ici (Real.sqrt ((c : ℝ) * ((m : ℝ) + 1))))
          (fun y : ℝ => 1 / y ^ 5) x‖ := by
    have h := (hasSum_scaled hc0).summable
    simpa only [hnorm] using h
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    ← MeasureTheory.integral_tsum_of_summable_integral_norm
      (fun m : ℕ => integrableOn_indicator_piece (Real.sqrt ((c : ℝ) * ((m : ℝ) + 1))))
      hsummable]
  simp only [hpiece]
  exact (hasSum_scaled hc0).tsum_eq

/-! ## 5. Integrability of the individual terms -/

lemma measurable_floor_div (c : ℕ) :
    Measurable fun x : ℝ => (⌊x ^ 2 / (c : ℝ)⌋₊ : ℝ) := by
  have h1 : Measurable fun x : ℝ => ⌊x ^ 2 / (c : ℝ)⌋₊ :=
    Nat.measurable_floor.comp (by fun_prop)
  exact (measurable_of_countable _).comp h1

lemma integrableOn_floor_div (c : ℕ) (hc : 1 ≤ c) :
    IntegrableOn (fun x : ℝ => (⌊x ^ 2 / (c : ℝ)⌋₊ : ℝ) / x ^ 5) (Ioi (1 : ℝ)) := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hg : IntegrableOn (fun x : ℝ => x ^ (-3 : ℝ)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  refine Integrable.mono' hg
    (((measurable_floor_div c).div (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : (1 : ℝ) < x := hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hx0' : x ≠ 0 := ne_of_gt hx0
  have hfl : ((⌊x ^ 2 / (c : ℝ)⌋₊ : ℕ) : ℝ) ≤ x ^ 2 := by
    refine le_trans (Nat.floor_le (by positivity)) ?_
    rw [div_le_iff₀ hc0]
    nlinarith [sq_nonneg x]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), rpow_neg_three hx0]
  calc ((⌊x ^ 2 / (c : ℝ)⌋₊ : ℕ) : ℝ) / x ^ 5 ≤ x ^ 2 / x ^ 5 := by gcongr
    _ = 1 / x ^ 3 := by field_simp <;> ring

/-! ## 6. The signed family -/

def F : ℕ → ℝ → ℝ
  | 0 => fun x => (⌊x ^ 2 / ((1 : ℕ) : ℝ)⌋₊ : ℝ) / x ^ 5
  | (k + 1) => fun x => -9 * ((⌊x ^ 2 / ((10 ^ (k + 1) : ℕ) : ℝ)⌋₊ : ℝ) / x ^ 5)

lemma F_zero_eq : F 0 = fun x : ℝ => (⌊x ^ 2 / ((1 : ℕ) : ℝ)⌋₊ : ℝ) / x ^ 5 := rfl

lemma F_succ_eq (k : ℕ) : F (k + 1)
    = fun x : ℝ => (-9 : ℝ) * ((⌊x ^ 2 / ((10 ^ (k + 1) : ℕ) : ℝ)⌋₊ : ℝ) / x ^ 5) := rfl

lemma F_zero_apply (x : ℝ) : F 0 x = (⌊x ^ 2 / ((1 : ℕ) : ℝ)⌋₊ : ℝ) / x ^ 5 := rfl

lemma F_succ_apply (k : ℕ) (x : ℝ) :
    F (k + 1) x = (-9 : ℝ) * ((⌊x ^ 2 / ((10 ^ (k + 1) : ℕ) : ℝ)⌋₊ : ℝ) / x ^ 5) := rfl

lemma F_succ_eq_zero {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : ⌊x ^ 2⌋₊ ≤ k) : F (k + 1) x = 0 := by
  have h : ⌊x ^ 2 / ((10 ^ (k + 1) : ℕ) : ℝ)⌋₊ = 0 := by
    rw [Nat.floor_div_natCast]
    exact div_pow_eq_zero_of_le hk
  show (-9 : ℝ) * ((⌊x ^ 2 / ((10 ^ (k + 1) : ℕ) : ℝ)⌋₊ : ℝ) / x ^ 5) = 0
  rw [h]
  simp

lemma summable_F {x : ℝ} (hx : 0 ≤ x) : Summable fun k : ℕ => F k x := by
  refine summable_of_ne_finset_zero (s := Finset.range (⌊x ^ 2⌋₊ + 1)) ?_
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact F_succ_eq_zero hx (by omega)

lemma tsum_F {x : ℝ} (hx : 1 ≤ x) : ∑' k : ℕ, F k x = S ⌊x ^ 2⌋₊ / x ^ 5 := by
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hx5 : x ^ 5 ≠ 0 := by positivity
  rw [(summable_F hx0).tsum_eq_zero_add]
  have h1 : ∀ k : ℕ, F (k + 1) x
      = (-9 / x ^ 5) * ((⌊x ^ 2⌋₊ / 10 ^ (k + 1) : ℕ) : ℝ) := by
    intro k
    have h : ⌊x ^ 2 / ((10 ^ (k + 1) : ℕ) : ℝ)⌋₊ = ⌊x ^ 2⌋₊ / 10 ^ (k + 1) :=
      Nat.floor_div_natCast _ _
    show (-9 : ℝ) * ((⌊x ^ 2 / ((10 ^ (k + 1) : ℕ) : ℝ)⌋₊ : ℝ) / x ^ 5)
        = (-9 / x ^ 5) * ((⌊x ^ 2⌋₊ / 10 ^ (k + 1) : ℕ) : ℝ)
    rw [h]
    ring
  have h0 : F 0 x = (⌊x ^ 2⌋₊ : ℝ) / x ^ 5 := by
    show ((⌊x ^ 2 / ((1 : ℕ) : ℝ)⌋₊ : ℝ)) / x ^ 5 = (⌊x ^ 2⌋₊ : ℝ) / x ^ 5
    norm_num
  simp_rw [h1]
  rw [tsum_mul_left, ← Tr, h0]
  have hST := S_add_Tr ⌊x ^ 2⌋₊
  field_simp
  linarith [hST]

/-! ## 7. Values and summability of the term integrals -/

lemma integral_F_zero : ∫ x in Ioi (1 : ℝ), F 0 x = π ^ 2 / 24 := by
  have h := integral_floor_div 1 le_rfl
  rw [F_zero_eq]
  simpa using h

lemma integral_F_succ (k : ℕ) :
    ∫ x in Ioi (1 : ℝ), F (k + 1) x = -(9 * (π ^ 2 / 24)) * (1 / 100) ^ (k + 1) := by
  have hc : 1 ≤ (10 ^ (k + 1) : ℕ) := Nat.one_le_pow _ _ (by norm_num)
  rw [F_succ_eq, integral_const_mul, integral_floor_div _ hc]
  have hcast : (((10 ^ (k + 1) : ℕ) : ℝ)) ^ 2 = (100 : ℝ) ^ (k + 1) := by
    push_cast
    rw [← pow_mul, show (100 : ℝ) = 10 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  have hpow : ((1 : ℝ) / 100) ^ (k + 1) = 1 / (100 : ℝ) ^ (k + 1) := by
    rw [div_pow, one_pow]
  have h100 : ((100 : ℝ)) ^ (k + 1) ≠ 0 := by positivity
  rw [hcast, hpow]
  field_simp <;> ring

lemma norm_integral_F_zero : ∫ x in Ioi (1 : ℝ), ‖F 0 x‖ = π ^ 2 / 24 := by
  rw [← integral_F_zero]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hnn : 0 ≤ F 0 x := by
    show (0 : ℝ) ≤ ((⌊x ^ 2 / ((1 : ℕ) : ℝ)⌋₊ : ℝ)) / x ^ 5
    positivity
  exact Real.norm_of_nonneg hnn

lemma norm_integral_F_succ (k : ℕ) :
    ∫ x in Ioi (1 : ℝ), ‖F (k + 1) x‖ = (9 * (π ^ 2 / 24)) * (1 / 100) ^ (k + 1) := by
  have hneg : EqOn (fun x : ℝ => ‖F (k + 1) x‖) (fun x : ℝ => -F (k + 1) x) (Ioi (1 : ℝ)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hcast : (0 : ℝ) ≤ (⌊x ^ 2 / ((10 ^ (k + 1) : ℕ) : ℝ)⌋₊ : ℝ) := Nat.cast_nonneg _
    have h5 : (0 : ℝ) < x ^ 5 := by positivity
    have hq : (0 : ℝ) ≤ (⌊x ^ 2 / ((10 ^ (k + 1) : ℕ) : ℝ)⌋₊ : ℝ) / x ^ 5 :=
      div_nonneg hcast h5.le
    have hle : F (k + 1) x ≤ 0 := by
      show (-9 : ℝ) * ((⌊x ^ 2 / ((10 ^ (k + 1) : ℕ) : ℝ)⌋₊ : ℝ) / x ^ 5) ≤ 0
      linarith
    exact Real.norm_of_nonpos hle
  rw [setIntegral_congr_fun measurableSet_Ioi hneg, integral_neg, integral_F_succ]
  ring

lemma integrableOn_F : ∀ k : ℕ, IntegrableOn (F k) (Ioi (1 : ℝ)) := by
  intro k
  cases k with
  | zero =>
      rw [F_zero_eq]
      exact integrableOn_floor_div 1 le_rfl
  | succ k =>
      have hc : 1 ≤ (10 ^ (k + 1) : ℕ) := Nat.one_le_pow _ _ (by norm_num)
      rw [F_succ_eq]
      exact (integrableOn_floor_div _ hc).const_mul (-9 : ℝ)

lemma geom_r0 : (0 : ℝ) ≤ 1 / 100 := by norm_num
lemma geom_r1 : (1 : ℝ) / 100 < 1 := by norm_num

lemma summable_geom : Summable fun k : ℕ => ((1 : ℝ) / 100) ^ (k + 1) := by
  have h := summable_geometric_of_lt_one geom_r0 geom_r1
  exact (h.mul_left ((1 : ℝ) / 100)).congr fun k => by ring

lemma tsum_geom : ∑' k : ℕ, ((1 : ℝ) / 100) ^ (k + 1) = 1 / 99 := by
  have h := tsum_geometric_of_lt_one geom_r0 geom_r1
  have hshift : ∑' k : ℕ, ((1 : ℝ) / 100) ^ (k + 1)
      = (1 / 100) * ∑' k : ℕ, ((1 : ℝ) / 100) ^ k := by
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring
  rw [hshift, h]
  norm_num

/-! ## 8. The theorem -/

theorem integral_digit_sum_floor_sq :
    ∫ x in Set.Ici (1 : ℝ), ((Nat.digits 10 (Nat.floor (x ^ 2))).sum : ℝ) / x ^ 5 = (5 * π ^ 2) / 132 := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hpt : EqOn (fun x : ℝ => ((Nat.digits 10 ⌊x ^ 2⌋₊).sum : ℝ) / x ^ 5)
      (fun x : ℝ => ∑' k : ℕ, F k x) (Ioi (1 : ℝ)) := by
    intro x hx
    show ((Nat.digits 10 ⌊x ^ 2⌋₊).sum : ℝ) / x ^ 5 = ∑' k : ℕ, F k x
    rw [tsum_F (le_of_lt hx), S]
  have hnormsum : Summable fun k : ℕ => ∫ x in Ioi (1 : ℝ), ‖F k x‖ := by
    have h2 : Summable fun k : ℕ => ∫ x in Ioi (1 : ℝ), ‖F (k + 1) x‖ := by
      simpa only [norm_integral_F_succ] using summable_geom.mul_left (9 * (π ^ 2 / 24))
    exact (summable_nat_add_iff 1).mp h2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    ← MeasureTheory.integral_tsum_of_summable_integral_norm integrableOn_F hnormsum]
  have hsum : Summable fun k : ℕ => ∫ x in Ioi (1 : ℝ), F k x := by
    have h2 : Summable fun k : ℕ => ∫ x in Ioi (1 : ℝ), F (k + 1) x := by
      simpa only [integral_F_succ] using summable_geom.mul_left (-(9 * (π ^ 2 / 24)))
    exact (summable_nat_add_iff 1).mp h2
  rw [hsum.tsum_eq_zero_add, integral_F_zero]
  have htail : (∑' k : ℕ, ∫ x in Ioi (1 : ℝ), F (k + 1) x)
      = -(9 * (π ^ 2 / 24)) * (1 / 99) := by
    simp only [integral_F_succ]
    rw [tsum_mul_left, tsum_geom]
  rw [htail]
  ring

end DigitIntegral
```
