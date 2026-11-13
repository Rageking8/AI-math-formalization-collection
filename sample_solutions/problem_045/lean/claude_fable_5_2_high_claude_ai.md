# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `13 November 2026`\
Line count: `193`\
Turn count: `1`

## Solution

```lean4
import Mathlib

open Real MeasureTheory

theorem integral_digit_sum_floor_sq :
    ∫ x in Set.Ici (1 : ℝ), ((Nat.digits 10 (Nat.floor (x ^ 2))).sum : ℝ) / x ^ 5 = (5 * π ^ 2) / 132 := by
  -- Abstract the integrand `F`, the digit sum `S`, the weights `a n = 1 / (4 n²)`,
  -- and the summand `g n = S n * (a n - a (n + 1))`.
  suffices H : ∀ F : ℝ → ℝ,
      (∀ x, F x = ((Nat.digits 10 (Nat.floor (x ^ 2))).sum : ℝ) / x ^ 5) →
      ∫ x in Set.Ici (1 : ℝ), F x = (5 * π ^ 2) / 132 from H _ fun _ => rfl
  intro F hF
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ, ∀ n, S n = ((Nat.digits 10 n).sum : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ n, a n = 1 / (4 * (n : ℝ) ^ 2) := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ n, g n = S n * (a n - a (n + 1)) := ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ n, u n = Real.sqrt ((n : ℝ) + 1) := ⟨_, fun _ => rfl⟩
  /- ### Facts about the digit sum -/
  have hS0 : S 0 = 0 := by simp [hS]
  have hSrec : ∀ d m : ℕ, d < 10 → S (d + 10 * m) = S m + d := by
    intro d m hd
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [hS]
      · rw [hS, hS, Nat.digits_add 10 (by norm_num) 0 m (by norm_num) (Or.inr hm.ne')]
        simp
    · rw [hS, hS, Nat.digits_add 10 (by norm_num) d m hd (Or.inl hdpos.ne')]
      rw [List.sum_cons]
      push_cast
      ring
  /- ### Integrability -/
  have hmeas : Measurable F := by
    have h1 : Measurable (fun x : ℝ => Nat.floor (x ^ 2)) :=
      Nat.measurable_floor.comp (measurable_id.pow_const 2)
    have h2 : Measurable (fun n : ℕ => ((Nat.digits 10 n).sum : ℝ)) := measurable_from_nat
    have h3 : Measurable (fun x : ℝ => ((Nat.digits 10 (Nat.floor (x ^ 2))).sum : ℝ) / x ^ 5) :=
      (h2.comp h1).div (measurable_id.pow_const 5)
    have : F = fun x : ℝ => ((Nat.digits 10 (Nat.floor (x ^ 2))).sum : ℝ) / x ^ 5 := funext hF
    rw [this]
    exact h3
  have hint : IntegrableOn F (Set.Ici 1) := by
    have hb : IntegrableOn (fun t : ℝ => t ^ (-3 : ℝ)) (Set.Ici 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2)).mono_set
        (Set.Ici_subset_Ioi.mpr (by norm_num))
    refine Integrable.mono' hb hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx1 : (1 : ℝ) ≤ x := hx
    have hx0 : 0 < x := by linarith
    have h1 : ((Nat.digits 10 (Nat.floor (x ^ 2))).sum : ℝ) ≤ x ^ 2 :=
      calc ((Nat.digits 10 (Nat.floor (x ^ 2))).sum : ℝ) ≤ (Nat.floor (x ^ 2) : ℝ) := by
            exact_mod_cast Nat.digit_sum_le 10 _
        _ ≤ x ^ 2 := Nat.floor_le (by positivity)
    have h2 : x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
      rw [Real.rpow_neg hx0.le]
      norm_cast
    rw [hF, Real.norm_of_nonneg (by positivity), h2, div_le_iff₀ (by positivity)]
    have h3 : (x ^ 3)⁻¹ * x ^ 5 = x ^ 2 := by field_simp
    rw [h3]
    exact h1
  /- ### Cutting `[1, ∞)` into the pieces `[√(n+1), √(n+2))` -/
  have hmono : Monotone u := by
    intro m n hmn
    rw [hu, hu]
    apply Real.sqrt_le_sqrt
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hupos : ∀ n, 0 < u n := fun n => by rw [hu]; positivity
  have husq : ∀ n, u n ^ 2 = n + 1 := fun n => by rw [hu]; exact Real.sq_sqrt (by positivity)
  have hfloor : ∀ n x, x ∈ Set.Ico (u n) (u (n + 1)) → Nat.floor (x ^ 2) = n + 1 := by
    rintro n x ⟨h1, h2⟩
    have hx0 : 0 < x := (hupos n).trans_le h1
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · have := pow_le_pow_left₀ (hupos n).le h1 2
      rw [husq] at this
      push_cast
      exact this
    · have := pow_lt_pow_left₀ h2 hx0.le (by norm_num : (2 : ℕ) ≠ 0)
      rw [husq] at this
      push_cast at this ⊢
      linarith
  have hU : (⋃ n, Set.Ico (u n) (u (n + 1))) = Set.Ici 1 := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_Ici]
    constructor
    · rintro ⟨n, h1, -⟩
      have h3 : (1 : ℝ) ≤ u n := by
        nlinarith [husq n, hupos n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
    · intro hx
      have hx2 : (1 : ℝ) ≤ x ^ 2 := by nlinarith
      have hfl : 0 < Nat.floor (x ^ 2) := Nat.floor_pos.mpr hx2
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hfl.ne'
      have hk' := (Nat.floor_eq_iff (by positivity)).mp hk
      push_cast at hk'
      refine ⟨k, ?_, ?_⟩
      · rw [hu, Real.sqrt_le_left (by linarith)]
        exact hk'.1
      · rw [hu, Real.lt_sqrt (by linarith)]
        push_cast
        linarith [hk'.2]
  have hdisj : Pairwise (Function.onFun Disjoint fun n => Set.Ico (u n) (u (n + 1))) :=
    hmono.pairwise_disjoint_on_Ico_succ
  have hpiece : ∀ n, ∫ x in Set.Ico (u n) (u (n + 1)), F x = g (n + 1) := by
    intro n
    have hle : u n ≤ u (n + 1) := hmono (Nat.le_succ n)
    have h0 : (0 : ℝ) ∉ Set.uIcc (u n) (u (n + 1)) := by
      rw [Set.uIcc_of_le hle]
      intro h
      exact absurd h.1 (not_le.mpr (hupos n))
    have hu4 : ∀ k, u k ^ (-5 + 1 : ℤ) = 1 / ((k : ℝ) + 1) ^ 2 := by
      intro k
      rw [show (-5 + 1 : ℤ) = -((4 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast,
        show u k ^ 4 = (u k ^ 2) ^ 2 by ring, husq, one_div]
    have hcongr : Set.EqOn F (fun x => S (n + 1) * x ^ (-5 : ℤ)) (Set.Ico (u n) (u (n + 1))) := by
      intro x hx
      simp only
      rw [hF, hfloor n x hx, ← hS, zpow_neg, div_eq_mul_inv]
      norm_cast
    rw [setIntegral_congr_fun measurableSet_Ico hcongr, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, intervalIntegral.integral_const_mul,
      integral_zpow (Or.inr ⟨by norm_num, h0⟩), hu4, hu4, hg, ha, ha]
    push_cast
    field_simp
    ring
  /- ### The integral as a series -/
  have hsum1 : HasSum (fun n => g (n + 1)) (∫ x in Set.Ici (1 : ℝ), F x) := by
    have h := hasSum_integral_iUnion (μ := volume) (f := F) (s := fun n => Set.Ico (u n) (u (n + 1)))
      (fun n => measurableSet_Ico) hdisj (by rw [hU]; exact hint)
    rw [hU] at h
    convert h using 1
    funext n
    exact (hpiece n).symm
  have hg0 : g 0 = 0 := by rw [hg, hS0, zero_mul]
  have hsumg : HasSum g (∫ x in Set.Ici (1 : ℝ), F x) := by
    have h := (hasSum_nat_add_iff 1).mp hsum1
    simpa [hg0] using h
  /- ### Evaluating the series by splitting into residue classes mod 10 -/
  have hA : HasSum a (π ^ 2 / 24) := by
    have h := hasSum_zeta_two.div_const 4
    convert h using 1
    · funext n
      rw [ha]
      ring
    · ring
  have ha0 : a 0 = 0 := by simp [ha]
  have hstep : ∀ m, a (10 * m) = a m / 100 := by
    intro m
    rw [ha, ha]
    push_cast
    ring
  have hinj : ∀ d : ℕ, Function.Injective (fun m : ℕ => d + 10 * m) := by
    intro d m₁ m₂ h
    simp only at h
    omega
  have hblock : ∀ f : ℕ → ℝ, Summable f →
      HasSum (fun m => ∑ d ∈ Finset.range 10, f (d + 10 * m)) (∑' n, f n) := by
    intro f hf
    have hres : ∑' n, f n = ∑ d ∈ Finset.range 10, ∑' m, f (d + 10 * m) := by
      rw [Nat.sumByResidueClasses hf 10]
      exact Fin.sum_univ_eq_sum_range (fun d => ∑' m, f (d + 10 * m)) 10
    rw [hres]
    exact hasSum_sum fun d _ => (hf.comp_injective (hinj d)).hasSum
  have hG := hblock g hsumg.summable
  have hAb := hblock a hA.summable
  rw [hsumg.tsum_eq] at hG
  rw [hA.tsum_eq] at hAb
  have hpt : ∀ m, ∑ d ∈ Finset.range 10, g (d + 10 * m) =
      g m / 100 + ∑ d ∈ Finset.range 10, a (d + 10 * m) - a m / 100 - 9 * (a (m + 1) / 100) := by
    intro m
    have h10 : a (10 + 10 * m) = a (m + 1) / 100 := by
      rw [← hstep]
      congr 1
      ring
    have e : ∀ d, d < 10 →
        g (d + 10 * m) = (S m + d) * (a (d + 10 * m) - a (d + 1 + 10 * m)) := by
      intro d hd
      rw [hg, hSrec d m hd, add_right_comm]
    rw [Finset.sum_congr rfl fun d hd => e d (Finset.mem_range.mp hd)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
      Nat.cast_one, zero_add, Nat.reduceAdd]
    rw [h10, hstep m, hg m]
    ring
  have hA1 : HasSum (fun m => a (m + 1)) (π ^ 2 / 24) :=
    (hasSum_nat_add_iff 1).mpr (by simpa [ha0] using hA)
  have hR := (((hsumg.div_const 100).add hAb).sub (hA.div_const 100)).sub
    ((hA1.div_const 100).mul_left 9)
  have hG' : HasSum (fun m => g m / 100 + ∑ d ∈ Finset.range 10, a (d + 10 * m) - a m / 100 -
      9 * (a (m + 1) / 100)) (∫ x in Set.Ici (1 : ℝ), F x) := by
    convert hG using 1
    funext m
    exact (hpt m).symm
  have hfinal := hG'.unique hR
  linarith
```
