# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `29 August 2026`\
Line count: `249`\
Turn count: `3`

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
  have hpow : ∀ (n : ℕ) (a b : ℝ), 0 ≤ a → a < b → a ^ (n + 1) < b ^ (n + 1) := by
    intro n
    induction n with
    | zero => intro a b ha hab; simpa using hab
    | succ k ih =>
      intro a b ha hab
      have hb : 0 < b := lt_of_le_of_lt ha hab
      have h1 : a ^ (k + 1) < b ^ (k + 1) := ih a b ha hab
      have e1 : a ^ (k + 1 + 1) = a * a ^ (k + 1) := by ring
      have e2 : b ^ (k + 1 + 1) = b * b ^ (k + 1) := by ring
      rw [e1, e2]
      calc a * a ^ (k + 1) ≤ a * b ^ (k + 1) := mul_le_mul_of_nonneg_left h1.le ha
        _ < b * b ^ (k + 1) := mul_lt_mul_of_pos_right hab (pow_pos hb (k + 1))
  have hpow12 : ∀ a b : ℝ, 0 ≤ a → a < b → a ^ 12 < b ^ 12 := by
    intro a b ha hab
    simpa using hpow 11 a b ha hab
  have habs12 : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ^ 12 = b ^ 12 → a = b := by
    intro a b ha hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (ne_of_lt (hpow12 a b ha h))
    · exact h
    · exact absurd hab.symm (ne_of_lt (hpow12 b a hb h))
  have hmem : ∀ (x₀ : ℝ) (p : ℝ × ℝ), p ∈ C ∩ verticalLine x₀ ↔
      (0 < p.1 ∧ p.1 * p.2 ^ 13 - 4 * p.2 = p.1 ^ (5 * p.1) - 3 * p.1 - 1 ∧ p.1 = x₀) := by
    intro x₀ p
    simp only [Set.mem_inter_iff, C, verticalLine, Set.mem_setOf_eq, gt_iff_lt]
    tauto
  constructor
  · intro x₀
    rcases le_or_gt x₀ 0 with hx | hx
    · have hempty : C ∩ verticalLine x₀ = ∅ := by
        ext p
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hp
        rw [hmem] at hp
        obtain ⟨h1, -, h3⟩ := hp
        rw [h3] at h1
        exact absurd h1 (not_lt.mpr hx)
      rw [hempty, Set.encard_empty]
      simp
    · have hx' : x₀ ≠ 0 := ne_of_gt hx
      obtain ⟨t, ht0, ht12⟩ : ∃ t : ℝ, 0 < t ∧ 13 * x₀ * t ^ 12 = 4 := by
        have hpos : (0:ℝ) < 4 / (13 * x₀) := div_pos (by norm_num) (by linarith)
        refine ⟨(4 / (13 * x₀)) ^ ((12:ℝ)⁻¹), Real.rpow_pos_of_pos hpos _, ?_⟩
        have h1 : ((4 / (13 * x₀)) ^ ((12:ℝ)⁻¹)) ^ (12:ℕ) = 4 / (13 * x₀) := by
          rw [← Real.rpow_natCast ((4 / (13 * x₀)) ^ ((12:ℝ)⁻¹)) 12, ← Real.rpow_mul hpos.le]
          norm_num
        rw [h1]
        field_simp
      have hcont : Continuous (fun y : ℝ => x₀ * y ^ 13 - 4 * y) := by
        first | fun_prop | continuity
      have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => x₀ * y ^ 13 - 4 * y)
          (13 * x₀ * y ^ 12 - 4) y := by
        intro y
        have h1 : HasDerivAt (fun y : ℝ => y ^ 13) ((13:ℝ) * y ^ 12) y := by
          simpa using hasDerivAt_pow 13 y
        have h2 : HasDerivAt (fun y : ℝ => y) (1:ℝ) y := by
          first | exact hasDerivAt_id y | simpa using hasDerivAt_id y
        have h3 : HasDerivAt (fun y : ℝ => x₀ * y ^ 13 - 4 * y)
            (x₀ * ((13:ℝ) * y ^ 12) - 4 * 1) y := (h1.const_mul x₀).sub (h2.const_mul (4:ℝ))
        have h4 : x₀ * ((13:ℝ) * y ^ 12) - 4 * 1 = 13 * x₀ * y ^ 12 - 4 := by ring
        rwa [h4] at h3
      have hderiv : ∀ y : ℝ, deriv (fun y : ℝ => x₀ * y ^ 13 - 4 * y) y
          = 13 * x₀ * y ^ 12 - 4 := fun y => (hd y).deriv
      have habsp : ∀ y : ℝ, (|y|) ^ 12 = y ^ 12 := by
        intro y
        rw [pow_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ y ^ 12)]
      have hposR : ∀ y : ℝ, t < y → 0 < 13 * x₀ * y ^ 12 - 4 := by
        intro y hy
        have h1 : t ^ 12 < y ^ 12 := hpow12 t y ht0.le hy
        nlinarith [mul_pos hx (sub_pos.mpr h1)]
      have hposL : ∀ y : ℝ, y < -t → 0 < 13 * x₀ * y ^ 12 - 4 := by
        intro y hy
        have hyneg : y < 0 := by linarith
        have hab : t < |y| := by rw [abs_of_neg hyneg]; linarith
        have h3 : t ^ 12 < (|y|) ^ 12 := hpow12 t (|y|) ht0.le hab
        rw [habsp] at h3
        nlinarith [mul_pos hx (sub_pos.mpr h3)]
      have hnegM : ∀ y : ℝ, -t < y → y < t → 13 * x₀ * y ^ 12 - 4 < 0 := by
        intro y h1 h2
        have hab : |y| < t := abs_lt.mpr ⟨h1, h2⟩
        have h3 : (|y|) ^ 12 < t ^ 12 := hpow12 (|y|) t (abs_nonneg y) hab
        rw [habsp] at h3
        nlinarith [mul_pos hx (sub_pos.mpr h3)]
      have hm1 : StrictMonoOn (fun y : ℝ => x₀ * y ^ 13 - 4 * y) (Set.Iic (-t)) := by
        apply strictMonoOn_of_deriv_pos (convex_Iic (-t)) hcont.continuousOn
        intro y hy
        rw [interior_Iic] at hy
        rw [hderiv y]
        exact hposL y hy
      have hm2 : StrictAntiOn (fun y : ℝ => x₀ * y ^ 13 - 4 * y) (Set.Icc (-t) t) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc (-t) t) hcont.continuousOn
        intro y hy
        rw [interior_Icc] at hy
        rw [hderiv y]
        exact hnegM y hy.1 hy.2
      have hm3 : StrictMonoOn (fun y : ℝ => x₀ * y ^ 13 - 4 * y) (Set.Ici t) := by
        apply strictMonoOn_of_deriv_pos (convex_Ici t) hcont.continuousOn
        intro y hy
        rw [interior_Ici] at hy
        rw [hderiv y]
        exact hposR y hy
      have key1 : ∀ D : Set ℝ, Set.InjOn (fun y : ℝ => x₀ * y ^ 13 - 4 * y) D →
          Set.encard ((C ∩ verticalLine x₀) ∩ {p : ℝ × ℝ | p.2 ∈ D}) ≤ 1 := by
        intro D hD
        rcases Set.eq_empty_or_nonempty ((C ∩ verticalLine x₀) ∩ {p : ℝ × ℝ | p.2 ∈ D}) with
          h | ⟨p₀, hp₀⟩
        · rw [h, Set.encard_empty]; simp
        · have hsub : ((C ∩ verticalLine x₀) ∩ {p : ℝ × ℝ | p.2 ∈ D}) ⊆ {p₀} := by
            intro q hq
            have h1 := (hmem x₀ p₀).mp hp₀.1
            have h2 := (hmem x₀ q).mp hq.1
            have e1 : x₀ * p₀.2 ^ 13 - 4 * p₀.2 = x₀ ^ (5 * x₀) - 3 * x₀ - 1 := by
              have h := h1.2.1
              rw [h1.2.2] at h
              exact h
            have e2 : x₀ * q.2 ^ 13 - 4 * q.2 = x₀ ^ (5 * x₀) - 3 * x₀ - 1 := by
              have h := h2.2.1
              rw [h2.2.2] at h
              exact h
            have hy : q.2 = p₀.2 := hD hq.2 hp₀.2 (e2.trans e1.symm)
            have hxx : q.1 = p₀.1 := by rw [h2.2.2, h1.2.2]
            have hfin : q = p₀ := by
              first
                | exact Prod.ext hxx hy
                | exact Prod.ext_iff.mpr ⟨hxx, hy⟩
            exact hfin
          calc Set.encard ((C ∩ verticalLine x₀) ∩ {p : ℝ × ℝ | p.2 ∈ D})
              ≤ Set.encard ({p₀} : Set (ℝ × ℝ)) := by
                first
                  | exact Set.encard_le_card hsub
                  | exact Set.encard_le_of_subset hsub
                  | exact Set.encard_mono hsub
                  | exact Set.encard_le_encard hsub
            _ = 1 := Set.encard_singleton p₀
      have hUnion : C ∩ verticalLine x₀ =
          (((C ∩ verticalLine x₀) ∩ {p : ℝ × ℝ | p.2 ∈ Set.Iic (-t)}) ∪
            ((C ∩ verticalLine x₀) ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-t) t})) ∪
          ((C ∩ verticalLine x₀) ∩ {p : ℝ × ℝ | p.2 ∈ Set.Ici t}) := by
        ext p
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iic, Set.mem_Icc,
          Set.mem_Ici]
        constructor
        · intro hp
          rcases le_or_gt p.2 (-t) with h | h
          · exact Or.inl (Or.inl ⟨hp, h⟩)
          · rcases le_or_gt p.2 t with h2 | h2
            · exact Or.inl (Or.inr ⟨hp, h.le, h2⟩)
            · exact Or.inr ⟨hp, h2.le⟩
        · rintro ((⟨hp, -⟩ | ⟨hp, -⟩) | ⟨hp, -⟩) <;> exact hp
      have final : ∀ A B D : Set (ℝ × ℝ), A.encard ≤ 1 → B.encard ≤ 1 → D.encard ≤ 1 →
          ((A ∪ B) ∪ D).encard ≤ 3 := by
        intro A B D hA hB hD
        have h1 : (A ∪ B).encard ≤ 1 + 1 := le_trans (Set.encard_union_le _ _) (add_le_add hA hB)
        have h2 : ((A ∪ B) ∪ D).encard ≤ 1 + 1 + 1 :=
          le_trans (Set.encard_union_le _ _) (add_le_add h1 hD)
        refine le_trans h2 ?_
        first | norm_num | rfl | decide | simp
      rw [hUnion]
      exact final _ _ _ (key1 _ hm1.injOn) (key1 _ hm2.injOn) (key1 _ hm3.injOn)
  · have hcontOn : ContinuousOn (fun x : ℝ => x ^ (5 * x) - 3 * x - 1) (Set.Icc 1 2) := by
      intro x hx
      have hx0 : x ≠ 0 := by
        have h1 : (1:ℝ) ≤ x := hx.1
        intro h
        rw [h] at h1
        linarith
      have hid : ContinuousAt (fun x : ℝ => x) x := continuousAt_id
      have h5 : ContinuousAt (fun x : ℝ => 5 * x) x := continuousAt_const.mul continuousAt_id
      have hr : ContinuousAt (fun x : ℝ => x ^ (5 * x)) x := ContinuousAt.rpow hid h5 (Or.inl hx0)
      have h3 : ContinuousAt (fun x : ℝ => 3 * x) x := continuousAt_const.mul continuousAt_id
      exact ((hr.sub h3).sub continuousAt_const).continuousWithinAt
    obtain ⟨x₀, hx₀I, hx₀⟩ : ∃ x ∈ Set.Icc (1:ℝ) 2, x ^ (5 * x) - 3 * x - 1 = 0 := by
      have hsub := intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2) hcontOn
      have h0 : (0:ℝ) ∈ Set.Icc ((1:ℝ) ^ (5 * (1:ℝ)) - 3 * 1 - 1)
          ((2:ℝ) ^ (5 * (2:ℝ)) - 3 * 2 - 1) := by
        rw [Set.mem_Icc]
        constructor
        · rw [Real.one_rpow]; norm_num
        · rw [show (5:ℝ) * 2 = ((10:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
      obtain ⟨x, hx, hfx⟩ := hsub h0
      exact ⟨x, hx, hfx⟩
    have hx0pos : 0 < x₀ := by
      have h1 := hx₀I.1
      linarith
    have hx0' : x₀ ≠ 0 := ne_of_gt hx0pos
    obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 < s ∧ x₀ * s ^ 12 = 4 := by
      have hpos : (0:ℝ) < 4 / x₀ := div_pos (by norm_num) hx0pos
      refine ⟨(4 / x₀) ^ ((12:ℝ)⁻¹), Real.rpow_pos_of_pos hpos _, ?_⟩
      have h1 : ((4 / x₀) ^ ((12:ℝ)⁻¹)) ^ (12:ℕ) = 4 / x₀ := by
        rw [← Real.rpow_natCast ((4 / x₀) ^ ((12:ℝ)⁻¹)) 12, ← Real.rpow_mul hpos.le]
        norm_num
      rw [h1]
      field_simp
    refine ⟨x₀, ?_⟩
    rw [Set.encard_eq_three]
    refine ⟨(x₀, 0), (x₀, s), (x₀, -s), ?_, ?_, ?_, ?_⟩
    · intro h
      rw [Prod.mk.injEq] at h
      have h2 := h.2
      linarith
    · intro h
      rw [Prod.mk.injEq] at h
      have h2 := h.2
      linarith
    · intro h
      rw [Prod.mk.injEq] at h
      have h2 := h.2
      linarith
    · ext ⟨a, b⟩
      simp only [hmem, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rw [h3] at h2
        rw [hx₀] at h2
        have hfac : b * (x₀ * b ^ 12 - 4) = 0 := by linear_combination h2
        rcases mul_eq_zero.mp hfac with h | h
        · exact Or.inl ⟨h3, h⟩
        · have hb12 : b ^ 12 = s ^ 12 := by
            have h4 : x₀ * b ^ 12 = x₀ * s ^ 12 := by rw [hs]; linarith
            exact mul_left_cancel₀ hx0' h4
          have habs : |b| = s := by
            apply habs12 (|b|) s (abs_nonneg b) hs0.le
            rw [pow_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ b ^ 12)]
            exact hb12
          rcases (abs_eq hs0.le).mp habs with h5 | h5
          · exact Or.inr (Or.inl ⟨h3, h5⟩)
          · exact Or.inr (Or.inr ⟨h3, h5⟩)
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · refine ⟨by rw [h1]; exact hx0pos, ?_, h1⟩
          rw [h1, h2, hx₀]
          ring
        · refine ⟨by rw [h1]; exact hx0pos, ?_, h1⟩
          rw [h1, h2, hx₀]
          linear_combination s * hs
        · refine ⟨by rw [h1]; exact hx0pos, ?_, h1⟩
          rw [h1, h2, hx₀]
          linear_combination (-s) * hs
```
