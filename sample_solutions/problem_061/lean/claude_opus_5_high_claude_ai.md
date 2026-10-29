# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `17 August 2026`\
Line count: `152`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem fractional_part_equation_two_solutions :
    Set.ncard { x : ℝ | x ≠ 0 ∧ Int.fract (x * Int.fract ((1 / x) *
      Int.fract (x * Int.fract (2 / x)))) + x ^ 3 = 0 } = 2 := by
  have keyn : ∀ (y : ℝ) (n : ℤ) (z : ℝ), z = y + (n : ℝ) → 0 ≤ z → z < 1 → Int.fract y = z := by
    intro y n z h h1 h2
    rw [Int.fract_eq_iff]
    refine ⟨h1, h2, -n, ?_⟩
    push_cast
    linarith
  have uniq : ∀ a b k : ℝ, 0 < k → a ^ 3 + k * a + 4 = 0 → b ^ 3 + k * b + 4 = 0 → a = b := by
    intro a b k hk ha hb
    have h : (a - b) * (a ^ 2 + a * b + b ^ 2 + k) = 0 := by linear_combination ha - hb
    rcases mul_eq_zero.mp h with h' | h'
    · linarith
    · nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
  have step : ∀ x : ℝ, -1 < x → x < -2 / 3 →
      x * (1 / x * Int.fract (x * Int.fract (2 / x))) = 3 + 3 * x := by
    intro x h1 h2
    have hx : x ≠ 0 := by intro h; rw [h] at h2; norm_num at h2
    have hinv1 : x * (1 / x) = 1 := by field_simp
    have hinv2 : x * (2 / x) = 2 := by field_simp
    have e1 : Int.fract (2 / x) = 2 / x + 3 :=
      keyn (2 / x) 3 (2 / x + 3) (by first | (push_cast; ring) | push_cast | norm_num)
        (by nlinarith [hinv2]) (by nlinarith [hinv2])
    have e2 : x * (2 / x + 3) = 2 + 3 * x := by rw [mul_add, hinv2]; ring
    have e3 : Int.fract (2 + 3 * x) = 3 + 3 * x :=
      keyn (2 + 3 * x) 1 (3 + 3 * x) (by first | (push_cast; ring) | push_cast | norm_num)
        (by linarith) (by linarith)
    rw [e1, e2, e3, ← mul_assoc, hinv1, one_mul]
  have main : ∀ x c : ℝ, x ≠ 0 → 0 ≤ c → c < 1 → Int.fract (x * c) + x ^ 3 = 0 →
      -1 < x ∧ x < -2 / 3 ∧ x * c + 1 = -x ^ 3 := by
    intro x c hx hc0 hc1 heq
    have hF : Int.fract (x * c) = -x ^ 3 := by linarith
    have hF0 : (0 : ℝ) ≤ -x ^ 3 := by rw [← hF]; exact Int.fract_nonneg _
    have hF1 : -x ^ 3 < 1 := by rw [← hF]; exact Int.fract_lt_one _
    have hxneg : x < 0 := by
      rcases lt_trichotomy x 0 with h | h | h
      · exact h
      · exact absurd h hx
      · exfalso; nlinarith [mul_pos (mul_pos h h) h]
    have hxgt : -1 < x := by
      by_contra hcon
      push_neg at hcon
      have hx2 : (1 : ℝ) ≤ x ^ 2 := by nlinarith
      nlinarith
    have hxc_le : x * c ≤ 0 := by nlinarith
    have hxc_gt : -1 < x * c := by nlinarith
    have hxceq : x * c + 1 = -x ^ 3 := by
      rcases eq_or_lt_of_le hxc_le with h | h
      · exfalso
        rw [h, Int.fract_zero] at hF
        nlinarith [mul_pos (mul_pos (neg_pos.mpr hxneg) (neg_pos.mpr hxneg)) (neg_pos.mpr hxneg)]
      · have hk := keyn (x * c) 1 (x * c + 1)
          (by first | (push_cast; ring) | push_cast | norm_num) (by linarith) (by linarith)
        rw [hk] at hF
        linarith
    refine ⟨hxgt, ?_, hxceq⟩
    have hcubic : x ^ 3 + x + 1 < 0 := by
      nlinarith [mul_pos (neg_pos.mpr hxneg) (sub_pos.mpr hc1)]
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x + 2 / 3) (sq_nonneg (x - 1 / 3))]
  obtain ⟨r1, hr1mem, hr1⟩ : ∃ r ∈ Set.Ioo (-1 : ℝ) (-3 / 4 : ℝ), r ^ 3 + 4 * r + 4 = 0 := by
    have hcont : ContinuousOn (fun t : ℝ => t ^ 3 + 4 * t + 4) (Set.Icc (-1 : ℝ) (-3 / 4)) := by
      fun_prop
    have h := intermediate_value_Ioo (by norm_num : (-1 : ℝ) ≤ -3 / 4) hcont
    have h0 : (0 : ℝ) ∈ Set.Ioo ((fun t : ℝ => t ^ 3 + 4 * t + 4) (-1))
        ((fun t : ℝ => t ^ 3 + 4 * t + 4) (-3 / 4)) := by
      norm_num [Set.mem_Ioo]
    obtain ⟨r, hr, hfr⟩ := h h0
    exact ⟨r, hr, hfr⟩
  obtain ⟨r2, hr2mem, hr2⟩ : ∃ r ∈ Set.Ioo (-3 / 4 : ℝ) (-2 / 3 : ℝ), r ^ 3 + 5 * r + 4 = 0 := by
    have hcont : ContinuousOn (fun t : ℝ => t ^ 3 + 5 * t + 4) (Set.Icc (-3 / 4 : ℝ) (-2 / 3)) := by
      fun_prop
    have h := intermediate_value_Ioo (by norm_num : (-3 / 4 : ℝ) ≤ -2 / 3) hcont
    have h0 : (0 : ℝ) ∈ Set.Ioo ((fun t : ℝ => t ^ 3 + 5 * t + 4) (-3 / 4))
        ((fun t : ℝ => t ^ 3 + 5 * t + 4) (-2 / 3)) := by
      norm_num [Set.mem_Ioo]
    obtain ⟨r, hr, hfr⟩ := h h0
    exact ⟨r, hr, hfr⟩
  obtain ⟨hr1a, hr1b⟩ := hr1mem
  obtain ⟨hr2a, hr2b⟩ := hr2mem
  have hne : r1 ≠ r2 := by intro h; rw [h] at hr1b; linarith
  have hmem1 : r1 ≠ 0 ∧ Int.fract (r1 * Int.fract ((1 / r1) *
      Int.fract (r1 * Int.fract (2 / r1)))) + r1 ^ 3 = 0 := by
    refine ⟨ne_of_lt (by linarith), ?_⟩
    have hA := step r1 hr1a (by linarith)
    set A := 1 / r1 * Int.fract (r1 * Int.fract (2 / r1)) with hAdef
    have hx0 : r1 < 0 := by linarith
    have hfA : Int.fract A = A + 1 :=
      keyn A 1 (A + 1) (by first | (push_cast; ring) | push_cast | norm_num)
        (by nlinarith) (by nlinarith)
    rw [hfA]
    have h5 : r1 * (A + 1) = 3 + 4 * r1 := by rw [mul_add, hA]; ring
    rw [h5]
    have hf2 : Int.fract (3 + 4 * r1) = 4 + 4 * r1 :=
      keyn (3 + 4 * r1) 1 (4 + 4 * r1) (by first | (push_cast; ring) | push_cast | norm_num)
        (by linarith) (by linarith)
    rw [hf2]
    linarith
  have hmem2 : r2 ≠ 0 ∧ Int.fract (r2 * Int.fract ((1 / r2) *
      Int.fract (r2 * Int.fract (2 / r2)))) + r2 ^ 3 = 0 := by
    refine ⟨ne_of_lt (by linarith), ?_⟩
    have hA := step r2 (by linarith) hr2b
    set A := 1 / r2 * Int.fract (r2 * Int.fract (2 / r2)) with hAdef
    have hx0 : r2 < 0 := by linarith
    have hfA : Int.fract A = A + 2 :=
      keyn A 2 (A + 2) (by first | (push_cast; ring) | push_cast | norm_num)
        (by nlinarith) (by nlinarith)
    rw [hfA]
    have h5 : r2 * (A + 2) = 3 + 5 * r2 := by rw [mul_add, hA]; ring
    rw [h5]
    have hf2 : Int.fract (3 + 5 * r2) = 4 + 5 * r2 :=
      keyn (3 + 5 * r2) 1 (4 + 5 * r2) (by first | (push_cast; ring) | push_cast | norm_num)
        (by linarith) (by linarith)
    rw [hf2]
    linarith
  have hset : { x : ℝ | x ≠ 0 ∧ Int.fract (x * Int.fract ((1 / x) *
      Int.fract (x * Int.fract (2 / x)))) + x ^ 3 = 0 } = {r1, r2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, heq⟩
      obtain ⟨hxgt, hxlt, hxceq⟩ :=
        main x (Int.fract (1 / x * Int.fract (x * Int.fract (2 / x)))) hx
          (Int.fract_nonneg _) (Int.fract_lt_one _) heq
      have hA := step x hxgt hxlt
      set A := 1 / x * Int.fract (x * Int.fract (2 / x)) with hAdef
      have hx0 : x < 0 := by linarith
      by_cases hc : x ≤ -3 / 4
      · have hfA : Int.fract A = A + 1 :=
          keyn A 1 (A + 1) (by first | (push_cast; ring) | push_cast | norm_num)
            (by nlinarith) (by nlinarith)
        rw [hfA] at hxceq
        have h5 : x * (A + 1) = 3 + 4 * x := by rw [mul_add, hA]; ring
        rw [h5] at hxceq
        exact Or.inl (uniq x r1 4 (by norm_num) (by linarith) hr1)
      · push_neg at hc
        have hfA : Int.fract A = A + 2 :=
          keyn A 2 (A + 2) (by first | (push_cast; ring) | push_cast | norm_num)
            (by nlinarith) (by nlinarith)
        rw [hfA] at hxceq
        have h5 : x * (A + 2) = 3 + 5 * x := by rw [mul_add, hA]; ring
        rw [h5] at hxceq
        exact Or.inr (uniq x r2 5 (by norm_num) (by linarith) hr2)
    · rintro (rfl | rfl)
      · exact hmem1
      · exact hmem2
  rw [hset]
  exact Set.ncard_pair hne
```
