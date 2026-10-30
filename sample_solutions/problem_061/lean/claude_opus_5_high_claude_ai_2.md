# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `3 September 2026`\
Line count: `127`\
Turn count: `4`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

private theorem frac_eq (r s : ℝ) (n : ℤ) (h1 : 0 ≤ s) (h2 : s < 1) (h3 : r - s = n) :
    Int.fract r = s :=
  Int.fract_eq_iff.mpr ⟨h1, h2, n, h3⟩

private theorem cubic_uniq (c a b : ℝ) (hc : 0 < c) (ha : a ^ 3 + c * a + 4 = 0)
    (hb : b ^ 3 + c * b + 4 = 0) : a = b := by
  have h : (a - b) * (a ^ 2 + a * b + b ^ 2 + c) = 0 := by linear_combination ha - hb
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]

private theorem exists_root (c a b : ℝ) (hab : a ≤ b) (h1 : a ^ 3 + c * a + 4 < 0)
    (h2 : 0 < b ^ 3 + c * b + 4) : ∃ x ∈ Set.Ioo a b, x ^ 3 + c * x + 4 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 + c * x + 4) (Set.Icc a b) := by fun_prop
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo hab hc (Set.mem_Ioo.mpr ⟨h1, h2⟩)
  exact ⟨y, hy, hy0⟩

private theorem chain_aux {x : ℝ} (h1 : -1 < x) (h2 : x < -2/3) :
    1 / x * Int.fract (x * Int.fract (2 / x)) = 3 + 3 / x := by
  have hx : x < 0 := by linarith
  have hx0 : x ≠ 0 := ne_of_lt hx
  have hu : x * (2 / x) = 2 := by field_simp
  have hn : 2 / x < 0 := div_neg_of_pos_of_neg (by norm_num) hx
  have hlo : -3 ≤ 2 / x := by nlinarith
  have hhi : 2 / x < -2 := by nlinarith
  rw [frac_eq (2 / x) (2 / x + 3) (-3) (by linarith) (by linarith) (by push_cast; ring),
      mul_add, hu,
      frac_eq (2 + x * 3) (3 * x + 3) (-1) (by linarith) (by linarith) (by push_cast; ring)]
  field_simp <;> ring

private theorem key_lo {x : ℝ} (h1 : -1 < x) (h2 : x ≤ -3/4) :
    Int.fract (1 / x * Int.fract (x * Int.fract (2 / x))) = 3 / x + 4 := by
  have hx : x < 0 := by linarith
  have hx0 : x ≠ 0 := ne_of_lt hx
  have hn : 3 / x < 0 := div_neg_of_pos_of_neg (by norm_num) hx
  have hv : x * (3 / x) = 3 := by field_simp
  have hlo : -4 ≤ 3 / x := by nlinarith
  have hhi : 3 / x < -3 := by nlinarith
  rw [chain_aux h1 (by linarith)]
  exact frac_eq (3 + 3 / x) (3 / x + 4) (-1) (by linarith) (by linarith) (by push_cast; ring)

private theorem key_hi {x : ℝ} (h1 : -3/4 < x) (h2 : x < -2/3) :
    Int.fract (1 / x * Int.fract (x * Int.fract (2 / x))) = 3 / x + 5 := by
  have hx : x < 0 := by linarith
  have hx0 : x ≠ 0 := ne_of_lt hx
  have hn : 3 / x < 0 := div_neg_of_pos_of_neg (by norm_num) hx
  have hv : x * (3 / x) = 3 := by field_simp
  have hlo : -5 ≤ 3 / x := by nlinarith
  have hhi : 3 / x < -4 := by nlinarith
  rw [chain_aux (by linarith) h2]
  exact frac_eq (3 + 3 / x) (3 / x + 5) (-2) (by linarith) (by linarith) (by push_cast; ring)

private theorem mem_lo {y : ℝ} (h1 : -1 < y) (h2 : y < -3/4) (h3 : y ^ 3 + 4 * y + 4 = 0) :
    Int.fract (y * Int.fract (1 / y * Int.fract (y * Int.fract (2 / y)))) + y ^ 3 = 0 := by
  have hy : y ≠ 0 := by intro h; rw [h] at h2; norm_num at h2
  have hv : y * (3 / y) = 3 := by field_simp
  rw [key_lo h1 h2.le, mul_add, hv,
      frac_eq (3 + y * 4) (4 * y + 4) (-1) (by linarith) (by linarith) (by push_cast; ring)]
  linarith

private theorem mem_hi {y : ℝ} (h1 : -3/4 < y) (h2 : y < -2/3) (h3 : y ^ 3 + 5 * y + 4 = 0) :
    Int.fract (y * Int.fract (1 / y * Int.fract (y * Int.fract (2 / y)))) + y ^ 3 = 0 := by
  have hy : y ≠ 0 := by intro h; rw [h] at h2; norm_num at h2
  have hv : y * (3 / y) = 3 := by field_simp
  rw [key_hi h1 h2, mul_add, hv,
      frac_eq (3 + y * 5) (5 * y + 4) (-1) (by linarith) (by linarith) (by push_cast; ring)]
  linarith

theorem fractional_part_equation_two_solutions :
    Set.ncard { x : ℝ | x ≠ 0 ∧ Int.fract (x * Int.fract ((1 / x) *
      Int.fract (x * Int.fract (2 / x)))) + x ^ 3 = 0 } = 2 := by
  obtain ⟨r, ⟨hr1, hr2⟩, hr0⟩ :=
    exists_root 4 (-1) (-3/4) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨s, ⟨hs1, hs2⟩, hs0⟩ :=
    exists_root 5 (-3/4) (-2/3) (by norm_num) (by norm_num) (by norm_num)
  have hne : r ≠ s := by intro h; rw [h] at hr2; linarith
  have hset : { x : ℝ | x ≠ 0 ∧ Int.fract (x * Int.fract ((1 / x) *
      Int.fract (x * Int.fract (2 / x)))) + x ^ 3 = 0 } = {r, s} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx0, heq⟩
      obtain ⟨C, hCdef⟩ :
          ∃ C : ℝ, Int.fract (1 / x * Int.fract (x * Int.fract (2 / x))) = C := ⟨_, rfl⟩
      have hC0 : 0 ≤ C := by rw [← hCdef]; exact Int.fract_nonneg _
      have hC1 : C < 1 := by rw [← hCdef]; exact Int.fract_lt_one _
      rw [hCdef] at heq
      have hD0 : (0:ℝ) ≤ Int.fract (x * C) := Int.fract_nonneg _
      have hD1 : Int.fract (x * C) < 1 := Int.fract_lt_one _
      have hxneg : x < 0 := by
        rcases lt_trichotomy x 0 with h | h | h
        · exact h
        · exact absurd h hx0
        · nlinarith [pow_pos h 3]
      have hxgt : -1 < x := by nlinarith [sq_nonneg x, sq_nonneg (x + 1)]
      have hCpos : 0 < C := by
        rcases hC0.lt_or_eq with h | h
        · exact h
        · exfalso
          rw [← h, mul_zero, Int.fract_zero] at heq
          nlinarith [pow_pos (neg_pos.mpr hxneg) 3]
      have key : x < x * C := by
        nlinarith [mul_pos (neg_pos.mpr hxneg) (sub_pos.mpr hC1)]
      have hDval : Int.fract (x * C) = x * C + 1 :=
        frac_eq (x * C) (x * C + 1) (-1) (by linarith)
          (by linarith [mul_neg_of_neg_of_pos hxneg hCpos]) (by push_cast; ring)
      rw [hDval] at heq
      have hxC : x * C = -x ^ 3 - 1 := by linarith
      have hcube : x ^ 3 + x + 1 < 0 := by linarith
      have h23 : x < -2/3 := by nlinarith [sq_nonneg (x - 1/3)]
      have hv : x * (3 / x) = 3 := by field_simp
      rcases le_or_gt x (-3/4) with hcase | hcase
      · left
        have hCeq : C = 3 / x + 4 := by rw [← hCdef, key_lo hxgt hcase]
        rw [hCeq, mul_add, hv] at hxC
        exact cubic_uniq 4 x r (by norm_num) (by linarith) hr0
      · right
        have hCeq : C = 3 / x + 5 := by rw [← hCdef, key_hi hcase h23]
        rw [hCeq, mul_add, hv] at hxC
        exact cubic_uniq 5 x s (by norm_num) (by linarith) hs0
    · rintro (rfl | rfl)
      · exact ⟨ne_of_lt (by linarith), mem_lo hr1 hr2 hr0⟩
      · exact ⟨ne_of_lt (by linarith), mem_hi hs1 hs2 hs0⟩
  rw [hset]
  exact Set.ncard_pair hne
```
