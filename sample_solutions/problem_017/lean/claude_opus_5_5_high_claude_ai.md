# Claude Opus 5.5 High (Claude AI)

Model: `Claude Opus 5.5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `107`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem real_solutions_count_2026 :
    Set.ncard {x : ℝ | Int.fract x * (1026002 - x - (Int.floor x : ℝ) ^ 2) = 1} = 2026 := by
  -- the smaller root lies in (0,1) and solves f(a-f)=1
  have key : ∀ a : ℝ, 2 < a →
      0 < (a - Real.sqrt (a ^ 2 - 4)) / 2 ∧ (a - Real.sqrt (a ^ 2 - 4)) / 2 < 1 ∧
      (a - Real.sqrt (a ^ 2 - 4)) / 2 * (a - (a - Real.sqrt (a ^ 2 - 4)) / 2) = 1 := by
    intro a ha
    have h4 : 0 ≤ a ^ 2 - 4 := by nlinarith
    have hs : Real.sqrt (a ^ 2 - 4) ^ 2 = a ^ 2 - 4 := Real.sq_sqrt h4
    have hs0 : 0 ≤ Real.sqrt (a ^ 2 - 4) := Real.sqrt_nonneg _
    have h1 : Real.sqrt (a ^ 2 - 4) < a := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_le_mul hc hc (by linarith) hs0]
    have h2 : a - 2 < Real.sqrt (a ^ 2 - 4) := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_le_mul hc hc hs0 (by linarith)]
    refine ⟨by linarith, by linarith, ?_⟩
    linear_combination (-1/4 : ℝ) * hs
  -- uniqueness of the root in [0,1)
  have quad : ∀ a f : ℝ, 2 < a → f < 1 → f * (a - f) = 1 →
      f = (a - Real.sqrt (a ^ 2 - 4)) / 2 := by
    intro a f ha hf hx
    have h4 : 0 ≤ a ^ 2 - 4 := by nlinarith
    have hs : Real.sqrt (a ^ 2 - 4) ^ 2 = a ^ 2 - 4 := Real.sq_sqrt h4
    have hs0 : 0 ≤ Real.sqrt (a ^ 2 - 4) := Real.sqrt_nonneg _
    have hprod : (f - (a - Real.sqrt (a ^ 2 - 4)) / 2) *
        (f - (a + Real.sqrt (a ^ 2 - 4)) / 2) = 0 := by
      linear_combination (-1 : ℝ) * hx + (-1/4 : ℝ) * hs
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exfalso
      linarith
  have bound : ∀ n : ℤ, -1013 ≤ n → n ≤ 1012 → 2 < 1026002 - (n : ℝ) - (n : ℝ) ^ 2 := by
    intro n hn1 hn2
    have hint : n ^ 2 + n ≤ 1025156 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hn2)]
    have : ((n ^ 2 + n : ℤ) : ℝ) ≤ 1025156 := by exact_mod_cast hint
    push_cast at this
    linarith
  have flr : ∀ (n : ℤ) (g : ℝ), 0 ≤ g → g < 1 → ⌊(n : ℝ) + g⌋ = n := by
    intro n g h0 h1
    rw [Int.floor_eq_iff]
    constructor <;> linarith
  have aux : ∀ (n : ℤ) (g : ℝ), 0 ≤ g → g < 1 →
      g * ((1026002 - (n : ℝ) - (n : ℝ) ^ 2) - g) = 1 →
      Int.fract ((n : ℝ) + g) * (1026002 - ((n : ℝ) + g) - (⌊(n : ℝ) + g⌋ : ℝ) ^ 2) = 1 := by
    intro n g hg0 hg1 hg
    have hfl : ⌊(n : ℝ) + g⌋ = n := flr n g hg0 hg1
    have hfr : Int.fract ((n : ℝ) + g) = g := by
      unfold Int.fract
      rw [hfl]
      ring
    rw [hfr, hfl]
    linear_combination hg
  have hset : {x : ℝ | Int.fract x * (1026002 - x - (Int.floor x : ℝ) ^ 2) = 1} =
      (((Finset.Icc (-1013 : ℤ) 1012).image (fun n : ℤ => (n : ℝ) +
        ((1026002 - (n : ℝ) - (n : ℝ) ^ 2) -
          Real.sqrt ((1026002 - (n : ℝ) - (n : ℝ) ^ 2) ^ 2 - 4)) / 2)) : Set ℝ) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_image, Finset.mem_Icc]
    constructor
    · intro hx
      have hf0 := Int.fract_nonneg x
      have hf1 := Int.fract_lt_one x
      have hsum : (⌊x⌋ : ℝ) + Int.fract x = x := Int.floor_add_fract x
      have hx' : Int.fract x * ((1026002 - (⌊x⌋ : ℝ) - (⌊x⌋ : ℝ) ^ 2) - Int.fract x) = 1 := by
        linear_combination hx - (Int.fract x) * hsum
      have ha : 2 < 1026002 - (⌊x⌋ : ℝ) - (⌊x⌋ : ℝ) ^ 2 := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_le_mul_of_nonneg_left hc hf0,
          mul_pos (sub_pos.mpr hf1) (sub_pos.mpr hf1)]
      have hint : ⌊x⌋ ^ 2 + ⌊x⌋ < 1026000 := by
        have : ((⌊x⌋ ^ 2 + ⌊x⌋ : ℤ) : ℝ) < 1026000 := by
          push_cast
          linarith
        exact_mod_cast this
      have hlow : -1013 ≤ ⌊x⌋ := by
        by_contra hc
        have h' : ⌊x⌋ ≤ -1014 := by omega
        nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ -1014 - ⌊x⌋)
          (by linarith : (0:ℤ) ≤ -1014 - ⌊x⌋)]
      have hup : ⌊x⌋ ≤ 1012 := by
        by_contra hc
        have h' : 1013 ≤ ⌊x⌋ := by omega
        nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ ⌊x⌋ - 1013)
          (by linarith : (0:ℤ) ≤ ⌊x⌋ - 1013)]
      exact ⟨⌊x⌋, ⟨hlow, hup⟩, by linarith [quad _ _ ha hf1 hx', hsum]⟩
    · rintro ⟨n, ⟨hn1, hn2⟩, rfl⟩
      obtain ⟨h0, h1, heq⟩ := key _ (bound n hn1 hn2)
      exact aux n _ h0.le h1 heq
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn]
  · rw [Int.card_Icc]
    rfl
  · intro m hm k hk hmk
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hm hk
    have hm' := key _ (bound m hm.1 hm.2)
    have hk' := key _ (bound k hk.1 hk.2)
    have e1 := flr m _ hm'.1.le hm'.2.1
    have e2 := flr k _ hk'.1.le hk'.2.1
    rw [← e1, ← e2]
    exact congrArg Int.floor hmk
```
