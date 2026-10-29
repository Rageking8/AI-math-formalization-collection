# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `29 July 2026`\
Line count: `122`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem real_solutions_count_2026 :
    Set.ncard {x : ℝ | Int.fract x * (1026002 - x - (Int.floor x : ℝ) ^ 2) = 1} = 2026 := by
  have gen1 : ∀ A f : ℝ, 0 ≤ f → f < 1 → f * (A - f) = 1 →
      2 < A ∧ f = (A - Real.sqrt (A ^ 2 - 4)) / 2 := by
    intro A f hf0 hf1 hfe
    have hfpos : 0 < f := by
      rcases eq_or_lt_of_le hf0 with h | h
      · exfalso
        rw [← h] at hfe
        norm_num at hfe
      · exact h
    have hA2 : 2 < A := by
      nlinarith [mul_pos (sub_pos.mpr hf1) (sub_pos.mpr hf1)]
    refine ⟨hA2, ?_⟩
    have hsq : A ^ 2 - 4 = (A - 2 * f) ^ 2 := by linear_combination 4 * hfe
    rw [hsq, Real.sqrt_sq (by linarith)]
    ring
  have gen2 : ∀ A : ℝ, 2 < A →
      0 ≤ (A - Real.sqrt (A ^ 2 - 4)) / 2 ∧
        (A - Real.sqrt (A ^ 2 - 4)) / 2 < 1 ∧
          (A - Real.sqrt (A ^ 2 - 4)) / 2 * (A - (A - Real.sqrt (A ^ 2 - 4)) / 2) = 1 := by
    intro A hA
    have h4 : (0:ℝ) ≤ A ^ 2 - 4 := by nlinarith
    have hs2 : Real.sqrt (A ^ 2 - 4) ^ 2 = A ^ 2 - 4 := Real.sq_sqrt h4
    have hlt : Real.sqrt (A ^ 2 - 4) < A := by
      have h := Real.sqrt_lt_sqrt h4 (show A ^ 2 - 4 < A ^ 2 by linarith)
      rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ A)] at h
    have hgt : A - 2 < Real.sqrt (A ^ 2 - 4) := by
      have h5 : (A - 2) ^ 2 < A ^ 2 - 4 := by nlinarith
      have h6 := Real.sqrt_lt_sqrt (sq_nonneg (A - 2)) h5
      rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ A - 2)] at h6
    exact ⟨by linarith, by linarith, by linear_combination (-1/4 : ℝ) * hs2⟩
  have hfloor : ∀ (n : ℤ) (g : ℝ), 0 ≤ g → g < 1 → ⌊(n:ℝ) + g⌋ = n := by
    intro n g hg0 hg1
    have hle : n ≤ ⌊(n:ℝ) + g⌋ := Int.le_floor.mpr (by linarith)
    have hlt : ⌊(n:ℝ) + g⌋ < n + 1 := by
      apply Int.floor_lt.mpr
      push_cast
      linarith
    omega
  have hArange : ∀ n : ℤ, -1013 ≤ n → n ≤ 1012 → 2 < 1026002 - (n:ℝ) - (n:ℝ) ^ 2 := by
    intro n h1 h2
    have h1' : (-1013:ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
    have h2' : (n:ℝ) ≤ 1012 := by exact_mod_cast h2
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ) + 1013)
      (by linarith : (0:ℝ) ≤ 1012 - (n:ℝ))]
  obtain ⟨F, hF⟩ : ∃ F : ℤ → ℝ, ∀ n : ℤ, F n = (n:ℝ) +
      (1026002 - (n:ℝ) - (n:ℝ) ^ 2 -
        Real.sqrt ((1026002 - (n:ℝ) - (n:ℝ) ^ 2) ^ 2 - 4)) / 2 := ⟨_, fun n => rfl⟩
  have hFmem : ∀ n : ℤ, -1013 ≤ n → n ≤ 1012 →
      ⌊F n⌋ = n ∧ Int.fract (F n) * (1026002 - F n - (⌊F n⌋ : ℝ) ^ 2) = 1 := by
    intro n h1 h2
    obtain ⟨hg0, hg1, hgeq⟩ := gen2 _ (hArange n h1 h2)
    have e0 : 0 ≤ F n - (n:ℝ) := by rw [hF n]; linarith
    have e1 : F n - (n:ℝ) < 1 := by rw [hF n]; linarith
    have efl : ⌊F n⌋ = n := by
      have h := hfloor n (F n - (n:ℝ)) e0 e1
      have h3 : (n:ℝ) + (F n - (n:ℝ)) = F n := by ring
      rwa [h3] at h
    have efr : Int.fract (F n) = F n - (n:ℝ) := by
      have h := Int.floor_add_fract (F n)
      rw [efl] at h
      linarith
    refine ⟨efl, ?_⟩
    rw [efr, efl, hF n]
    linear_combination hgeq
  have hkey : {x : ℝ | Int.fract x * (1026002 - x - (Int.floor x : ℝ) ^ 2) = 1}
      = F '' ↑(Finset.Icc (-1013 : ℤ) 1012) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe,
      Finset.mem_Icc]
    constructor
    · intro hx
      have hf0 := Int.fract_nonneg x
      have hf1 := Int.fract_lt_one x
      have hxe := Int.floor_add_fract x
      set n := ⌊x⌋ with hn
      set f := Int.fract x with hfd
      have hx' : f * ((1026002 - (n:ℝ) - (n:ℝ) ^ 2) - f) = 1 := by
        linear_combination hx - f * hxe
      obtain ⟨hA2, hfeq⟩ := gen1 (1026002 - (n:ℝ) - (n:ℝ) ^ 2) f hf0 hf1 hx'
      have hn1 : -1013 ≤ n := by
        by_contra hcon
        push_neg at hcon
        have h' : n ≤ -1014 := by omega
        have h'' : (n:ℝ) ≤ -1014 := by exact_mod_cast h'
        nlinarith [sq_nonneg ((n:ℝ) + 1014)]
      have hn2 : n ≤ 1012 := by
        by_contra hcon
        push_neg at hcon
        have h' : (1013:ℤ) ≤ n := by omega
        have h'' : (1013:ℝ) ≤ (n:ℝ) := by exact_mod_cast h'
        nlinarith [sq_nonneg ((n:ℝ) - 1013)]
      refine ⟨n, ⟨hn1, hn2⟩, ?_⟩
      rw [hF n, ← hfeq]
      exact hxe
    · rintro ⟨n, ⟨hn1, hn2⟩, rfl⟩
      exact (hFmem n hn1 hn2).2
  have hinj : Set.InjOn F ↑(Finset.Icc (-1013 : ℤ) 1012) := by
    intro a ha b hb hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    have h1 : ⌊F a⌋ = ⌊F b⌋ := by rw [hab]
    rw [(hFmem a ha.1 ha.2).1, (hFmem b hb.1 hb.2).1] at h1
    exact h1
  have hc : (Finset.Icc (-1013 : ℤ) 1012).card = 2026 := by
    first
      | (rw [Int.card_Icc]; rfl)
      | (rw [Int.card_Icc]; decide)
      | simp
      | decide
  have key : ((Finset.Icc (-1013 : ℤ) 1012 : Finset ℤ) : Set ℤ).ncard = 2026 := by
    classical
    first
      | (rw [Set.ncard_coe_Finset]; exact hc)
      | (simpa using hc)
      | (rw [Set.ncard_eq_toFinset_card']; simpa using hc)
      | (rw [← Set.Nat.card_coe_set_eq, Nat.card_eq_finsetCard]; exact hc)
      | (simp [Set.ncard_eq_toFinset_card', hc])
  rw [hkey, Set.ncard_image_of_injOn hinj]
  exact key
```
