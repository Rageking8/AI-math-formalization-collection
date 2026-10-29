# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `12 August 2026`\
Line count: `78`\
Turn count: `5`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem real_solutions_count_2026 :
    Set.ncard {x : ℝ | Int.fract x * (1026002 - x - (Int.floor x : ℝ) ^ 2) = 1} = 2026 := by
  have hfr : ∀ x : ℝ, Int.fract x = x - (⌊x⌋ : ℝ) := fun _ => rfl
  have L1 : ∀ n : ℤ, n ∈ Finset.Icc (-1013 : ℤ) 1012 →
      (3 : ℝ) ≤ 1026002 - (n : ℝ) - (n : ℝ) ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h : n ^ 2 + n ≤ 1025156 := by nlinarith [hn.1, hn.2]
    have h' : (n : ℝ) ^ 2 + (n : ℝ) ≤ 1025156 := by exact_mod_cast h
    linarith
  have L2 : ∀ n : ℤ, (0 : ℝ) < 1026002 - (n : ℝ) - (n : ℝ) ^ 2 →
      n ∈ Finset.Icc (-1013 : ℤ) 1012 := by
    intro n h
    have h' : (0 : ℤ) < 1026002 - n - n ^ 2 := by exact_mod_cast h
    rw [Finset.mem_Icc]
    constructor <;> nlinarith [h']
  have main : ∀ x : ℝ, Int.fract x * (1026002 - x - (⌊x⌋ : ℝ) ^ 2) = 1 →
      Int.fract x * (1026002 - (⌊x⌋ : ℝ) - (⌊x⌋ : ℝ) ^ 2 - Int.fract x) = 1 ∧
      (3 : ℝ) ≤ 1026002 - (⌊x⌋ : ℝ) - (⌊x⌋ : ℝ) ^ 2 ∧
      ⌊x⌋ ∈ Finset.Icc (-1013 : ℤ) 1012 := by
    intro x hx
    rw [show (1026002 : ℝ) - x - (⌊x⌋ : ℝ) ^ 2
        = 1026002 - (⌊x⌋ : ℝ) - (⌊x⌋ : ℝ) ^ 2 - Int.fract x by rw [hfr x]; ring] at hx
    have h0 : 0 ≤ Int.fract x := Int.fract_nonneg x
    have hp : 0 < Int.fract x := by
      rcases h0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hx; norm_num at hx
    have hc := L2 ⌊x⌋ (by nlinarith [hx, hp, sq_nonneg (Int.fract x)])
    exact ⟨hx, L1 _ hc, hc⟩
  have E : ∀ c : ℝ, 3 ≤ c → ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t * (c - t) = 1 := by
    intro c hc
    have h4 : (0 : ℝ) ≤ c ^ 2 - 4 := by nlinarith
    have hs : Real.sqrt (c ^ 2 - 4) ^ 2 = c ^ 2 - 4 := Real.sq_sqrt h4
    have hs0 : 0 ≤ Real.sqrt (c ^ 2 - 4) := Real.sqrt_nonneg _
    exact ⟨(c - Real.sqrt (c ^ 2 - 4)) / 2, by nlinarith [hs, hs0, hc],
      by nlinarith [hs, hs0, hc], by linear_combination (-1 / 4 : ℝ) * hs⟩
  have hbij : Set.BijOn (fun x : ℝ => ⌊x⌋)
      {x : ℝ | Int.fract x * (1026002 - x - (Int.floor x : ℝ) ^ 2) = 1}
      ↑(Finset.Icc (-1013 : ℤ) 1012) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simpa using (main x hx).2.2
    · intro x hx y hy hxy
      have hxy' : ⌊x⌋ = ⌊y⌋ := hxy
      obtain ⟨hx1, hx3, -⟩ := main x hx
      obtain ⟨hy1, -, -⟩ := main y hy
      rw [hxy'] at hx1 hx3
      have h1 := Int.fract_lt_one x
      have h2 := Int.fract_lt_one y
      have hz : (Int.fract x - Int.fract y) *
          (Int.fract x + Int.fract y - (1026002 - (⌊y⌋ : ℝ) - (⌊y⌋ : ℝ) ^ 2)) = 0 := by
        linear_combination hy1 - hx1
      have hf : Int.fract x = Int.fract y := by
        rcases mul_eq_zero.1 hz with h | h
        · linarith
        · exfalso; linarith
      have hf2 : x - (⌊x⌋ : ℝ) = y - (⌊y⌋ : ℝ) := hf
      rw [hxy'] at hf2
      linarith
    · intro n hn
      obtain ⟨t, ht0, ht1, hteq⟩ := E _ (L1 n (by simpa using hn))
      have hfl : ⌊(n : ℝ) + t⌋ = n := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      refine ⟨(n : ℝ) + t, ?_, hfl⟩
      have hft : Int.fract ((n : ℝ) + t) = t := by
        show (n : ℝ) + t - (⌊(n : ℝ) + t⌋ : ℝ) = t
        rw [hfl]; ring
      show Int.fract ((n : ℝ) + t) *
        (1026002 - ((n : ℝ) + t) - (⌊(n : ℝ) + t⌋ : ℝ) ^ 2) = 1
      rw [hft, hfl]
      linear_combination hteq
  have hcard := Nat.card_congr (Set.BijOn.equiv _ hbij)
  have h2 : Nat.card (↑(Finset.Icc (-1013 : ℤ) 1012) : Set ℤ) = 2026 := by
    simp
  exact hcard.trans h2
```
