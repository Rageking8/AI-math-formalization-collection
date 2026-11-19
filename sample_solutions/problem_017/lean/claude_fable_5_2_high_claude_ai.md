# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `15 November 2026`\
Line count: `122`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem real_solutions_count_2026 :
    Set.ncard {x : ℝ | Int.fract x * (1026002 - x - (Int.floor x : ℝ) ^ 2) = 1} = 2026 := by
  -- For each integer `n` with `c n ≥ 3` there is exactly one solution with floor `n`.
  set c : ℤ → ℝ := fun n => 1026002 - (n : ℝ) - (n : ℝ) ^ 2 with hc
  set g : ℤ → ℝ := fun n => (n : ℝ) + (c n - Real.sqrt (c n ^ 2 - 4)) / 2 with hg
  -- `c n ≥ 3` on the range
  have key : ∀ n : ℤ, n ∈ Finset.Icc (-1013 : ℤ) 1012 → 3 ≤ c n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨h1, h2⟩ := hn
    have h1' : (-1013 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    have h2' : (n : ℝ) ≤ 1012 := by exact_mod_cast h2
    simp only [hc]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1') (sub_nonneg.mpr h2')]
  -- properties of the fractional part of `g n`
  have hroot : ∀ t : ℝ, 3 ≤ t →
      0 < (t - Real.sqrt (t ^ 2 - 4)) / 2 ∧ (t - Real.sqrt (t ^ 2 - 4)) / 2 < 1 ∧
      (t - Real.sqrt (t ^ 2 - 4)) / 2 * (t - (t - Real.sqrt (t ^ 2 - 4)) / 2) = 1 := by
    intro t ht
    have h0 : (0 : ℝ) ≤ t ^ 2 - 4 := by nlinarith
    have hs0 : 0 ≤ Real.sqrt (t ^ 2 - 4) := Real.sqrt_nonneg _
    have hs2 : Real.sqrt (t ^ 2 - 4) ^ 2 = t ^ 2 - 4 := Real.sq_sqrt h0
    refine ⟨?_, ?_, ?_⟩
    · have : Real.sqrt (t ^ 2 - 4) < t := by nlinarith
      linarith
    · have : t - 2 < Real.sqrt (t ^ 2 - 4) := by nlinarith
      linarith
    · nlinarith
  have hfloor : ∀ n : ℤ, n ∈ Finset.Icc (-1013 : ℤ) 1012 → ⌊g n⌋ = n := by
    intro n hn
    obtain ⟨h1, h2, _⟩ := hroot (c n) (key n hn)
    rw [Int.floor_eq_iff]
    simp only [hg]
    constructor <;> linarith
  have hinj : Set.InjOn g (↑(Finset.Icc (-1013 : ℤ) 1012) : Set ℤ) := by
    intro a ha b hb hab
    have ha' := hfloor a (Finset.mem_coe.mp ha)
    have hb' := hfloor b (Finset.mem_coe.mp hb)
    rw [← ha', ← hb', hab]
  have hSeq : {x : ℝ | Int.fract x * (1026002 - x - (Int.floor x : ℝ) ^ 2) = 1}
      = g '' (↑(Finset.Icc (-1013 : ℤ) 1012) : Set ℤ) := by
    ext x
    constructor
    · intro hx
      have hx : Int.fract x * (1026002 - x - (Int.floor x : ℝ) ^ 2) = 1 := hx
      have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
      have hf1 : Int.fract x < 1 := Int.fract_lt_one x
      have hxe : x = (⌊x⌋ : ℝ) + Int.fract x := (Int.floor_add_fract x).symm
      -- rewrite the equation in terms of `f` and `c`
      have heq : Int.fract x * (c ⌊x⌋ - Int.fract x) = 1 := by
        have : c ⌊x⌋ - Int.fract x = 1026002 - x - (⌊x⌋ : ℝ) ^ 2 := by
          simp only [hc]
          linarith
        rw [this]
        exact hx
      have hfpos : 0 < Int.fract x := by
        rcases hf0.lt_or_eq with h | h
        · exact h
        · rw [← h] at heq
          norm_num at heq
      -- `c > 2`
      have hc2 : 2 < c ⌊x⌋ := by
        by_contra hcon
        have hcon := not_lt.mp hcon
        nlinarith [mul_pos hfpos (sub_pos.mpr hf1), sq_nonneg (1 - Int.fract x),
          mul_nonneg hf0 (sub_nonneg.mpr hcon)]
      -- hence `c ≥ 3` because `c` is an integer
      have hcint : c ⌊x⌋ = ((1026002 - ⌊x⌋ - ⌊x⌋ ^ 2 : ℤ) : ℝ) := by
        simp only [hc]
        push_cast
        ring
      have hc3z : (3 : ℤ) ≤ 1026002 - ⌊x⌋ - ⌊x⌋ ^ 2 := by
        have : ((2 : ℤ) : ℝ) < ((1026002 - ⌊x⌋ - ⌊x⌋ ^ 2 : ℤ) : ℝ) := by
          rw [← hcint]
          exact_mod_cast hc2
        have := Int.cast_lt.mp this
        omega
      have hc3 : 3 ≤ c ⌊x⌋ := by
        rw [hcint]
        exact_mod_cast hc3z
      have hmem : ⌊x⌋ ∈ Finset.Icc (-1013 : ℤ) 1012 := by
        rw [Finset.mem_Icc]
        constructor
        · by_contra hcon
          have : ⌊x⌋ ≤ -1014 := by omega
          nlinarith
        · by_contra hcon
          have : 1013 ≤ ⌊x⌋ := by omega
          nlinarith
      refine ⟨⌊x⌋, Finset.mem_coe.mpr hmem, ?_⟩
      have hsq : c ⌊x⌋ ^ 2 - 4 = (c ⌊x⌋ - 2 * Int.fract x) ^ 2 := by
        nlinarith
      have hnn : 0 ≤ c ⌊x⌋ - 2 * Int.fract x := by linarith
      simp only [hg]
      rw [hsq, Real.sqrt_sq hnn]
      linarith
    · rintro ⟨n, hn, rfl⟩
      have hn := Finset.mem_coe.mp hn
      show Int.fract (g n) * (1026002 - g n - (Int.floor (g n) : ℝ) ^ 2) = 1
      obtain ⟨h1, h2, h3⟩ := hroot (c n) (key n hn)
      have hfl := hfloor n hn
      have hfr : Int.fract (g n) = (c n - Real.sqrt (c n ^ 2 - 4)) / 2 := by
        rw [Int.fract, hfl]
        simp only [hg]
        ring
      rw [hfr, hfl]
      have : (1026002 : ℝ) - g n - (n : ℝ) ^ 2
          = c n - (c n - Real.sqrt (c n ^ 2 - 4)) / 2 := by
        simp only [hg, hc]
        ring
      rw [this]
      exact h3
  rw [hSeq]
  first
    | rw [Set.InjOn.ncard_image hinj]
    | rw [Set.ncard_image_of_injOn hinj]
  first
    | rw [Set.ncard_coe_finset]
    | rw [Set.ncard_coe_Finset]
  simp
```
