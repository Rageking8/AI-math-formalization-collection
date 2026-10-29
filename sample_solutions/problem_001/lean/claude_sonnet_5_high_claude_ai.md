# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `30 July 2026`\
Line count: `133`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def seqA : ℕ → ℤ
  | 0 => 2
  | 1 => 5
  | (n + 2) => 5 * seqA (n + 1) - 2 * seqA n

lemma seqA_odd (n : ℕ) : Odd (seqA (n + 1)) := by
  induction n with
  | zero =>
    show Odd (seqA 1)
    exact ⟨2, by norm_num [seqA]⟩
  | succ k ih =>
    show Odd (seqA (k + 2))
    obtain ⟨m, hm⟩ := ih
    have hA : seqA (k + 2) = 5 * seqA (k + 1) - 2 * seqA k := by simp [seqA]
    refine ⟨5 * m - seqA k + 2, ?_⟩
    rw [hA, hm]
    ring

lemma alpha_beta_eq (n : ℕ) :
    (seqA n : ℝ) =
      (((5 : ℝ) + Real.sqrt 17) / 2) ^ n + (((5 : ℝ) - Real.sqrt 17) / 2) ^ n := by
  have h17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  set α : ℝ := (5 + Real.sqrt 17) / 2 with hα_def
  set β : ℝ := (5 - Real.sqrt 17) / 2 with hβ_def
  have hα2 : α ^ 2 = 5 * α - 2 := by
    rw [hα_def]
    have expand : ((5 + Real.sqrt 17) / 2 : ℝ) ^ 2
        = (25 + 10 * Real.sqrt 17 + Real.sqrt 17 ^ 2) / 4 := by ring
    rw [expand, h17]; ring
  have hβ2 : β ^ 2 = 5 * β - 2 := by
    rw [hβ_def]
    have expand : ((5 - Real.sqrt 17) / 2 : ℝ) ^ 2
        = (25 - 10 * Real.sqrt 17 + Real.sqrt 17 ^ 2) / 4 := by ring
    rw [expand, h17]; ring
  have hstep : ∀ (r : ℝ), r ^ 2 = 5 * r - 2 →
      ∀ k, r ^ (k + 2) = 5 * r ^ (k + 1) - 2 * r ^ k := by
    intro r hr k
    have s1 : r ^ (k + 1 + 1) = r ^ (k + 1) * r := pow_succ r (k + 1)
    have s2 : r ^ (k + 1) = r ^ k * r := pow_succ r k
    have e : r ^ (k + 2) = r ^ k * r ^ 2 := by
      have hk2 : k + 2 = k + 1 + 1 := by omega
      rw [hk2, s1, s2]; ring
    rw [e, hr, s2]; ring
  have main : ∀ n, (seqA n : ℝ) = α ^ n + β ^ n ∧
      (seqA (n + 1) : ℝ) = α ^ (n + 1) + β ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      constructor
      · show (seqA 0 : ℝ) = α ^ 0 + β ^ 0
        norm_num [seqA]
      · show (seqA 1 : ℝ) = α ^ 1 + β ^ 1
        have e1 : seqA 1 = 5 := by simp [seqA]
        rw [e1, pow_one, pow_one, hα_def, hβ_def]
        push_cast
        ring
    | succ k ih =>
      obtain ⟨ihk, ihk1⟩ := ih
      refine ⟨ihk1, ?_⟩
      show (seqA (k + 2) : ℝ) = α ^ (k + 2) + β ^ (k + 2)
      have hA : seqA (k + 2) = 5 * seqA (k + 1) - 2 * seqA k := by simp [seqA]
      have hcast : (seqA (k + 2) : ℝ) = 5 * (seqA (k + 1) : ℝ) - 2 * (seqA k : ℝ) := by
        rw [hA]; push_cast; ring
      have hstepA := hstep α hα2 k
      have hstepB := hstep β hβ2 k
      rw [hcast, ihk1, ihk, hstepA, hstepB]
      ring
  exact (main n).1

theorem ceil_pow_expr_odd (x : ℕ) :
    Odd ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ x⌉ := by
  have h17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 17 := Real.sqrt_nonneg 17
  have hlt5 : Real.sqrt 17 < 5 := by nlinarith [h17, hnn]
  have hgt3 : (3 : ℝ) < Real.sqrt 17 := by nlinarith [h17, hnn]
  have hβ_pos : (0 : ℝ) < (5 - Real.sqrt 17) / 2 := by linarith
  have hβ_lt1 : (5 - Real.sqrt 17) / 2 < 1 := by linarith
  cases x with
  | zero =>
    show Odd ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ 0⌉
    have h0 : (((5 : ℝ) + Real.sqrt 17) / 2) ^ 0 = 1 := pow_zero _
    rw [h0]
    have hc : (⌈(1 : ℝ)⌉ : ℤ) = 1 := by
      apply le_antisymm
      · exact Int.ceil_le.mpr (by norm_num)
      · have h2 : (0 : ℤ) < ⌈(1 : ℝ)⌉ := Int.lt_ceil.mpr (by norm_num)
        omega
    rw [hc]
    exact ⟨0, by norm_num⟩
  | succ y =>
    show Odd ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ (y + 1)⌉
    have key : (seqA (y + 1) : ℝ) =
        (((5 : ℝ) + Real.sqrt 17) / 2) ^ (y + 1) + ((5 - Real.sqrt 17) / 2) ^ (y + 1) :=
      alpha_beta_eq (y + 1)
    have hodd := seqA_odd y
    have hb_pow_pos : (0 : ℝ) < ((5 - Real.sqrt 17) / 2) ^ (y + 1) := pow_pos hβ_pos (y + 1)
    have hind : ∀ m, ((5 - Real.sqrt 17) / 2) ^ (m + 1) < 1 := by
      intro m
      induction m with
      | zero =>
        show ((5 - Real.sqrt 17) / 2) ^ 1 < 1
        rw [pow_one]
        exact hβ_lt1
      | succ k ih =>
        show ((5 - Real.sqrt 17) / 2) ^ (k + 1 + 1) < 1
        have e : ((5 - Real.sqrt 17) / 2) ^ (k + 1 + 1)
            = ((5 - Real.sqrt 17) / 2) ^ (k + 1) * ((5 - Real.sqrt 17) / 2) :=
          pow_succ _ (k + 1)
        rw [e]
        have step1 : ((5 - Real.sqrt 17) / 2) ^ (k + 1) * ((5 - Real.sqrt 17) / 2)
            < 1 * ((5 - Real.sqrt 17) / 2) :=
          mul_lt_mul_of_pos_right ih hβ_pos
        rw [one_mul] at step1
        linarith
    have hb_pow_lt1 : ((5 - Real.sqrt 17) / 2) ^ (y + 1) < 1 := hind y
    have heq : (((5 : ℝ) + Real.sqrt 17) / 2) ^ (y + 1)
        = (seqA (y + 1) : ℝ) - ((5 - Real.sqrt 17) / 2) ^ (y + 1) := by
      rw [key]; ring
    have hle : (((5 : ℝ) + Real.sqrt 17) / 2) ^ (y + 1) ≤ (seqA (y + 1) : ℝ) := by
      rw [heq]; linarith [hb_pow_pos]
    have hgt : ((seqA (y + 1) - 1 : ℤ) : ℝ) < (((5 : ℝ) + Real.sqrt 17) / 2) ^ (y + 1) := by
      rw [heq]; push_cast; linarith [hb_pow_lt1]
    have hceil_le : ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ (y + 1)⌉ ≤ seqA (y + 1) :=
      Int.ceil_le.mpr hle
    have hceil_ge : seqA (y + 1) ≤ ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ (y + 1)⌉ := by
      have hh := Int.lt_ceil.mpr hgt
      omega
    have hfin : ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ (y + 1)⌉ = seqA (y + 1) :=
      le_antisymm hceil_le hceil_ge
    rw [hfin]
    exact hodd
```
