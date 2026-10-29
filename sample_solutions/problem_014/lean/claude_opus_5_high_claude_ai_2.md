# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `12 August 2026`\
Line count: `58`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem sqrt_x_add_y_irrational (x y : ℚ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 + y^2 + 1 = 3 * x * y) :
      Irrational (Real.sqrt (x + y : ℝ)) := by
  have hp5 : Prime (5 : ℤ) := by norm_num
  have h5 : ∀ u v w : ZMod 5, u ^ 4 = 5 * v ^ 2 + 4 * w ^ 4 → u = 0 ∧ w = 0 := by decide
  have main : ∀ N : ℕ, ∀ a c m : ℤ, m.natAbs ≤ N → m ≠ 0 →
      a ^ 4 = 5 * c ^ 2 + 4 * m ^ 4 → False := by
    intro N
    induction N with
    | zero => intro a c m h1 h2 _; exact h2 (Int.natAbs_eq_zero.mp (Nat.le_zero.mp h1))
    | succ N ih =>
      intro a c m hle hm heq
      have hz : (a : ZMod 5) ^ 4 = 5 * (c : ZMod 5) ^ 2 + 4 * (m : ZMod 5) ^ 4 := by
        have h' : ((a ^ 4 : ℤ) : ZMod 5) = ((5 * c ^ 2 + 4 * m ^ 4 : ℤ) : ZMod 5) := by rw [heq]
        push_cast at h'; linear_combination h'
      obtain ⟨ha0, hm0⟩ := h5 _ _ _ hz
      obtain ⟨a, rfl⟩ : (5 : ℤ) ∣ a := by
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd a 5).mp ha0
      obtain ⟨m, rfl⟩ : (5 : ℤ) ∣ m := by
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd m 5).mp hm0
      have h2 : c ^ 2 = 125 * a ^ 4 - 500 * m ^ 4 :=
        mul_left_cancel₀ (by norm_num : (5:ℤ) ≠ 0) (by linear_combination -heq)
      obtain ⟨c, rfl⟩ := hp5.dvd_of_dvd_pow
        (⟨25 * a ^ 4 - 100 * m ^ 4, by linear_combination h2⟩ : (5:ℤ) ∣ c ^ 2)
      have h3 : c ^ 2 = 5 * a ^ 4 - 20 * m ^ 4 :=
        mul_left_cancel₀ (by norm_num : (25:ℤ) ≠ 0) (by linear_combination h2)
      obtain ⟨c, rfl⟩ := hp5.dvd_of_dvd_pow
        (⟨a ^ 4 - 4 * m ^ 4, by linear_combination h3⟩ : (5:ℤ) ∣ c ^ 2)
      exact ih a c m (by omega) (by rintro rfl; simp at hm)
        (mul_left_cancel₀ (by norm_num : (5:ℤ) ≠ 0) (by linear_combination -h3))
  rintro ⟨r, hr⟩
  have hx0 : (0:ℝ) ≤ (x:ℝ) + (y:ℝ) := by
    have h1 : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
    have h2 : (0:ℝ) < (y:ℝ) := by exact_mod_cast hy
    linarith
  have hq : r ^ 2 = x + y := by
    have h1 : (r:ℝ) ^ 2 = (x:ℝ) + (y:ℝ) := by rw [hr, Real.sq_sqrt hx0]
    exact_mod_cast h1
  have key : r ^ 4 = 5 * (x - y) ^ 2 + 4 := by
    linear_combination (r ^ 2 + x + y) * hq - 4 * h
  have hb : ((r.den : ℚ)) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hbd : (((x - y).den : ℚ)) ≠ 0 := by exact_mod_cast (x - y).den_ne_zero
  have hn1 : ((r.num : ℚ)) = r * (r.den : ℚ) := (div_eq_iff hb).mp (Rat.num_div_den r)
  have hn2 : (((x - y).num : ℚ)) = (x - y) * ((x - y).den : ℚ) :=
    (div_eq_iff hbd).mp (Rat.num_div_den (x - y))
  refine main ((r.den : ℤ) * ((x - y).den : ℤ)).natAbs (r.num * ((x - y).den : ℤ))
    ((x - y).num * (r.den : ℤ) * ((r.den : ℤ) * ((x - y).den : ℤ)))
    ((r.den : ℤ) * ((x - y).den : ℤ)) le_rfl
    (mul_ne_zero (by exact_mod_cast r.den_ne_zero) (by exact_mod_cast (x - y).den_ne_zero)) ?_
  have hQ : ((r.num * ((x - y).den : ℤ) : ℤ) : ℚ) ^ 4
      = 5 * (((x - y).num * (r.den : ℤ) * ((r.den : ℤ) * ((x - y).den : ℤ)) : ℤ) : ℚ) ^ 2
        + 4 * ((((r.den : ℤ) * ((x - y).den : ℤ)) : ℤ) : ℚ) ^ 4 := by
    push_cast
    rw [hn1, hn2]
    linear_combination ((r.den : ℚ) ^ 4 * ((x - y).den : ℚ) ^ 4) * key
  exact_mod_cast hQ
```
