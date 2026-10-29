# Claude Opus 5 Medium (Arena AI)

Model: `claude-opus-5-medium` (via Arena AI)\
Date: `27 July 2026`\
Line count: `95`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem sqrt_x_add_y_irrational (x y : ℚ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 + y^2 + 1 = 3 * x * y) :
      Irrational (Real.sqrt (x + y : ℝ)) := by
  have hp5 : Prime (5:ℤ) := by norm_num
  have h5 : ∀ a b : ZMod 5, a^4 + b^4 = 0 → a = 0 ∧ b = 0 := by decide
  -- integer descent : A^4 = 4M^4 + 5B^2 forces A = 0
  have key : ∀ n : ℕ, ∀ A M B : ℤ, A.natAbs ≤ n → A^4 = 4*M^4 + 5*B^2 → A = 0 := by
    intro n
    induction n with
    | zero =>
      intro A M B hA _
      exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp hA)
    | succ n ih =>
      intro A M B hA hEq
      by_contra hA0
      have hdvd : (5:ℤ) ∣ A^4 + M^4 := ⟨B^2 + M^4, by linarith⟩
      have hzero : ((A^4 + M^4 : ℤ) : ZMod 5) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact_mod_cast hdvd
      have hz : ((A : ZMod 5))^4 + ((M : ZMod 5))^4 = 0 := by
        push_cast at hzero
        exact hzero
      obtain ⟨hA5, hM5⟩ := h5 _ _ hz
      have hA5' : (5:ℤ) ∣ A := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd A 5).mp hA5
        exact_mod_cast this
      have hM5' : (5:ℤ) ∣ M := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd M 5).mp hM5
        exact_mod_cast this
      obtain ⟨A1, rfl⟩ := hA5'
      obtain ⟨M1, rfl⟩ := hM5'
      have hB5 : (5:ℤ) ∣ B := by
        have h2 : (5:ℤ) ∣ B^2 := ⟨25*A1^4 - 100*M1^4, by linarith⟩
        exact hp5.dvd_of_dvd_pow h2
      obtain ⟨B1, rfl⟩ := hB5
      have hB15 : (5:ℤ) ∣ B1 := by
        have h2 : (5:ℤ) ∣ B1^2 := ⟨A1^4 - 4*M1^4, by linarith⟩
        exact hp5.dvd_of_dvd_pow h2
      obtain ⟨B2, rfl⟩ := hB15
      have hEq2 : A1^4 = 4*M1^4 + 5*B2^2 := by linarith
      have hA1ne : A1 ≠ 0 := by
        intro h0
        exact hA0 (by simp [h0])
      have hnat : (5 * A1).natAbs = 5 * A1.natAbs := Int.natAbs_mul 5 A1
      have hpos : 0 < A1.natAbs := Int.natAbs_pos.mpr hA1ne
      rw [hnat] at hA
      exact hA1ne (ih A1 M1 B2 (by omega) hEq2)
  have hden : ∀ q : ℚ, (q.num : ℚ) = q * (q.den : ℚ) := by
    intro q
    have hne : ((q.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
    rw [eq_comm, ← eq_div_iff hne]
    exact (Rat.num_div_den q).symm
  have key2 : ∀ q d : ℚ, q^4 = 4 + 5 * d^2 → False := by
    intro q d hqd
    have hq := hden q
    have hd := hden d
    have hEqQ : ((q.num * (d.den:ℤ) : ℤ) : ℚ)^4
        = 4 * (((q.den:ℤ) * (d.den:ℤ) : ℤ) : ℚ)^4
          + 5 * ((d.num * (q.den:ℤ)^2 * (d.den:ℤ) : ℤ) : ℚ)^2 := by
      push_cast
      rw [hq, hd]
      linear_combination ((q.den:ℚ)^4 * (d.den:ℚ)^4) * hqd
    have hEqZ : (q.num * (d.den:ℤ))^4
        = 4 * ((q.den:ℤ) * (d.den:ℤ))^4
          + 5 * (d.num * (q.den:ℤ)^2 * (d.den:ℤ))^2 := by
      exact_mod_cast hEqQ
    have h0 : q.num * (d.den:ℤ) = 0 :=
      key (q.num * (d.den:ℤ)).natAbs (q.num * (d.den:ℤ)) ((q.den:ℤ) * (d.den:ℤ))
        (d.num * (q.den:ℤ)^2 * (d.den:ℤ)) le_rfl hEqZ
    have hdn : ((d.den:ℤ)) ≠ 0 := by exact_mod_cast d.den_ne_zero
    have hnum : q.num = 0 := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact h1
      · exact absurd h1 hdn
    have hq0 : q = 0 := by
      have hne : ((q.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
      have h2 : q * (q.den:ℚ) = 0 := by
        rw [← hq]
        exact_mod_cast hnum
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd h3 hne
    rw [hq0] at hqd
    nlinarith [sq_nonneg d]
  rintro ⟨r, hr⟩
  have hx' : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
  have hy' : (0:ℝ) < (y:ℝ) := by exact_mod_cast hy
  have hpos : (0:ℝ) ≤ (x:ℝ) + (y:ℝ) := by linarith
  have hsq : ((r:ℝ))^2 = (x:ℝ) + (y:ℝ) := by
    rw [hr]
    exact Real.sq_sqrt hpos
  have hsq' : r^2 = x + y := by exact_mod_cast hsq
  exact key2 r (x - y) (by linear_combination (r^2 + x + y) * hsq' - 4 * h)
```
