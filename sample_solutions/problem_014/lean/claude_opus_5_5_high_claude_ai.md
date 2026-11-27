# Claude Opus 5.5 High (Claude AI)

Model: `Claude Opus 5.5 High` (via Claude AI)\
Date: `24 September 2026`\
Line count: `67`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem sqrt_x_add_y_irrational (x y : ℚ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 + y^2 + 1 = 3 * x * y) :
      Irrational (Real.sqrt (x + y : ℝ)) := by
  rintro ⟨r, hr⟩
  have hx' : (0:ℝ) < x := by exact_mod_cast hx
  have hy' : (0:ℝ) < y := by exact_mod_cast hy
  have hxy : (0:ℝ) ≤ (x:ℝ) + y := by linarith
  have hr2 : r ^ 2 = x + y := by
    have h1 : ((r:ℝ))^2 = (x:ℝ) + y := by
      rw [hr, Real.sq_sqrt hxy]
    exact_mod_cast h1
  have key : 5 * (r ^ 4 - 4) = (5 * (x - y)) ^ 2 := by
    linear_combination (-20) * h + 5 * (r^2 + x + y) * hr2
  have hq : (5 * (x - y) * (r.den:ℚ)^2)^2 = 5 * ((r.num:ℚ)^4 - 4 * (r.den:ℚ)^4) := by
    rw [← Rat.mul_den_eq_num r]
    linear_combination (r.den:ℚ)^4 * key.symm
  generalize hqq : 5 * (x - y) * (r.den:ℚ)^2 = q at hq
  have hZ : q.num^2 = 5 * (r.num^4 - 4 * (r.den:ℤ)^4) * (q.den:ℤ)^2 := by
    have h' : ((q.num:ℚ))^2 = 5 * ((r.num:ℚ)^4 - 4 * (r.den:ℚ)^4) * (q.den:ℚ)^2 := by
      rw [← Rat.mul_den_eq_num q]
      linear_combination (q.den:ℚ)^2 * hq
    exact_mod_cast h'
  have cop : ∀ a b : ℤ, Nat.Coprime a.natAbs b.natAbs → (5:ℤ) ∣ a → (5:ℤ) ∣ b → False := by
    intro a b hab ha hb
    have h1 : (5:ℕ) ∣ a.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr ha
      simpa using this
    have h2 : (5:ℕ) ∣ b.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hb
      simpa using this
    have := Nat.dvd_gcd h1 h2
    rw [hab.gcd_eq_one] at this
    norm_num at this
  have main : ∀ n u V D : ℤ, Nat.Coprime n.natAbs D.natAbs → Nat.Coprime u.natAbs V.natAbs →
      n^2 = 5 * (u^4 - 4 * V^4) * D^2 → False := by
    intro n u V D hnD huV hZ
    have z5 : (5 : ZMod 5) = 0 := by decide
    have h5 := congrArg (Int.cast : ℤ → ZMod 5) hZ
    push_cast at h5
    have h5' : (n : ZMod 5)^2 = 0 := by
      linear_combination h5 + ((u:ZMod 5)^4 - 4*(V:ZMod 5)^4) * (D:ZMod 5)^2 * z5
    have hn0 : (n : ZMod 5) = 0 := by
      have k : ∀ a : ZMod 5, a^2 = 0 → a = 0 := by decide
      exact k _ h5'
    have hn5 : (5:ℤ) ∣ n := by
      exact_mod_cast (CharP.intCast_eq_zero_iff (ZMod 5) 5 n).mp hn0
    obtain ⟨e, he⟩ := hn5
    have h6 : 5 * e^2 = (u^4 - 4 * V^4) * D^2 := by
      have : (5:ℤ) * (5 * e^2) = 5 * ((u^4 - 4 * V^4) * D^2) := by
        rw [he] at hZ; linear_combination hZ
      exact mul_left_cancel₀ (by norm_num) this
    have h7 := congrArg (Int.cast : ℤ → ZMod 5) h6
    push_cast at h7
    have h7' : ((u:ZMod 5)^4 - 4*(V:ZMod 5)^4) * (D:ZMod 5)^2 = 0 := by
      linear_combination (-1 : ZMod 5) * h7 + (e:ZMod 5)^2 * z5
    have k2 : ∀ a b c : ZMod 5, (a^4 - 4*b^4)*c^2 = 0 → (a = 0 ∧ b = 0) ∨ c = 0 := by
      decide
    rcases k2 _ _ _ h7' with ⟨hu0, hv0⟩ | hd0
    · exact cop u V huV
        (by exact_mod_cast (CharP.intCast_eq_zero_iff (ZMod 5) 5 u).mp hu0)
        (by exact_mod_cast (CharP.intCast_eq_zero_iff (ZMod 5) 5 V).mp hv0)
    · exact cop n D hnD ⟨e, he⟩
        (by exact_mod_cast (CharP.intCast_eq_zero_iff (ZMod 5) 5 D).mp hd0)
  exact main q.num r.num (r.den:ℤ) (q.den:ℤ) (by simpa using q.reduced)
    (by simpa using r.reduced) hZ
```
