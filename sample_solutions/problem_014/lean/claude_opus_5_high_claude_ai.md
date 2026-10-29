# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `29 July 2026`\
Line count: `117`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem sqrt_x_add_y_irrational (x y : ℚ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 + y^2 + 1 = 3 * x * y) :
      Irrational (Real.sqrt (x + y : ℝ)) := by
  have hp5 : Prime (5:ℤ) := by norm_num
  have key : ∀ S N C D : ZMod 5, N ≠ 0 → D ≠ 0 →
      S * S + N * N = 0 → S * (D * D) - N * (C * C) = 0 → False := by
    set_option maxRecDepth 8000 in decide
  have core : ∀ M : ℕ, ∀ n : ℕ, n ≤ M → ∀ a b c d : ℤ, 0 < n →
      a^2 + b^2 + (n:ℤ)^2 = 3 * a * b → (a + b) * d^2 = (n:ℤ) * c^2 →
      ¬((5:ℤ) ∣ c ∧ (5:ℤ) ∣ d) → False := by
    intro M
    induction M with
    | zero =>
      intro n hn a b c d hn0 _ _ _
      omega
    | succ M ih =>
      intro n hnM a b c d hn0 heq hsq hcop
      by_cases h5 : (5:ℕ) ∣ n
      · obtain ⟨m, hm⟩ := h5
        have hm0 : 0 < m := by omega
        have hnZ : (n:ℤ) = 5 * (m:ℤ) := by omega
        rw [hnZ] at heq hsq
        have e1 : (a + b)^2 = 5 * (a * b - 5 * (m:ℤ)^2) := by linarith
        have habsq : (5:ℤ) ∣ (a + b)^2 := by rw [e1]; exact dvd_mul_right _ _
        obtain ⟨j, hj⟩ := hp5.dvd_of_dvd_pow habsq
        have ha : a = 5 * j - b := by linarith
        subst ha
        have e3 : b^2 = 5 * (j * b - j^2 - (m:ℤ)^2) := by linarith
        have hbsq : (5:ℤ) ∣ b^2 := by rw [e3]; exact dvd_mul_right _ _
        obtain ⟨b', hb'⟩ := hp5.dvd_of_dvd_pow hbsq
        subst hb'
        exact ih m (by omega) (j - b') b' c d hm0 (by linarith) (by linarith) hcop
      · have hn5Z : ¬ ((5:ℤ) ∣ (n:ℤ)) := by
          intro hcon
          exact h5 (by exact_mod_cast hcon)
        have hd5 : ¬ ((5:ℤ) ∣ d) := by
          intro hd
          refine hcop ⟨?_, hd⟩
          have h1 : (5:ℤ) ∣ (n:ℤ) * c^2 := by
            rw [← hsq]
            exact (dvd_pow hd (by norm_num)).mul_left (a + b)
          rcases hp5.dvd_mul.mp h1 with h' | h'
          · exact absurd h' hn5Z
          · exact hp5.dvd_of_dvd_pow h'
        have E1 : ((a : ZMod 5) + (b : ZMod 5)) * ((a : ZMod 5) + (b : ZMod 5))
            + (n : ZMod 5) * (n : ZMod 5) = 0 := by
          have h0 : (((a + b)^2 + (n:ℤ)^2 : ℤ) : ZMod 5) = 0 := by
            rw [CharP.intCast_eq_zero_iff (ZMod 5) 5]
            exact ⟨a * b, by push_cast; linear_combination heq⟩
          push_cast at h0
          linear_combination h0
        have E2 : ((a : ZMod 5) + (b : ZMod 5)) * ((d : ZMod 5) * (d : ZMod 5))
            - (n : ZMod 5) * ((c : ZMod 5) * (c : ZMod 5)) = 0 := by
          have h0 : (((a + b) * d^2 - (n:ℤ) * c^2 : ℤ) : ZMod 5) = 0 := by
            rw [CharP.intCast_eq_zero_iff (ZMod 5) 5]
            exact ⟨0, by push_cast; linear_combination hsq⟩
          push_cast at h0
          linear_combination h0
        have hN : ((n : ℕ) : ZMod 5) ≠ 0 := by
          intro hcon
          rw [CharP.cast_eq_zero_iff (ZMod 5) 5] at hcon
          exact h5 hcon
        have hD : ((d : ℤ) : ZMod 5) ≠ 0 := by
          intro hcon
          rw [CharP.intCast_eq_zero_iff (ZMod 5) 5] at hcon
          exact hd5 (by exact_mod_cast hcon)
        exact key _ _ _ _ hN hD E1 E2
  rintro ⟨q, hq⟩
  have hx' : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
  have hy' : (0:ℝ) < (y:ℝ) := by exact_mod_cast hy
  have hxy0 : (0:ℝ) ≤ (x:ℝ) + (y:ℝ) := by linarith
  have hq2 : ((q:ℝ))^2 = (x:ℝ) + (y:ℝ) := by rw [hq, Real.sq_sqrt hxy0]
  have hq2' : q^2 = x + y := by exact_mod_cast hq2
  have hxd : ((x.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_pos x).ne'
  have hyd : ((y.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_pos y).ne'
  have hqd : ((q.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_pos q).ne'
  have hxn : (x.num : ℚ) = x * (x.den : ℚ) := by
    have h' := Rat.num_div_den x
    rw [div_eq_iff hxd] at h'
    exact h'
  have hyn : (y.num : ℚ) = y * (y.den : ℚ) := by
    have h' := Rat.num_div_den y
    rw [div_eq_iff hyd] at h'
    exact h'
  have hqn : (q.num : ℚ) = q * (q.den : ℚ) := by
    have h' := Rat.num_div_den q
    rw [div_eq_iff hqd] at h'
    exact h'
  have hn0 : 0 < x.den * y.den := mul_pos (Rat.den_pos x) (Rat.den_pos y)
  have key1 : ((x.num : ℚ) * (y.den : ℚ))^2 + ((y.num : ℚ) * (x.den : ℚ))^2
      + ((x.den : ℚ) * (y.den : ℚ))^2
      = 3 * ((x.num : ℚ) * (y.den : ℚ)) * ((y.num : ℚ) * (x.den : ℚ)) := by
    rw [hxn, hyn]
    linear_combination ((x.den : ℚ) * (y.den : ℚ))^2 * h
  have key2 : ((x.num : ℚ) * (y.den : ℚ) + (y.num : ℚ) * (x.den : ℚ)) * ((q.den : ℚ))^2
      = ((x.den : ℚ) * (y.den : ℚ)) * ((q.num : ℚ))^2 := by
    rw [hxn, hyn, hqn]
    linear_combination (-((x.den : ℚ) * (y.den : ℚ) * (q.den : ℚ)^2)) * hq2'
  have heqZ : (x.num * (y.den : ℤ))^2 + (y.num * (x.den : ℤ))^2
      + ((x.den * y.den : ℕ) : ℤ)^2
      = 3 * (x.num * (y.den : ℤ)) * (y.num * (x.den : ℤ)) := by exact_mod_cast key1
  have hsqZ : ((x.num * (y.den : ℤ)) + (y.num * (x.den : ℤ))) * ((q.den : ℤ))^2
      = ((x.den * y.den : ℕ) : ℤ) * q.num^2 := by exact_mod_cast key2
  have hcop : ¬((5:ℤ) ∣ q.num ∧ (5:ℤ) ∣ ((q.den : ℤ))) := by
    rintro ⟨hc, hd⟩
    have h1 : (5:ℕ) ∣ q.num.natAbs := by
      obtain ⟨k, hk⟩ := hc
      exact ⟨k.natAbs, by rw [hk]; simp [Int.natAbs_mul]⟩
    have h2 : (5:ℕ) ∣ q.den := by exact_mod_cast hd
    have h3 : (5:ℕ) ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd q.num.natAbs q.den = 1 := q.reduced
    rw [h4] at h3
    omega
  exact core (x.den * y.den) (x.den * y.den) le_rfl (x.num * (y.den : ℤ))
    (y.num * (x.den : ℤ)) q.num ((q.den : ℤ)) hn0 heqZ hsqZ hcop
```
