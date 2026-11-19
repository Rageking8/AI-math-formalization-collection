# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `15 November 2026`\
Line count: `81`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem factorial_add_one_div_eq_iff_x_two_y_three
    (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
      ((x + y - 1).factorial + 1 : ℚ) / (x + y : ℚ) + 59 =
      (x.factorial : ℚ) ^ (y + 3) ↔ x = 2 ∧ y = 3 := by
  constructor
  · intro h
    -- Clear denominators and move to ℕ.
    have hn : (x + y - 1).factorial + (1 + 59 * (x + y))
        = (x + y) * x.factorial ^ (y + 3) := by
      have hpos : (x + y : ℚ) ≠ 0 := by positivity
      have h2 : ((x + y - 1).factorial + (1 + 59 * (x + y)) : ℚ)
          = (x + y) * (x.factorial : ℚ) ^ (y + 3) := by
        rw [← h]; field_simp; ring
      exact_mod_cast h2
    -- 2 ^ (m / 2) ∣ m!
    have key : ∀ m : ℕ, 2 ^ (m / 2) ∣ m.factorial := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        match m, ih with
        | 0, _ => simp
        | 1, _ => simp
        | (k + 2), ih =>
          have h1 := ih k (by omega)
          have h3 : (k + 2) / 2 = k / 2 + 1 := by omega
          have h4 : 2 ∣ (k + 1) * (k + 1 + 1) :=
            even_iff_two_dvd.mp (Nat.even_mul_succ_self (k + 1))
          have h5 : (k + 2).factorial = k.factorial * ((k + 1) * (k + 1 + 1)) := by
            rw [Nat.factorial_succ, Nat.factorial_succ]; ring
          rw [h3, pow_succ, h5]
          exact mul_dvd_mul h1 h4
    -- exponential growth bound
    have grow : ∀ k : ℕ, 11 ≤ k → 118 * k + 119 < 2 ^ k := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => norm_num
      | succ k hk ih => rw [pow_succ]; omega
    -- x ≥ 2
    have hx2 : 2 ≤ x := by
      by_contra hlt
      have hx1 : x = 1 := by omega
      subst hx1
      rw [Nat.factorial_one, one_pow, mul_one] at hn
      omega
    -- bound on x + y
    have hbound : x + y ≤ 22 := by
      by_contra hgt
      have hd1 : 2 ^ ((x + y - 1) / 2) ∣ (x + y - 1).factorial := key _
      have hle : (x + y - 1) / 2 ≤ (x / 2) * (y + 3) := by
        have ha : 1 ≤ x / 2 := by omega
        have hb : y + 3 ≤ (x / 2) * (y + 3) := Nat.le_mul_of_pos_left _ ha
        have hc : 3 * (x / 2) ≤ (x / 2) * (y + 3) := by
          rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
        have hc' : y * 1 ≤ y * (x / 2) := Nat.mul_le_mul_left _ ha
        have he : (x / 2) * (y + 3) = y * (x / 2) + 3 * (x / 2) := by ring
        omega
      have hd2 : 2 ^ ((x + y - 1) / 2) ∣ x.factorial ^ (y + 3) := by
        have h1 : (2 ^ (x / 2)) ^ (y + 3) ∣ x.factorial ^ (y + 3) :=
          pow_dvd_pow_of_dvd (key x) _
        rw [← pow_mul] at h1
        exact (pow_dvd_pow 2 hle).trans h1
      have hd3 : 2 ^ ((x + y - 1) / 2) ∣ 1 + 59 * (x + y) := by
        have h1 : 2 ^ ((x + y - 1) / 2) ∣
            (x + y - 1).factorial + (1 + 59 * (x + y)) := by
          rw [hn]; exact Dvd.dvd.mul_left hd2 _
        exact (Nat.dvd_add_right hd1).mp h1
      have h6 := Nat.le_of_dvd (by omega) hd3
      have h7 := grow ((x + y - 1) / 2) (by omega)
      omega
    -- finite check
    have hy' : y ≤ 20 := by omega
    have hx' : x ≤ 21 := by omega
    interval_cases x <;> interval_cases y <;>
      first
        | exact ⟨rfl, rfl⟩
        | omega
        | (norm_num [Nat.factorial] at hn)
  · rintro ⟨rfl, rfl⟩
    norm_num [Nat.factorial]
```
