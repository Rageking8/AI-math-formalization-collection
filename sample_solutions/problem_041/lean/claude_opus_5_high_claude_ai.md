# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `7 August 2026`\
Line count: `68`\
Turn count: `3`

## Solution

```lean4
import Mathlib

theorem no_pos_integers_factorial_eq :
    ¬ ∃ (x y : ℕ), 0 < x ∧ 0 < y ∧
      x.factorial + y.factorial = (x + y + 1) ^ 3 * Nat.gcd x.factorial y.factorial := by
  have poly1 : ∀ x : ℕ, 1 ≤ x → (x + 1) * (x + 2) * (x + 3) + 1 < (2 * x + 1) ^ 3 := by
    intro x hx
    obtain ⟨w, rfl⟩ : ∃ w, x = w + 1 := ⟨x - 1, by omega⟩
    nlinarith [Nat.zero_le w, Nat.zero_le (w ^ 2), Nat.zero_le (w ^ 3)]
  have poly2 : ∀ z : ℕ, 6 ≤ z → (2 * z + 5) ^ 3 < (z + 1) * (z + 2) * (z + 3) * (z + 4) := by
    intro z hz
    obtain ⟨t, rfl⟩ : ∃ t, z = t + 6 := ⟨z - 6, by omega⟩
    nlinarith [Nat.zero_le t, Nat.zero_le (t ^ 2), Nat.zero_le (t ^ 3), Nat.zero_le (t ^ 4)]
  have key : ∀ x y : ℕ, 0 < x → x ≤ y →
      x.factorial + y.factorial ≠ (x + y + 1) ^ 3 * x.factorial := by
    intro x y hx hxy h
    rcases (show y ≤ 9 ∨ 9 < y by omega) with hy9 | hy9
    · have hx9 : x ≤ 9 := by omega
      have hy1 : 1 ≤ y := by omega
      clear hxy
      interval_cases x <;> interval_cases y <;> simp_all [Nat.factorial]
    · rcases (show y ≤ x + 3 ∨ x + 3 < y by omega) with hA | hB
      · have a1 : (x + 1).factorial = (x + 1) * x.factorial := Nat.factorial_succ x
        have a2 : (x + 2).factorial = (x + 2) * (x + 1).factorial := Nat.factorial_succ (x + 1)
        have a3 : (x + 3).factorial = (x + 3) * (x + 2).factorial := Nat.factorial_succ (x + 2)
        have e3 : (x + 3).factorial = (x + 1) * (x + 2) * (x + 3) * x.factorial := by
          rw [a3, a2, a1]; ring
        have hyle : y.factorial ≤ (x + 3).factorial := Nat.factorial_le (by omega)
        have hpos : 0 < x.factorial := Nat.factorial_pos x
        have hb : (x + 1) * (x + 2) * (x + 3) + 1 < (x + y + 1) ^ 3 :=
          lt_of_lt_of_le (poly1 x hx) (Nat.pow_le_pow_left (by omega) 3)
        have hlt : x.factorial + y.factorial < (x + y + 1) ^ 3 * x.factorial := by
          calc x.factorial + y.factorial
              ≤ x.factorial + (x + 1) * (x + 2) * (x + 3) * x.factorial := by
                rw [← e3]; exact Nat.add_le_add_left hyle _
            _ = ((x + 1) * (x + 2) * (x + 3) + 1) * x.factorial := by ring
            _ < (x + y + 1) ^ 3 * x.factorial := mul_lt_mul_of_pos_right hb hpos
        exact hlt.ne h
      · obtain ⟨z, rfl⟩ : ∃ z, y = z + 4 := ⟨y - 4, by omega⟩
        have hxz : x ≤ z := by omega
        have hz : 6 ≤ z := by omega
        have b1 : (z + 1).factorial = (z + 1) * z.factorial := Nat.factorial_succ z
        have b2 : (z + 2).factorial = (z + 2) * (z + 1).factorial := Nat.factorial_succ (z + 1)
        have b3 : (z + 3).factorial = (z + 3) * (z + 2).factorial := Nat.factorial_succ (z + 2)
        have b4 : (z + 4).factorial = (z + 4) * (z + 3).factorial := Nat.factorial_succ (z + 3)
        have e4 : (z + 4).factorial = (z + 1) * (z + 2) * (z + 3) * (z + 4) * z.factorial := by
          rw [b4, b3, b2, b1]; ring
        have hxf : x.factorial ≤ z.factorial := Nat.factorial_le hxz
        have hpos : 0 < x.factorial := Nat.factorial_pos x
        have hlt : (x + (z + 4) + 1) ^ 3 * x.factorial < x.factorial + (z + 4).factorial := by
          calc (x + (z + 4) + 1) ^ 3 * x.factorial
              ≤ (2 * z + 5) ^ 3 * x.factorial :=
                Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 3) (le_refl _)
            _ < (z + 1) * (z + 2) * (z + 3) * (z + 4) * x.factorial :=
                mul_lt_mul_of_pos_right (poly2 z hz) hpos
            _ ≤ (z + 1) * (z + 2) * (z + 3) * (z + 4) * z.factorial :=
                Nat.mul_le_mul (le_refl _) hxf
            _ = (z + 4).factorial := e4.symm
            _ ≤ x.factorial + (z + 4).factorial := Nat.le_add_left _ _
        exact hlt.ne' h
  rintro ⟨x, y, hx, hy, h⟩
  rcases le_total x y with hxy | hxy
  · refine key x y hx hxy ?_
    rwa [Nat.gcd_eq_left (Nat.factorial_dvd_factorial hxy)] at h
  · refine key y x hy hxy ?_
    rw [Nat.gcd_comm, Nat.gcd_eq_left (Nat.factorial_dvd_factorial hxy)] at h
    rw [show y + x + 1 = x + y + 1 from by omega, Nat.add_comm y.factorial x.factorial]
    exact h
```
