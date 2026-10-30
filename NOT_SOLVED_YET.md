# Not solved yet

List of potentially unsound problems that have not been solved by an AI system. Problems here generally fall into two buckets: those that pose genuine mathematical difficulties or are open problems, and those that present challenges in formalization.

## Problems

Below are the problems sorted into categories.

### General

```lean4
import Mathlib

noncomputable def P (n : ℕ) : ℕ := sInf { p : ℕ | Nat.Prime p ∧ n < p }

theorem next_prime_quadratic_eq_iff_two (n : ℕ) (hn : 0 < n) :
    (P n : ℝ) = ((n : ℝ) ^ 2 - (n : ℝ) + 1) / ((P n : ℝ) - (n : ℝ)) ↔ n = 2 := by
  sorry
```

```lean4
import Mathlib

theorem digit_sum_prod_finitely_many_solutions :
    Set.Finite { n : ℕ | 0 < n ∧ ((Nat.digits 10 n).sum) ^ 2 + 8 = (Nat.digits 10 n).prod } := by
  sorry
```

```lean4
import Mathlib

theorem binom_equation_unique_solution (a b c d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
      (2 * a + 1) ^ (b + 2) - 1 = 2 ^ c * Nat.choose d (2 * a + 2) ↔
      a = 1 ∧ b = 2 ∧ c = 4 ∧ d = 5 := by
  sorry
```

```lean4
import Mathlib

def P (x : ℝ) : ℝ := x^2 + x + 1

theorem floor_p_pow_r_odd_even_iff (r : ℝ) :
    ({n : ℕ | 0 < n ∧ Even ⌊(P (n : ℝ)) ^ r⌋}.Infinite ∧
      {n : ℕ | 0 < n ∧ Odd ⌊(P (n : ℝ)) ^ r⌋}.Infinite) ↔
      (0 < r ∧ ¬ ∃ k : ℤ, r = (k : ℝ)) := by
  sorry
```

```lean4
import Mathlib

theorem digit_product_sq_eq_div (n : ℕ) (hn : 0 < n) :
    ((Nat.digits 10 n).prod) ^ 2 = Nat.floor ((n : ℝ) / 11) ↔
      n = 10 ∨ n = 11 ∨ n = 383113691144 := by
  sorry
```

```lean4
import Mathlib

theorem no_prime_solution_xy_2 (x y z : ℕ)
    (hx : Nat.Prime x) (hy : Nat.Prime y) (hz : Nat.Prime z) :
      x ^ y + 2 ≠ 2 ^ z + y ^ x := by
  sorry
```

```lean4
import Mathlib

theorem cube_add_one_dvd_unique_solution (x : ℕ) (hx : 0 < x) :
    x ^ 3 + 1 ∣ Nat.factorial x + 2 ^ (x ^ x) ↔ x = 2 := by
  sorry
```

```lean4
import Mathlib

theorem reciprocal_gcd_lcm_system_infinite_solutions :
    Set.Infinite { (x, y, z, n) : ℕ × ℕ × ℕ × ℕ |
      0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < n ∧
      (1 : ℚ) / x + (1 : ℚ) / y + (1 : ℚ) / z = (1 : ℚ) / (n + 7) ∧
      x * y * z = (Nat.gcd (Nat.gcd x y) z) ^ 5 * Nat.lcm z n } := by
  sorry
```

```lean4
import Mathlib

def InBase (b : ℕ) (n : ℕ) : ℕ :=
  Nat.ofDigits b (Nat.digits 10 n)

def R (n d : ℕ) : ℕ := d * ((10 ^ n - 1) / 9)

theorem no_pos_int_a_b_repdigit_in_base :
    ¬ ∃ (a b : ℕ), 0 < a ∧ 0 < b ∧
      (InBase b (R 9653 1) : ℤ) + (InBase b (R 3686 4) : ℤ) =
      (a : ℤ) ^ 3 - (b : ℤ) - 2 := by
  sorry
```

### Require theorems not in Lean Mathlib

Needs the Gelfond–Schneider theorem:

```lean4
import Mathlib

theorem transcendental_sin_cbrt6_arcsin_sub_arccos :
    Transcendental ℚ (Real.sin ((6 : ℝ) ^ (1 / 3 : ℝ) * Real.arcsin (1 / 3) - Real.arccos (2 / 7))) := by
  sorry
```
