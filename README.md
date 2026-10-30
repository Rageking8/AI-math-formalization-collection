# AI Math Formalization Collection

A collection of mostly novel math problems, along with their AI Lean/Rocq formalization.

## Problem creation process

### Scope

- Length: intentionally short (capped at 1-2 lines)
- Prerequisites: minimal topics needed, almost all problems should be comprehensible with high school level knowledge
- Difficulty: ranges from trivial to extremely hard, but the target is at the high school competition level

### Step 1: Brainstorm/initial problem

Various AI models are used to brainstorm a list of short, novel, and hard problems, typically guided by a human-provided seed topic. The seed topic varies in specificity, from just providing a sub-topic (e.g. "problem about probability and parity") to giving a detailed problem structure to follow (e.g. "equation involving sin, fractional part, and absolute value, such that there are no real solutions"). In some cases, the brainstorm process is replaced by a human-provided problem. From there, a candidate problem that seems interesting and meets the problem scope is selected.

### Step 2: Iterate

The candidate problem is given to various AI models to solve, helping gauge the difficulty and techniques required. In most cases, the problem at this point is too plain ("cookie-cutter" problems that lack originality and novelty) and too simple (easy to solve and/or requires little reasoning). Therefore, different AI models are used to iterate on the problem by increasing its difficulty and dimensionality. To prevent the model from drastically changing the essence of the candidate problem (the problem structure might already be favourable), it is instructed to "make minimal changes" and/or "preserve problem structure", while improving the problem's difficulty. The iteration process can continue for as many cycles as required, until a problem is deemed satisfactory. As a final check, the problem is given to AI models to solve to ensure soundness (problem is correct and solvable with a definitive solution) and wording precision (minimize ambiguity or inference needed to parse the problem).

### Step 3: Formalize/solve

Once the problem is more or less finalized, the natural language version is then given to an AI model, which converts it into Lean/Rocq. Care is taken to ensure the code is readable even with minimal experience with the language. If needed, an alternative formalization is requested and compared with existing ones. Once a version is chosen, AI models are then consulted on whether the natural language version matches the code version exactly. Lastly, the final code can be added as a new problem in the collection, and be given to various AI models to solve, before their solutions are added as samples.

## 1. Prove that $\left\lceil\left(\frac{5+\sqrt{17}}{2}\right)^x\right\rceil$ is odd for all natural $x$

```lean4
import Mathlib

theorem ceil_pow_expr_odd (x : ℕ) :
    Odd ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ x⌉ := by
  sorry
```

## 2. Prove that if $x + y + z = \pi$, then $\sin{x}\sin{y}\sin{z} \le \frac{3\sqrt{3}}{8}$

```lean4
import Mathlib

theorem sin_mul_upper_bound
    (x y z : ℝ)
    (h : x + y + z = Real.pi) :
    Real.sin x * Real.sin y * Real.sin z ≤
      (3 * Real.sqrt 3) / 8 := by
  sorry
```

## 3. Prove that no finite sum of distinct irreducible fractions of the form $\frac{2}{n}$ equals $\frac{5}{121}$

```lean4
import Mathlib

theorem no_distinct_irreducible_two_over_n_sum :
    ¬ ∃ (S : Finset ℕ), (∀ n ∈ S, n > 0 ∧ Nat.Coprime 2 n) ∧
      (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) = 5 / 121 := by
  sorry
```

## 4. Prove that $\left\lvert\ln{x}\right\rvert + \left\lvert\ln{y}\right\rvert \geq 2\ln{\left(\frac{x + y}{2\sqrt{xy}}\right)}$

```lean4
import Mathlib

theorem log_abs_sum_lower_bound (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    |Real.log x| + |Real.log y| ≥
      2 * Real.log ((x + y) / (2 * Real.sqrt (x * y))) := by
  sorry
```

## 5. Prove that if $1 < x < y$ and $x^y = y^x$, then $x^{y^y} > y^{x^x}$

```lean4
import Mathlib

theorem power_tower_inequality {x y : ℝ} (h1 : 1 < x) (h2 : x < y) (h3 : x ^ y = y ^ x) :
    x ^ (y ^ y) > y ^ (x ^ x) := by
  sorry
```

## 6. Prove that there are no positive integers $x$, $y$, and $z$ such that $((x \bmod y) \bmod z)((y \bmod z) \bmod x)((z \bmod x) \bmod y) = gcd(x, y, z)$

```lean4
import Mathlib

theorem no_mod_mod_mod_eq_gcd (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((x % y) % z) * ((y % z) % x) * ((z % x) % y) ≠ Nat.gcd x (Nat.gcd y z) := by
  sorry
```

## 7. Let $S(n)$ be the base-10 digit sum of $n$. Prove that for all positive integers $n$ and $x$, $S(n^x) \leq S(n)^x$

```lean4
import Mathlib

theorem digit_sum_pow_le (n x : ℕ) (hn : 0 < n) (hx : 0 < x) :
    (Nat.digits 10 (n ^ x)).sum ≤ ((Nat.digits 10 n).sum) ^ x := by
  sorry
```

## 8. Prove that there are no positive integers $x$ and $y$ such that $x^2 + 2x \mid y^2 + 1$

```lean4
import Mathlib

theorem no_x_sq_plus_two_x_dvd_y_sq_plus_one (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    ¬ (x^2 + 2*x ∣ y^2 + 1) := by
  sorry
```

## 9. Prove that if $n$ is a positive integer such that $n \mid 2^n + 1$ and $n \mid 3^n + 1$, then $n = 1$

```lean4
import Mathlib

theorem eq_one_of_dvd_pow_add_one (n : ℕ) (hn : 0 < n) (h2 : n ∣ 2^n + 1) (h3 : n ∣ 3^n + 1) :
    n = 1 := by
  sorry
```

## 10. Prove that there are no natural numbers $x$ and $y$ such that $(((x^3 + y^3) \bmod 18) \bmod 17) = 15$

```lean4
import Mathlib

theorem no_nat_cube_sum_mod_eq (x y : ℕ) :
    (((x^3 + y^3) % 18) % 17) ≠ 15 := by
  sorry
```

## 11. Prove that there are no real numbers $x$ and $y$ such that $x^2 + y^2 + 4 = 2\sqrt{x^2y + xy^2 + x + y}$

```lean4
import Mathlib

theorem no_real_solutions_x2_y2_4 (x y : ℝ) :
    x^2 + y^2 + 4 ≠ 2 * Real.sqrt (x^2 * y + x * y^2 + x + y) := by
  sorry
```

## 12. Prove that there are infinitely many triples of positive integers ($x$, $y$, $z$) such that $\frac{z^2}{x + y} + z = \frac{x^2 + 1}{y} + \frac{y^2 + 1}{x}$

```lean4
import Mathlib

theorem infinite_solutions_z2_x_y_z :
    Set.Infinite { (x, y, z) : ℕ × ℕ × ℕ |
      0 < x ∧ 0 < y ∧ 0 < z ∧
      ((z : ℚ) ^ 2 / ((x : ℚ) + (y : ℚ))) + (z : ℚ) =
      (((x : ℚ) ^ 2 + 1) / (y : ℚ)) + (((y : ℚ) ^ 2 + 1) / (x : ℚ)) } := by
  sorry
```

## 13. Prove that the only positive real number solutions to $x^\left\lceil x \right\rceil = \left\lceil x \right\rceil^\left\lfloor x \right\rfloor + 1$ are $\sqrt{3}$ and $\sqrt[3]{10}$

```lean4
import Mathlib

theorem ceil_floor_eq_solutions (x : ℝ) (hx : 0 < x) :
    x ^ ⌈x⌉ = (⌈x⌉ : ℝ) ^ ⌊x⌋ + 1 ↔ x = Real.sqrt 3 ∨ x = (10 : ℝ) ^ (1 / 3 : ℝ) := by
  sorry
```

## 14. Prove that if $x$ and $y$ are positive rational numbers such that $x^2 + y^2 + 1 = 3xy$, then $\sqrt{x + y}$ is irrational

```lean4
import Mathlib

theorem sqrt_x_add_y_irrational (x y : ℚ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 + y^2 + 1 = 3 * x * y) :
      Irrational (Real.sqrt (x + y : ℝ)) := by
  sorry
```

## 15. Prove that the only real number solution to $\frac{x \pm y}{x \mp y} = (x \mp y)(2 - x \mp y)$ is $x = 1$ and $y = 0$

```lean4
import Mathlib

theorem div_pm_mp_eq_one_zero (x y : ℝ) :
    (x - y ≠ 0 ∧ x + y ≠ 0 ∧
      (x + y) / (x - y) = (x - y) * (2 - x - y) ∧
      (x - y) / (x + y) = (x + y) * (2 - x + y)) ↔
      (x = 1 ∧ y = 0) := by
  sorry
```

## 16. Let $S(n)$ be the base-10 digit sum of $n$. Prove that for every natural number $k$, one can find a real polynomial $P$, such that there are exactly $k$ natural numbers $n$ satisfying the equation $n = P(S(n))$

```lean4
import Mathlib

theorem exists_polynomial_with_k_digit_sum_solutions (k : ℕ) :
    ∃ (P : Polynomial ℝ), ∃ (S : Finset ℕ), S.card = k ∧
      ∀ (n : ℕ), n ∈ S ↔ (n : ℝ) = P.eval ((Nat.digits 10 n).sum : ℝ) := by
  sorry
```

## 17. Let $\\{x\\}$ be the fractional part of $x$. Prove that the number of real solutions $x$ to the equation $\\{x\\}(1026002 - x - \lfloor x \rfloor^2) = 1$ is exactly 2026

```lean4
import Mathlib

theorem real_solutions_count_2026 :
    Set.ncard {x : ℝ | Int.fract x * (1026002 - x - (Int.floor x : ℝ) ^ 2) = 1} = 2026 := by
  sorry
```

## 18. Prove that there is no natural number $n$ such that the combined base-10 digits of $n^2$ and $n^3$ contain each of the digits from 1 to 9 exactly twice

```lean4
import Mathlib

theorem no_nat_sq_cube_digits_one_through_nine_twice :
    ¬ ∃ (n : ℕ), List.Perm (Nat.digits 10 (n ^ 2) ++ Nat.digits 10 (n ^ 3))
      (List.range' 1 9 ++ List.range' 1 9) := by
  sorry
```

## 19. Prove that $\displaystyle\sum_{n = 1}^{\infty} \frac{n(n + 4)}{lcm(n, n + 2, n + 4)^2} = \frac{35}{6} - \frac{55\pi^2}{96}$

```lean4
import Mathlib

theorem series_lcm_converges :
    HasSum (fun (n : ℕ) =>
      let n' := n + 1
      ((n' : ℝ) * (n' + 4)) / ((Nat.lcm (Nat.lcm n' (n' + 2)) (n' + 4) : ℝ) ^ 2))
      ((35 / 6 : ℝ) - ((55 * Real.pi ^ 2) / 96)) := by
  sorry
```

## 20. Let $S(n)$ be the base-10 digit sum of $n$ and $P(n)$ be a polynomial with non-negative integer coefficients. Prove that for all positive integers $n$, $S(P(n)) \le P(S(n))$

```lean4
import Mathlib

theorem digit_sum_polynomial_le (P : Polynomial ℕ) (n : ℕ) (hn : 0 < n) :
    (Nat.digits 10 (P.eval n)).sum ≤ P.eval (Nat.digits 10 n).sum := by
  sorry
```

## 21. Let $\\{x\\}$ be the fractional part of $x$. Prove that for all positive integers $n$, $\displaystyle\int_{0}^{n} x \cdot \left\\{\frac{n}{x}\right\\} \cdot \left\lceil\frac{n}{x}\right\rceil \\, dx = \frac{n^2}{2}$

```lean4
import Mathlib

open MeasureTheory

theorem integral_fract_ceil (n : ℕ) (hn : 0 < n) :
    ∫ x in (0 : ℝ)..(n : ℝ),
      x * Int.fract ((n : ℝ) / x) * (Int.ceil ((n : ℝ) / x) : ℝ) = ((n : ℝ) ^ 2) / 2 := by
  sorry
```

## 22. Prove that if $x$ and $y$ are positive real numbers such that $x^2 + y^2 = 1$, then $\frac{x^{2x}}{3y} + \frac{y^{2y}}{3x} \gt \frac{1}{x^2 + y^2 + 4xy}$

```lean4
import Mathlib

theorem positive_real_inequality (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y)
      (h_sum : x ^ 2 + y ^ 2 = 1) :
      ((x ^ (2 * x)) / (3 * y)) + ((y ^ (2 * y)) / (3 * x)) > 1 / (x ^ 2 + y ^ 2 + 4 * x * y) := by
  sorry
```

## 23. Prove that if $x$ and $y$ are distinct positive real numbers such that $x^y = y^x$, then $e^{x + y} \lt x^x \cdot y^y$

```lean4
import Mathlib

theorem distinct_pos_real_power_ineq (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hne : x ≠ y) (h : x ^ y = y ^ x) :
      Real.exp (x + y) < (x ^ x) * (y ^ y) := by
  sorry
```

## 24. Let $S(n)$ be the base-10 digit sum of $n$. Prove that $\displaystyle\sum_{n = 3 \atop S(n) \ge 2}^{\infty} \frac{1}{n \cdot S(n) \cdot ln(S(n))}$ diverges

```lean4
import Mathlib

theorem digit_sum_series_diverges :
    ¬ Summable (fun n : ℕ =>
      if n ≥ 3 ∧ (Nat.digits 10 n).sum ≥ 2 then
      1 / ((n : ℝ) * ((Nat.digits 10 n).sum : ℝ) * Real.log ((Nat.digits 10 n).sum : ℝ))
      else 0) := by
  sorry
```

## 25. Prove that the only positive real solutions to $\displaystyle\sqrt{2(x - 3)\smash{^2} + 4} = \sqrt{\tfrac{12}{x}}$ are $x = 1$ or $2$ or $3$

```lean4
import Mathlib

theorem positive_solutions_sqrt_eq (x : ℝ) (hx : 0 < x) :
    Real.sqrt (2 * (x - 3) ^ 2 + 4) = Real.sqrt (12 / x) ↔ x = 1 ∨ x = 2 ∨ x = 3 := by
  sorry
```

## 26. Prove that if $x$ and $y$ are distinct prime numbers, then $gcd(x^{y - 1} + y^{x - 1}, x \cdot y) = 1$

```lean4
import Mathlib

theorem gcd_prime_pow_sum_eq_one (x y : ℕ) (hx : Nat.Prime x) (hy : Nat.Prime y) (hne : x ≠ y) :
    Nat.gcd (x ^ (y - 1) + y ^ (x - 1)) (x * y) = 1 := by
  sorry
```

## 27. Prove that there is no natural number $n$ such that $29^n + 13n^4 + 5n^3 \equiv 5 \pmod{65}$

```lean4
import Mathlib

theorem no_nat_satisfies_congruence :
    ¬ ∃ n : ℕ, (29 ^ n + 13 * n ^ 4 + 5 * n ^ 3) % 65 = 5 := by
  sorry
```

## 28. Prove that the only non-negative real solution to $\displaystyle\sqrt[3]{19\sqrt{2x + 1} + 34\sqrt{x}} = \sqrt{2x + 1} + \sqrt{x}$ is $x = 4$

```lean4
import Mathlib

theorem unique_real_solution_nested_radical (x : ℝ) (hx : 0 ≤ x) :
    (19 * Real.sqrt (2 * x + 1) + 34 * Real.sqrt x) ^ (1 / 3 : ℝ) =
      Real.sqrt (2 * x + 1) + Real.sqrt x ↔ x = 4 := by
  sorry
```

## 29. Prove that $\displaystyle\sum_{n = -\infty}^{\infty} n \cdot arctan\left(\frac{4n + 2}{4n^4 + 8n^3 + 4n^2 + 1}\right) = \pi$

```lean4
import Mathlib

theorem sum_n_arctan_eq_pi :
    tsum (fun (n : ℤ) => (n : ℝ) * Real.arctan ((4 * (n : ℝ) + 2) /
      (4 * (n : ℝ) ^ 4 + 8 * (n : ℝ) ^ 3 + 4 * (n : ℝ) ^ 2 + 1))) = Real.pi := by
  sorry
```

## 30. Let $S(n)$ be the base-10 digit sum of $n$. Prove that the only positive odd integer solution to $x \cdot S(x) + y \cdot S(y) + z \cdot S(z) = xyz$ is $x = y = z = 3$

```lean4
import Mathlib

theorem odd_digit_sum_eq_xyz_iff (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxo : Odd x) (hyo : Odd y) (hzo : Odd z) :
      x * (Nat.digits 10 x).sum + y * (Nat.digits 10 y).sum + z * (Nat.digits 10 z).sum = x * y * z ↔
      x = 3 ∧ y = 3 ∧ z = 3 := by
  sorry
```

## 31. Prove that for all positive integers $x$, $y$, $z$, $\lvert((x \bmod y) \bmod z) - (x \bmod z)\rvert \le z - gcd(y, z)$

```lean4
import Mathlib

theorem abs_mod_mod_sub_mod_le (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    |((x % y % z : ℤ) - (x % z : ℤ))| ≤ (z : ℤ) - Nat.gcd y z := by
  sorry
```

## 32. Prove that for all real number $x$, $x^4 - 4x^3 + \frac{63}{8}x^2 - 12x + 9 \gt 0$

```lean4
import Mathlib

theorem quartic_pos_x4_4x3 (x : ℝ) : x ^ 4 - 4 * x ^ 3 + (63 / 8 : ℝ) * x ^ 2 - 12 * x + 9 > 0 := by
  sorry
```

## 33. Prove that for all real number $x$, $2x^4 + 5x^3 + 6x^2 + 11x + 10 \gt 0$

```lean4
import Mathlib

theorem quartic_pos_2x4_5x3 (x : ℝ) : 2 * x ^ 4 + 5 * x ^ 3 + 6 * x ^ 2 + 11 * x + 10 > 0 := by
  sorry
```

## 34. Prove that for all real numbers $x$ and $y$, $3x^8 + 2x^4y^4 - 7x^2y^2 + 2y^6 + \frac{5}{3} \gt 0$

```lean4
import Mathlib

theorem polynomial_pos_3x8_2x4 (x y : ℝ) :
    3 * x ^ 8 + 2 * x ^ 4 * y ^ 4 - 7 * x ^ 2 * y ^ 2 + 2 * y ^ 6 + 5 / 3 > 0 := by
  sorry
```

## 35. Let $L(n)$ be the base-10 digit length of $n$. Prove that the only positive integer solution to $n \cdot L(n) \le L(n!)$ is $n = 1$

```lean4
import Mathlib

theorem unique_pos_int_digit_length_ineq (n : ℕ) (hn : 0 < n) :
    n * (Nat.digits 10 n).length ≤ (Nat.digits 10 n.factorial).length ↔ n = 1 := by
  sorry
```

## 36. Prove that there is no non-negative real number $x$ such that $\sqrt{x^2 + x + 1 + 2\sqrt{x^3 + x^2}} = x + \frac{1}{x + 2}$

```lean4
import Mathlib

theorem no_real_solution_nested_radical (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x ^ 2 + x + 1 + 2 * Real.sqrt (x ^ 3 + x ^ 2)) ≠ x + 1 / (x + 2) := by
  sorry
```

## 37. Prove that the only real number solution to $min(x^3 - 2x^2 + 3, x^2 - 1) = max(3^x - 6, 7 - 2^x)$ is $x = 2$

```lean4
import Mathlib

theorem min_poly_eq_max_exp_iff_eq_two (x : ℝ) :
    min (x ^ 3 - 2 * x ^ 2 + 3) (x ^ 2 - 1) = max ((3 : ℝ) ^ x - 6) (7 - (2 : ℝ) ^ x) ↔ x = 2 := by
  sorry
```

## 38. Prove that if $a$, $b$, $c$, $d$, and $e$ are real numbers that sum to $0$ and the sum of their squares is $10$, then $min(|a - b|, |b - c|, |c - d|, |d - e|, |e - a|) \le 2$

```lean4
import Mathlib

theorem min_abs_diff_le_two (a b c d e : ℝ)
    (h_sum : a + b + c + d + e = 0) (h_sq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 10) :
      (min |a - b| (min |b - c| (min |c - d| (min |d - e| |e - a|)))) ≤ 2 := by
  sorry
```

## 39. Prove that there are infinitely many positive integer solutions $n$ to $tan(n\pi x) = 0$ if and only if $x$ is a rational number

```lean4
import Mathlib

theorem infinite_tan_zero_iff_rat (x : ℝ) :
    Set.Infinite { n : ℕ | n > 0 ∧ Real.tan ((n : ℝ) * Real.pi * x) = 0 } ↔ ∃ q : ℚ, x = q := by
  sorry
```

## 40. Prove that for all real numbers $x$, $y$, $z$, $2^x(y^2 + 1) + 2^{-x}(z^2 + 1) + 2(y \cos x + z \sin x) \gt 0$

```lean4
import Mathlib

theorem two_rpow_sq_add_cos_sin_pos (x y z : ℝ) :
    (2 : ℝ) ^ x * (y ^ 2 + 1) + (2 : ℝ) ^ (-x) * (z ^ 2 + 1) + 2 * (y * Real.cos x + z * Real.sin x) > 0 := by
  sorry
```

## 41. Prove that there are no positive integers $x$ and $y$ such that $x! + y! = (x + y + 1)^3 \cdot gcd(x!, y!)$

```lean4
import Mathlib

theorem no_pos_integers_factorial_eq :
    ¬ ∃ (x y : ℕ), 0 < x ∧ 0 < y ∧
      x.factorial + y.factorial = (x + y + 1) ^ 3 * Nat.gcd x.factorial y.factorial := by
  sorry
```

## 42. Prove that for all positive integer $n$, $\frac{Im((2 + i)^{2n})}{Re((1 + 2i)^n)}$ is an integer

```lean4
import Mathlib

theorem im_div_re_is_integer (n : ℕ) (hn : 0 < n) :
    ∃ k : ℤ, (((2 : ℂ) + Complex.I) ^ (2 * n)).im / (((1 : ℂ) + 2 * Complex.I) ^ n).re = (k : ℝ) := by
  sorry
```

## 43. Prove that $cos(100\pi x^2) = 2.01x^2 - 1$ has exactly $198$ unique real solutions

```lean4
import Mathlib

theorem cos_eq_solutions_count :
    Set.ncard { x : ℝ | Real.cos (100 * Real.pi * x ^ 2) = 2.01 * x ^ 2 - 1 } = 198 := by
  sorry
```

## 44. Prove that the only positive real numbers $x$ and $y$ satisfying both $x^{y^x} = y$ and $y^{x^y} = x$ are $x = y = 1$

```lean4
import Mathlib

theorem pos_reals_pow_eq_one (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x ^ (y ^ x) = y ∧ y ^ (x ^ y) = x ↔ x = 1 ∧ y = 1 := by
  sorry
```

## 45. Let $S(n)$ be the base-10 digit sum of $n$. Prove that $\displaystyle\int_{1}^{\infty} \frac{S(\lfloor x^2 \rfloor)}{x^5} \\, dx = \frac{5\pi^2}{132}$

```lean4
import Mathlib

open Real MeasureTheory

theorem integral_digit_sum_floor_sq :
    ∫ x in Set.Ici (1 : ℝ), ((Nat.digits 10 (Nat.floor (x ^ 2))).sum : ℝ) / x ^ 5 = (5 * π ^ 2) / 132 := by
  sorry
```

## 46. Let $S(n)$ be the base-10 digit sum of $n$. Prove that if $x$, $y$, $z$ are positive integers such that $xyz = 10^k$ for some integer $k \ge 1$, and at least one of $x$, $y$, $z$ is not a power of $10$, then $S(x) + S(y) + S(z) \ge 8$

```lean4
import Mathlib

theorem digit_sum_xyz_bounds (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h_prod : ∃ k : ℕ, 1 ≤ k ∧ x * y * z = 10 ^ k)
      (h_not_pow : (¬ ∃ a : ℕ, x = 10 ^ a) ∨ (¬ ∃ b : ℕ, y = 10 ^ b) ∨ (¬ ∃ c : ℕ, z = 10 ^ c)) :
      (Nat.digits 10 x).sum + (Nat.digits 10 y).sum + (Nat.digits 10 z).sum ≥ 8 := by
  sorry
```

## 47. Prove that if $x$ and $y$ are positive integers such that $\displaystyle\sum_{n = 0}^{\infty} \frac{n}{2^n} \cdot \left\lfloor\frac{ny}{x}\right\rfloor = \frac{6y}{x}$, then $x \mid y$

```lean4
import Mathlib

theorem sum_floor_div_eq_implies_dvd (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : ∑' (n : ℕ), ((n : ℝ) / (2 : ℝ) ^ n) * (Int.floor ((n : ℝ) * (y : ℝ) / (x : ℝ)) : ℝ) = 6 * (y : ℝ) / (x : ℝ)) :
      x ∣ y := by
  sorry
```

## 48. Prove that if $x$ and $y$ are positive integers such that $x^2 + 3y^2 - 17$ and $\frac{x^5 + y^5}{x + y}$ are prime, then both $x$ and $y$ must be odd

```lean4
import Mathlib

theorem odd_of_prime_quadratic_and_quintic (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h1 : Nat.Prime (x ^ 2 + 3 * y ^ 2 - 17))
      (h2 : Nat.Prime ((x ^ 5 + y ^ 5) / (x + y))) :
      Odd x ∧ Odd y := by
  sorry
```

## 49. Prove that if $x$ and $y$ are positive integers such that $2x^2 + xy + y^2 = 7(x - y)^4$, then neither $x$ nor $y$ is prime

```lean4
import Mathlib

theorem neither_x_nor_y_prime (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : 2 * (x : ℤ) ^ 2 + (x : ℤ) * (y : ℤ) + (y : ℤ) ^ 2 = 7 * ((x : ℤ) - (y : ℤ)) ^ 4) :
      ¬ Nat.Prime x ∧ ¬ Nat.Prime y := by
  sorry
```

## 50. Prove that there exists a primitive set $S$ of arbitrarily large cardinality such that $\vert S_{odd} \vert = \vert S_{even} \vert$ and $\displaystyle\sum_{o \in S_{odd}} o = \sum_{e \in S_{even}} e$

```lean4
import Mathlib

theorem primitive_set_arbitrarily_large :
    ∀ n : ℕ, ∃ S : Finset ℕ, S.Nonempty ∧
      (∀ a ∈ S, ∀ b ∈ S, a ∣ b → a = b) ∧
      (S.filter Odd).card = (S.filter Even).card ∧
      (S.filter Odd).sum id = (S.filter Even).sum id ∧
      S.card ≥ n := by
  sorry
```

## 51. Prove that there are no positive integers $x$ and $y$ such that $x^2 + 4xy + 2y^2 \equiv 5 \cdot 2^x \pmod{2^{2x + 3}}$

```lean4
import Mathlib

theorem not_exists_pos_sol_quad_modeq_pow :
    ¬ ∃ (x y : ℕ), 0 < x ∧ 0 < y ∧ (x ^ 2 + 4 * x * y + 2 * y ^ 2 ≡ 5 * 2 ^ x [MOD 2 ^ (2 * x + 3)]) := by
  sorry
```

## 52. Let $a$ and $b$ be positive integers such that $a + b = 2026$. Prove that there are exactly $1011$ permutations $(a, b)$ for which the equation $\ln(x^3 + a) = \ln(x^b - 3a)$ has a unique real solution $x$

```lean4
import Mathlib

theorem permutations_a_b_log_eq_unique_sol_count :
    Nat.card { p : ℕ × ℕ |
      let a := p.1
      let b := p.2
      0 < a ∧ 0 < b ∧ a + b = 2026 ∧
      ∃! x : ℝ, 0 < x ^ 3 + (a : ℝ) ∧ 0 < x ^ b - 3 * (a : ℝ) ∧
      Real.log (x ^ 3 + (a : ℝ)) = Real.log (x ^ b - 3 * (a : ℝ)) } = 1011 := by
  sorry
```

## 53. Prove that the equation $x^{20} - 7x^{11} + 10x^{10} - 5x + 4 = 0$ has no real solutions

```lean4
import Mathlib

theorem no_real_solutions_x20_7x11 (x : ℝ) :
    x ^ 20 - 7 * x ^ 11 + 10 * x ^ 10 - 5 * x + 4 ≠ 0 := by
  sorry
```

## 54. Prove that the equation $x^{10}y^2 + x^2y^8 + x^6 + y^6 - 3x^4y^3 - 2x^2y + 3 = 0$ has no real solutions

```lean4
import Mathlib

theorem no_real_solutions_x10y2_x2y8 (x y : ℝ) :
    x ^ 10 * y ^ 2 + x ^ 2 * y ^ 8 + x ^ 6 + y ^ 6 - 3 * x ^ 4 * y ^ 3 - 2 * x ^ 2 * y + 3 ≠ 0 := by
  sorry
```

## 55. Prove that for all real numbers $x$ and $y$, $sgn(x + y) + sgn(x - y) = sgn(\sin(x) + x) \cdot (1 + sgn(x^4 - y^4))$

```lean4
import Mathlib

theorem sgn_add_sub_eq (x y : ℝ) :
    Real.sign (x + y) + Real.sign (x - y) =
      Real.sign (Real.sin x + x) * (1 + Real.sign (x ^ 4 - y ^ 4)) := by
  sorry
```

## 56. Let $S(n)$ be the base-10 digit sum of $n$. Prove that if $n$ is a positive integer such that $n^2 + S(n)^2 \mid n^4 + S(n)^4$, then $S(n) \mid n$

```lean4
import Mathlib

theorem digit_sum_divides (n : ℕ) (hn : 0 < n)
    (h : n ^ 2 + (Nat.digits 10 n).sum ^ 2 ∣ n ^ 4 + (Nat.digits 10 n).sum ^ 4) :
      (Nat.digits 10 n).sum ∣ n := by
  sorry
```

## 57. Let $f(x) = \lvert\lvert x \rvert - 3 \rvert + \lvert x \rvert$. Prove that the only real solution to equation $f^{2026}(x) = 3 - x^2$ is $x = 0$

```lean4
import Mathlib

def f (x : ℝ) : ℝ := |abs x - 3| + |x|

theorem unique_solution_f_iterate (x : ℝ) :
    f^[2026] x = 3 - x ^ 2 ↔ x = 0 := by
  sorry
```

## 58. Let $L(n)$ be the base-10 digit length of $n$. Prove that there is no integer $n \gt 1$ such that $\displaystyle\frac{1}{n} \sum_{k = 1}^{n} L(k) = L(n) - \frac{1}{\sqrt[4]{n} - 1}$

```lean4
import Mathlib

open BigOperators

theorem no_pos_int_satisfies_digit_sum_eq :
    ¬ ∃ (n : ℕ), 1 < n ∧
      (1 / (n : ℝ)) * (∑ k ∈ Finset.Icc 1 n, ((Nat.digits 10 k).length : ℝ)) =
      ((Nat.digits 10 n).length : ℝ) - 1 / ((n : ℝ) ^ (1 / 4 : ℝ) - 1) := by
  sorry
```

## 59. Prove that the only positive integer satisfying $3^n \mid 2^{3^{4^n}} - 11$ is $n = 1$

```lean4
import Mathlib

theorem unique_solution_pow_tower_div (n : ℕ) (hn : 0 < n) :
    3 ^ n ∣ 2 ^ (3 ^ (4 ^ n)) - 11 ↔ n = 1 := by
  sorry
```

## 60. Prove that the only positive integer solutions to $\frac{(n!)!}{(n^2 - 1)!} \lt n^{n! + n^3}$ are $n = 2$, $3$, and $4$

```lean4
import Mathlib

theorem factorial_inequality (n : ℕ) (hn : 0 < n) :
    ((n.factorial.factorial : ℝ) / ((n ^ 2 - 1).factorial : ℝ) < (n : ℝ) ^ (n.factorial + n ^ 3)) ↔
      n = 2 ∨ n = 3 ∨ n = 4 := by
  sorry
```

## 61. Let $\\{x\\}$ be the fractional part of $x$. Prove that there are exactly $2$ non-zero real solutions to $\left\\{x\left\\{\frac{1}{x}\left\\{x\left\\{\frac{2}{x}\right\\}\right\\}\right\\}\right\\} + x^3 = 0$

```lean4
import Mathlib

theorem fractional_part_equation_two_solutions :
    Set.ncard { x : ℝ | x ≠ 0 ∧ Int.fract (x * Int.fract ((1 / x) *
      Int.fract (x * Int.fract (2 / x)))) + x ^ 3 = 0 } = 2 := by
  sorry
```

## 62. Let $P(n)$ be the base-10 digit product of $n$. Prove that there is no positive integer $n$ such that $\frac{P(n + 3)}{P(n + 5) - 6} = n^2$

```lean4
import Mathlib

theorem no_pos_int_digit_prod_eq :
    ¬ ∃ n : ℕ, 0 < n ∧ ((Nat.digits 10 (n + 3)).prod : ℝ) /
      (((Nat.digits 10 (n + 5)).prod : ℝ) - 6) = (n : ℝ) ^ 2 := by
  sorry
```

## 63. Let $x$ and $y$ be distinct positive integers. Prove that $\frac{3x + \sqrt[3]{y^5}}{\sqrt[7]{x^2} - y^6}$ is rational if and only if $x$ is a perfect 7th power and $y$ is a perfect cube

```lean4
import Mathlib

theorem rational_expr_iff_perfect_powers (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) (hne : (x : ℝ) ^ ((2 : ℝ) / 7) ≠ (y : ℝ) ^ 6) :
      (∃ q : ℚ, (3 * (x : ℝ) + (y : ℝ) ^ ((5 : ℝ) / 3)) /
      ((x : ℝ) ^ ((2 : ℝ) / 7) - (y : ℝ) ^ 6) = (q : ℝ)) ↔
      (∃ a : ℕ, a ^ 7 = x) ∧ (∃ b : ℕ, b ^ 3 = y) := by
  sorry
```

## 64. Prove that there exist arbitrarily long sequences of consecutive natural numbers with the same additive persistence

```lean4
import Mathlib

def additivePersistence (n : ℕ) : ℕ :=
  if n < 10 then 0
  else 1 + additivePersistence (Nat.digits 10 n).sum
termination_by n
decreasing_by sorry

theorem arbitrary_consecutive_same_additive_persistence (k : ℕ) :
    ∃ n : ℕ, ∀ i < k, additivePersistence (n + i) = additivePersistence n := by
  sorry
```

## 65. Prove that $\displaystyle\sum_{n = 1}^{\infty} \frac{\lceil 3 \pi n \rceil}{5^{n!} - 1}$ is transcendental

```lean4
import Mathlib

theorem transcendental_sum_ceil_pi :
    Transcendental ℚ (∑' (n : ℕ+), (⌈3 * Real.pi * (n : ℝ)⌉ : ℝ) / ((5 : ℝ) ^ (n : ℕ).factorial - 1)) := by
  sorry
```

## 66. Let $x$ and $y$ be real numbers such that $e \le x$, $e \le y$, and $y^x \le x^y$. Prove that $\left(\frac{x}{y}\right)^{(x - y)(\ln x - \ln y)} \le \frac{x^x + y^y}{x^y + y^x}$

```lean4
import Mathlib

theorem rpow_sub_mul_log_sub_le_div_add_rpow (x y : ℝ)
    (hx : Real.exp 1 ≤ x) (hy : Real.exp 1 ≤ y) (hxy : y ^ x ≤ x ^ y) :
      (x / y) ^ ((x - y) * (Real.log x - Real.log y)) ≤
      (x ^ x + y ^ y) / (x ^ y + y ^ x) := by
  sorry
```

## 67. Prove that the last five digits of $^{951}7$ is $72343$

```lean4
import Mathlib

def tetrate (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => a ^ (tetrate a n)

theorem last_five_digits_tetrate_seven_951 :
    tetrate 7 951 % 100000 = 72343 := by
  sorry
```

## 68. Let $S(n)$ denote the integer obtained by sorting the base-10 digits of $n$ in descending order. Prove that there are infinitely many positive integers $n$ such that $S(n) = 2n$

```lean4
import Mathlib

def S (n : ℕ) : ℕ :=
  Nat.ofDigits 10 ((Nat.digits 10 n).mergeSort (· ≤ ·))

theorem infinite_solutions_s_eq_two_n :
    Set.Infinite { n : ℕ | 0 < n ∧ S n = 2 * n } := by
  sorry
```

## 69. Prove that there does not exist an integer $n \gt 1$ whose largest prime factor $P$ satisfies $P^2 = n - gcd(n, P - 5)$

```lean4
import Mathlib

theorem no_int_sol_prime_factor_gcd :
    ¬ ∃ (n : ℕ) (P : ℕ), 1 < n ∧ Nat.Prime P ∧ P ∣ n ∧
      (∀ q : ℕ, Nat.Prime q → q ∣ n → q ≤ P) ∧
      (P : ℤ) ^ 2 = (n : ℤ) - (Int.gcd (n : ℤ) ((P : ℤ) - 5) : ℤ) := by
  sorry
```

## 70. Prove that $\displaystyle\int_{0}^{\pi} x \cdot sgn(\sin(3x)) \cdot sgn(\sin(11x^2)) \\, dx = \frac{5 \pi^2}{6} - \frac{29 \pi}{11}$

```lean4
import Mathlib

theorem integral_sgn_sin :
    ∫ x in (0)..Real.pi,
      x * Real.sign (Real.sin (3 * x)) * Real.sign (Real.sin (11 * x ^ 2)) =
      (5 * Real.pi ^ 2) / 6 - (29 * Real.pi) / 11 := by
  sorry
```

## 71. Let $R(n, d)$ be the base-10 repdigit with digit $d$ repeated $n$ times, and let $S(n)$ be the base-10 digit sum of $n$. Prove that $S((\sqrt{R(3334, 4) - R(1667, 8)} - 5)^3) = 24994$

```lean4
import Mathlib

def R (n d : ℕ) : ℕ := d * ((10 ^ n - 1) / 9)

def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum

theorem digit_sum_rep_digits_expr :
    S ((Nat.sqrt (R 3334 4 - R 1667 8) - 5) ^ 3) = 24994 := by
  sorry
```

## 72. Let $R(n, d)$ be the base-10 repdigit with digit $d$ repeated $n$ times. Prove that the only positive integer solution to $R(n, 3)^2 - R(n, 2) = R(n, 7)$ is $n = 1$

```lean4
import Mathlib

def R (n d : ℕ) : ℕ := d * ((10 ^ n - 1) / 9)

theorem repdigit_unique_sol_n_one (n : ℕ) (hn : 0 < n) :
    R n 3 ^ 2 - R n 2 = R n 7 ↔ n = 1 := by
  sorry
```

## 73. Prove that for any positive integer $n$, the base-10 representation of $\displaystyle\prod_{k = 1}^{n} (^{k}10 - 1)$ does not contain the digit $2$

```lean4
import Mathlib

def tetrate (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => a ^ (tetrate a n)

theorem product_tetrate_sub_one_no_digit_two (n : ℕ) (hn : 0 < n) :
    2 ∉ Nat.digits 10 (∏ k ∈ Finset.Icc 1 n, (tetrate 10 k - 1)) := by
  sorry
```

## 74. Let $a_1 = 11$ and $a_n = 10^{a_{n - 1}}$. Prove that the first five digits of $(10^{a_6} - 3)^{a_7}$ is $49787$

```lean4
import Mathlib

def a : ℕ → ℕ
  | 0 => 0
  | 1 => 11
  | n + 2 => 10 ^ a (n + 1)

theorem first_five_digits_of_pow :
    ((Nat.digits 10 ((10 ^ a 6 - 3) ^ a 7)).reverse.take 5) = [4, 9, 7, 8, 7] := by
  sorry
```

## 75. Let $n$ be a 10-digit positive integer with no zero digits. Prove that if $n$ has exactly $m$ distinct digits and the median of its digits is $m$, then $m \le 7$

```lean4
import Mathlib

theorem ten_digit_median_distinct_digits_le_seven
    (n m : ℕ) (h_digits_len : (Nat.digits 10 n).length = 10)
      (h_no_zero : 0 ∉ Nat.digits 10 n)
      (h_median :
        let s := (Nat.digits 10 n).mergeSort (· ≤ ·)
        s[4]! + s[5]! = 2 * m)
      (h_distinct : (Nat.digits 10 n).toFinset.card = m) : m ≤ 7 := by
  sorry
```

## 76. Prove that there are infinitely many positive integers $n$ such that the digit $7$ is the unique modal digit in the base-10 representation of both $(n - 4)^2$ and $n^3 + 12$

```lean4
import Mathlib

theorem infinite_positive_integers_mode_digit_seven :
    Set.Infinite { n : ℕ | 0 < n ∧
      (∀ d : ℕ, d ≠ 7 → (Nat.digits 10 ((n - 4) ^ 2)).count d <
      (Nat.digits 10 ((n - 4) ^ 2)).count 7) ∧
      (∀ d : ℕ, d ≠ 7 → (Nat.digits 10 (n ^ 3 + 12)).count d <
      (Nat.digits 10 (n ^ 3 + 12)).count 7) } := by
  sorry
```

## 77. Let $sumValidIntegers(l, s)$ be the sum of all positive integers with at most $l$ base-10 digits whose base-10 digit sum is less than or equal to $s$. Prove that if $sumValidIntegers(l, s) \gt 10^{12}$, then the tight lower bound of $s + l$ is $14$

```lean4
import Mathlib

def sumValidIntegers (l s : ℕ) : ℕ :=
  ∑ n ∈ (Finset.Ico 1 (10 ^ l)).filter (fun n => (Nat.digits 10 n).sum ≤ s), n

theorem tight_lower_bound_s_add_l :
    (∀ l s : ℕ, sumValidIntegers l s > 10 ^ 12 → s + l ≥ 14) ∧
      (∃ l s : ℕ, sumValidIntegers l s > 10 ^ 12 ∧ s + l = 14) := by
  sorry
```

## 78. Let $\frac{311}{457} = \frac{1}{n_1} + \frac{1}{n_2} + \cdots + \frac{1}{n_k}$ be an Egyptian fraction decomposition, where $n_1, n_2, \ldots, n_k$ are positive integers satisfying $2 \le n_1 \lt n_2 \lt \cdots \lt n_k$. Prove that the tight lower bound for the largest denominator $n_k$ is $3199$

```lean4
import Mathlib

def IsEgyptianFractionDecomp (q : ℚ) (l : List ℕ) : Prop :=
  l.Pairwise (· < ·) ∧ (∀ x ∈ l, 2 ≤ x) ∧ (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = q

theorem egyptian_fraction_311_457_tight_lower_bound :
    (∀ l : List ℕ, IsEgyptianFractionDecomp (311 / 457) l → ∃ n ∈ l, 3199 ≤ n) ∧
      (∃ l : List ℕ, IsEgyptianFractionDecomp (311 / 457) l ∧ ∀ n ∈ l, n ≤ 3199) := by
  sorry
```

## 79. Prove that the only real solution to equation $\left\lfloor x \left\lfloor x \right\rfloor\right\rfloor - \left\lceil x \left\lceil x \right\rceil\right\rceil^3 = x^4 - 31$ is $x = \sqrt[4]{5}$

```lean4
import Mathlib

theorem floor_ceil_eq_fourth_root (x : ℝ) :
    (⌊x * ⌊x⌋⌋ : ℝ) - (⌈x * ⌈x⌉⌉ : ℝ) ^ 3 = x ^ 4 - 31 ↔ x = (5 : ℝ) ^ ((1 : ℝ) / 4) := by
  sorry
```

## 80. Prove that the only positive integer solution to equation $\frac{(x + y - 1)! + 1}{x + y} + 59 = (x!)^{y + 3}$ is $x = 2$ and $y = 3$

```lean4
import Mathlib

theorem factorial_add_one_div_eq_iff_x_two_y_three
    (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
      ((x + y - 1).factorial + 1 : ℚ) / (x + y : ℚ) + 59 =
      (x.factorial : ℚ) ^ (y + 3) ↔ x = 2 ∧ y = 3 := by
  sorry
```

## 81. Let $O(n)$ and $E(n)$ denote the number of odd and even digits in the base-10 representation of $n$, respectively. Proof that the smallest positive integer $n$ that satisfies both $(O(n^2 + n))^2 = 3 \cdot O(n)$ and $E(n^2 - n) = 5 \cdot E(n)$ is $1059$

```lean4
import Mathlib

def O (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).filter (· % 2 == 1)).length

def E (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).filter (· % 2 == 0)).length

theorem is_least_pos_int_odd_even_digit_count_eq_1059 :
    IsLeast { n : ℕ | 0 < n ∧ (O (n ^ 2 + n)) ^ 2 =
      3 * O n ∧ E (n ^ 2 - n) = 5 * E n } 1059 := by
  sorry
```

## 82. Let $\\{x\\}$ be the fractional part of $x$. Prove that $\displaystyle\prod_{n = 1}^{\infty} \frac{1 + 2\cos\left(\pi\left\\{\frac{25}{2 \cdot 3^n} - \left\\{\frac{16}{2 \cdot 3^n}\right\\}\right\\}\right)}{3} = \frac{2 \sqrt 2}{9 \pi}$

```lean4
import Mathlib

theorem infinite_product_cos_fract :
    Filter.Tendsto (fun N => ∏ n ∈ Finset.Icc 1 N,
      (1 + 2 * Real.cos (Real.pi * Int.fract (25 / (2 * (3 : ℝ) ^ n) -
      Int.fract (16 / (2 * (3 : ℝ) ^ n))))) / 3)
      Filter.atTop (nhds ((2 * Real.sqrt 2) / (9 * Real.pi))) := by
  sorry
```

## 83. Let $S(n)$ be the base-10 digit sum of $n$ and let $a$ and $b$ be 6-digit triangular numbers. Prove that if $b - a = 13761$ and $S(ab) = 54$, then $b$ must be equal to $299151$

```lean4
import Mathlib

theorem six_digit_triangular_digit_sum (a b : ℕ)
    (ha_digits : 10 ^ 5 ≤ a ∧ a < 10 ^ 6) (hb_digits : 10 ^ 5 ≤ b ∧ b < 10 ^ 6)
      (ha_tri : ∃ k : ℕ, a = k * (k + 1) / 2) (hb_tri : ∃ k : ℕ, b = k * (k + 1) / 2)
      (h_diff : b - a = 13761) (h_sum : (Nat.digits 10 (a * b)).sum = 54) :
      b = 299151 := by
  sorry
```

## 84. Let $\\{x\\}$ be the fractional part of $x$. Prove that the only real solution that satisfies both $\lceil 3 \lfloor x \rfloor y^2 \rceil + \lfloor y \lfloor x^4 \rfloor \rfloor^2 = 5$ and $\\{x\\} - 3y^2 = 5k + 1$ for some integer $k$, is $x = 1$ and $y = \frac{2}{\sqrt{3}}$

```lean4
import Mathlib

theorem floor_ceil_fract_system_unique_solution (x y : ℝ) :
    (Int.ceil (3 * (Int.floor x : ℝ) * y ^ 2) +
      (Int.floor (y * (Int.floor (x ^ 4) : ℝ))) ^ 2 = 5 ∧
      ∃ k : ℤ, Int.fract x - 3 * y ^ 2 = 5 * (k : ℝ) + 1) ↔
      (x = 1 ∧ y = 2 / Real.sqrt 3) := by
  sorry
```

## 85. Let curve $C$ be defined by $xy^{13} - 4y = x^{5x} - 3x - 1$, for $x \gt 0$. Proof that the tight upper bound on the number of intersections between $C$ and any vertical line is $3$

```lean4
import Mathlib

def C : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | p.1 > 0 ∧ p.1 * p.2 ^ 13 - 4 * p.2 = p.1 ^ (5 * p.1) - 3 * p.1 - 1 }

def verticalLine (x₀ : ℝ) : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | p.1 = x₀ }

theorem max_vertical_intersections_xy13_4y :
    (∀ x₀ : ℝ, Set.encard (C ∩ verticalLine x₀) ≤ 3) ∧
      (∃ x₀ : ℝ, Set.encard (C ∩ verticalLine x₀) = 3) := by
  sorry
```

## 86. Prove that there is no upper bound on the number of intersections between the curve $3y^2 = \sin(9xy) + \frac{x}{\pi} - 7y$ and a circle of arbitrary position and size

```lean4
import Mathlib

def curve : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | 3 * p.2 ^ 2 = Real.sin (9 * p.1 * p.2) + p.1 / Real.pi - 7 * p.2 }

def circle (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 = r ^ 2 }

theorem curve_circle_intersections_not_bounded_above :
    ¬ ∃ N : ℕ, ∀ (c : ℝ × ℝ) (r : ℝ), r > 0 → (circle c r ∩ curve).encard ≤ N := by
  sorry
```

## 87. Prove that $\displaystyle\sum_{m = 1}^{\infty}\sum_{n = 1}^{\infty} \frac{sgn(2m - n - 5) + (-1)^{min(m, n) + 3}}{(max(m, n) + 1)!} = \frac{1249}{120} - 4e$

```lean4
import Mathlib

theorem double_infinite_sum_sgn_factorial_eq :
    (∑' (m : ℕ+) (n : ℕ+),
      ((Int.sign (2 * (m : ℤ) - (n : ℤ) - 5) : ℝ) + (-1 : ℝ) ^ ((min (m : ℕ) (n : ℕ)) + 3)) /
      (Nat.factorial ((max (m : ℕ) (n : ℕ)) + 1) : ℝ)) =
      (1249 : ℝ) / 120 - 4 * Real.exp 1 := by
  sorry
```
