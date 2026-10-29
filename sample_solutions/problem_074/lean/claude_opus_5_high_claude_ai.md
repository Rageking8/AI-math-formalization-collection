# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `22 August 2026`\
Line count: `264`\
Turn count: `4`

## Solution

```lean4
import Mathlib

set_option maxRecDepth 10000

def a : ℕ → ℕ
  | 0 => 0
  | 1 => 11
  | n + 2 => 10 ^ a (n + 1)

-- ## Small analytic helpers

private lemma exp_pow_eq (y : ℝ) (n : ℕ) : Real.exp y ^ n = Real.exp (n * y) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

private lemma pow_le_pow_of_le' (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    x ^ n ≤ y ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hy : (0:ℝ) ≤ y := le_trans hx hxy
      have h2 : (0:ℝ) ≤ x ^ k := pow_nonneg hx k
      have s1 := mul_le_mul_of_nonneg_left ih hy
      have s2 := mul_le_mul_of_nonneg_right hxy h2
      rw [pow_succ, pow_succ]
      nlinarith [s1, s2]

private lemma exp3_le : Real.exp 3 ≤ 20.0855370 := by
  have h : Real.exp 3 = Real.exp 1 ^ (3:ℕ) := by
    rw [show (3:ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]; ring
  rw [h]
  have h1 : Real.exp 1 ^ (3:ℕ) ≤ (2.7182818286:ℝ) ^ (3:ℕ) :=
    pow_le_pow_of_le' _ _ (Real.exp_pos 1).le (le_of_lt Real.exp_one_lt_d9) 3
  have h2 : (2.7182818286:ℝ) ^ (3:ℕ) ≤ 20.0855370 := by norm_num
  linarith

private lemma exp3_ge : (20.0855368:ℝ) ≤ Real.exp 3 := by
  have h : Real.exp 3 = Real.exp 1 ^ (3:ℕ) := by
    rw [show (3:ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]; ring
  rw [h]
  have h1 : (2.7182818283:ℝ) ^ (3:ℕ) ≤ Real.exp 1 ^ (3:ℕ) :=
    pow_le_pow_of_le' _ _ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 3
  have h2 : (20.0855368:ℝ) ≤ (2.7182818283:ℝ) ^ (3:ℕ) := by norm_num
  linarith

-- ## The core estimate

private lemma key (M : ℕ) (hM : (100000000000:ℕ) ≤ M) :
    49787 * M ^ M ≤ 10 ^ 6 * (M - 3) ^ M ∧ 10 ^ 6 * (M - 3) ^ M < 49788 * M ^ M := by
  have h3M : 3 ≤ M := by omega
  have hx : (100000000000:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hx0 : (0:ℝ) < (M:ℝ) := by linarith
  have hne : (M:ℝ) ≠ 0 := ne_of_gt hx0
  have hs : (0:ℝ) < (M:ℝ) - 3 := by linarith
  have hne3 : (M:ℝ) - 3 ≠ 0 := ne_of_gt hs
  have hcast : ((M - 3 : ℕ) : ℝ) = (M:ℝ) - 3 := by rw [Nat.cast_sub h3M]; norm_num
  have hMM0 : (0:ℝ) < (M:ℝ) ^ M := by positivity
  -- (M-3)^M ≤ M^M e^{-3}
  have hUB : ((M:ℝ) - 3) ^ M ≤ (M:ℝ) ^ M * Real.exp (-3) := by
    have h := Real.add_one_le_exp (-3 / (M:ℝ))
    have h2 := mul_le_mul_of_nonneg_left h hx0.le
    have hxe : (M:ℝ) * (-3 / (M:ℝ) + 1) = (M:ℝ) - 3 := by field_simp <;> ring
    rw [hxe] at h2
    have h5 : (M:ℝ) * (-3 / (M:ℝ)) = -3 := by field_simp <;> ring
    calc ((M:ℝ) - 3) ^ M ≤ ((M:ℝ) * Real.exp (-3 / (M:ℝ))) ^ M :=
          pow_le_pow_of_le' _ _ (by linarith) h2 M
      _ = (M:ℝ) ^ M * Real.exp (-3) := by rw [mul_pow, exp_pow_eq, h5]
  -- M^M e^{-3M/(M-3)} ≤ (M-3)^M
  have hLB : (M:ℝ) ^ M * Real.exp (-(3 * (M:ℝ) / ((M:ℝ) - 3))) ≤ ((M:ℝ) - 3) ^ M := by
    have h := Real.add_one_le_exp (3 / ((M:ℝ) - 3))
    have h2 := mul_le_mul_of_nonneg_left h hs.le
    have he : ((M:ℝ) - 3) * (3 / ((M:ℝ) - 3) + 1) = (M:ℝ) := by field_simp <;> ring
    rw [he] at h2
    have h4 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-(3 / ((M:ℝ) - 3)))).le
    have hz : 3 / ((M:ℝ) - 3) + -(3 / ((M:ℝ) - 3)) = 0 := by ring
    rw [mul_assoc, ← Real.exp_add, hz, Real.exp_zero, mul_one] at h4
    have h6 : (M:ℝ) * -(3 / ((M:ℝ) - 3)) = -(3 * (M:ℝ) / ((M:ℝ) - 3)) := by
      field_simp <;> ring
    calc (M:ℝ) ^ M * Real.exp (-(3 * (M:ℝ) / ((M:ℝ) - 3)))
        = ((M:ℝ) * Real.exp (-(3 / ((M:ℝ) - 3)))) ^ M := by
          rw [mul_pow, exp_pow_eq, h6]
      _ ≤ ((M:ℝ) - 3) ^ M := pow_le_pow_of_le' _ _ (by positivity) h4 M
  -- numeric bounds
  have hu : 3 * (M:ℝ) / ((M:ℝ) - 3) = 3 + 9 / ((M:ℝ) - 3) := by field_simp <;> ring
  have hueq : (9 / ((M:ℝ) - 3)) * ((M:ℝ) - 3) = 9 := by field_simp
  have hu0 : (0:ℝ) ≤ 9 / ((M:ℝ) - 3) := by positivity
  have hbig : (99999999997:ℝ) ≤ (M:ℝ) - 3 := by linarith
  have hmul : (9 / ((M:ℝ) - 3)) * 99999999997 ≤ 9 := by
    have hstep := mul_le_mul_of_nonneg_left hbig hu0
    linarith [hueq]
  have ht : 9 / ((M:ℝ) - 3) ≤ 1 / 10 ^ 10 := by
    have hnum : (1:ℝ) / 10 ^ 10 = 1 / 10000000000 := by norm_num
    rw [hnum]
    linarith
  have hexpt : Real.exp (9 / ((M:ℝ) - 3)) ≤ 1 + 1 / 10 ^ 9 := by
    have h1 : (1:ℝ) - 1 / 10 ^ 10 ≤ Real.exp (-(9 / ((M:ℝ) - 3))) := by
      have h := Real.add_one_le_exp (-(9 / ((M:ℝ) - 3))); linarith
    have hz : 9 / ((M:ℝ) - 3) + -(9 / ((M:ℝ) - 3)) = 0 := by ring
    have h2 : Real.exp (9 / ((M:ℝ) - 3)) * Real.exp (-(9 / ((M:ℝ) - 3))) = 1 := by
      rw [← Real.exp_add, hz, Real.exp_zero]
    have h3 : Real.exp (9 / ((M:ℝ) - 3)) * (1 - 1 / 10 ^ 10) ≤ 1 := by
      calc Real.exp (9 / ((M:ℝ) - 3)) * (1 - 1 / 10 ^ 10)
          ≤ Real.exp (9 / ((M:ℝ) - 3)) * Real.exp (-(9 / ((M:ℝ) - 3))) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := h2
    linarith
  have hexpu : Real.exp (3 * (M:ℝ) / ((M:ℝ) - 3)) ≤ 20.0855370 * (1 + 1 / 10 ^ 9) := by
    rw [hu, Real.exp_add]
    exact mul_le_mul exp3_le hexpt (Real.exp_pos _).le (by norm_num)
  have hfin1 : 49787 * Real.exp (3 * (M:ℝ) / ((M:ℝ) - 3)) ≤ 10 ^ 6 := by
    have hnum : (49787:ℝ) * (20.0855370 * (1 + 1 / 10 ^ 9)) ≤ 10 ^ 6 := by norm_num
    linarith [hexpu]
  have hfin2 : (49787:ℝ) ≤ 10 ^ 6 * Real.exp (-(3 * (M:ℝ) / ((M:ℝ) - 3))) := by
    have hz : 3 * (M:ℝ) / ((M:ℝ) - 3) + -(3 * (M:ℝ) / ((M:ℝ) - 3)) = 0 := by ring
    have h2 : Real.exp (3 * (M:ℝ) / ((M:ℝ) - 3)) *
        Real.exp (-(3 * (M:ℝ) / ((M:ℝ) - 3))) = 1 := by
      rw [← Real.exp_add, hz, Real.exp_zero]
    have h3 := mul_le_mul_of_nonneg_right hfin1
      (Real.exp_pos (-(3 * (M:ℝ) / ((M:ℝ) - 3)))).le
    rw [mul_assoc, h2, mul_one] at h3
    exact h3
  have hexpneg3 : (10:ℝ) ^ 6 * Real.exp (-3) < 49788 := by
    have h1 : (10:ℝ) ^ 6 < 49788 * Real.exp 3 := by linarith [exp3_ge]
    have hz : (3:ℝ) + -3 = 0 := by ring
    have h2 : Real.exp 3 * Real.exp (-3) = 1 := by
      rw [← Real.exp_add, hz, Real.exp_zero]
    have h3 := mul_lt_mul_of_pos_right h1 (Real.exp_pos (-3))
    rw [mul_assoc, h2, mul_one] at h3
    exact h3
  -- conclude
  have hAreal : (49787:ℝ) * (M:ℝ) ^ M ≤ 10 ^ 6 * ((M:ℝ) - 3) ^ M := by
    calc (49787:ℝ) * (M:ℝ) ^ M
        ≤ (10 ^ 6 * Real.exp (-(3 * (M:ℝ) / ((M:ℝ) - 3)))) * (M:ℝ) ^ M :=
          mul_le_mul_of_nonneg_right hfin2 hMM0.le
      _ = 10 ^ 6 * ((M:ℝ) ^ M * Real.exp (-(3 * (M:ℝ) / ((M:ℝ) - 3)))) := by ring
      _ ≤ 10 ^ 6 * ((M:ℝ) - 3) ^ M := by linarith [hLB]
  have hBreal : (10:ℝ) ^ 6 * ((M:ℝ) - 3) ^ M < 49788 * (M:ℝ) ^ M := by
    calc (10:ℝ) ^ 6 * ((M:ℝ) - 3) ^ M ≤ 10 ^ 6 * ((M:ℝ) ^ M * Real.exp (-3)) := by
          linarith [hUB]
      _ = (M:ℝ) ^ M * (10 ^ 6 * Real.exp (-3)) := by ring
      _ < (M:ℝ) ^ M * 49788 := mul_lt_mul_of_pos_left hexpneg3 hMM0
      _ = 49788 * (M:ℝ) ^ M := by ring
  constructor
  · have hh : (49787:ℝ) * (M:ℝ) ^ M ≤ 10 ^ 6 * (((M - 3 : ℕ)):ℝ) ^ M := by
      rw [hcast]; exact hAreal
    exact_mod_cast hh
  · have hh : (10:ℝ) ^ 6 * (((M - 3 : ℕ)):ℝ) ^ M < 49788 * (M:ℝ) ^ M := by
      rw [hcast]; exact hBreal
    exact_mod_cast hh

-- ## Reading off the leading digits

private lemma digits_split (q : ℕ) (hq : q ≠ 0) :
    ∀ (k r : ℕ), r < 10 ^ k →
      ∃ L : List ℕ, L.length = k ∧ Nat.digits 10 (q * 10 ^ k + r) = L ++ Nat.digits 10 q := by
  intro k
  induction k with
  | zero =>
      intro r hr
      have hr0 : r = 0 := by simpa using hr
      subst hr0
      exact ⟨[], rfl, by simp⟩
  | succ k ih =>
      intro r hr
      have h10 : (0:ℕ) < 10 := by norm_num
      have hr' : r < 10 * 10 ^ k := by
        have e : (10:ℕ) ^ (k + 1) = 10 * 10 ^ k := by ring
        omega
      obtain ⟨L, hL, hLd⟩ := ih (r / 10) (Nat.div_lt_of_lt_mul hr')
      have hq0 : 0 < q := Nat.pos_of_ne_zero hq
      have hpow : (0:ℕ) < 10 ^ (k + 1) := by positivity
      have hpos : 0 < q * 10 ^ (k + 1) + r := by
        have := Nat.mul_pos hq0 hpow
        omega
      refine ⟨(q * 10 ^ (k + 1) + r) % 10 :: L, by simp [hL], ?_⟩
      have hdiv : (q * 10 ^ (k + 1) + r) / 10 = q * 10 ^ k + r / 10 := by
        have h : q * 10 ^ (k + 1) + r = r + q * 10 ^ k * 10 := by ring
        rw [h, Nat.add_mul_div_right _ _ h10, Nat.add_comm]
      rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hpos, hdiv, hLd]
      rfl

private lemma leading_digits (X k : ℕ) (h1 : 49787 * 10 ^ k ≤ X) (h2 : X < 49788 * 10 ^ k) :
    (Nat.digits 10 X).reverse.take 5 = [4, 9, 7, 8, 7] := by
  obtain ⟨r, hr⟩ : ∃ r, X = 49787 * 10 ^ k + r := ⟨X - 49787 * 10 ^ k, by omega⟩
  have hrlt : r < 10 ^ k := by omega
  obtain ⟨L, hL, hLd⟩ := digits_split 49787 (by norm_num) k r hrlt
  have hq : Nat.digits 10 49787 = [7, 8, 7, 9, 4] := by norm_num
  have hrev : ([7, 8, 7, 9, 4] : List ℕ).reverse = [4, 9, 7, 8, 7] := rfl
  rw [hr, hLd, hq, List.reverse_append, hrev]
  simp

-- ## Main computation

private lemma main_lemma (n : ℕ) (hn : 11 ≤ n) :
    (Nat.digits 10 ((10 ^ n - 3) ^ (10 ^ n))).reverse.take 5 = [4, 9, 7, 8, 7] := by
  have hM : (100000000000:ℕ) ≤ 10 ^ n := by
    calc (100000000000:ℕ) = 10 ^ 11 := by norm_num
      _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨hA, hB⟩ := key (10 ^ n) hM
  have hMM : ((10:ℕ) ^ n) ^ ((10:ℕ) ^ n) = 10 ^ (n * 10 ^ n) := by rw [← pow_mul]
  set M := (10:ℕ) ^ n with hMdef
  set K := n * M with hKdef
  have hM1 : 1 ≤ M := by omega
  have hK6 : 6 ≤ K := by
    rw [hKdef]
    calc (6:ℕ) ≤ 11 * 1 := by norm_num
      _ ≤ n * M := Nat.mul_le_mul hn hM1
  have hKsplit : K = 6 + (K - 6) := by omega
  have hpow : (10:ℕ) ^ K = 10 ^ 6 * 10 ^ (K - 6) := by
    conv_lhs => rw [hKsplit]
    rw [pow_add]
  apply leading_digits _ (K - 6)
  · have h1 : 49787 * (10 ^ 6 * 10 ^ (K - 6)) ≤ 10 ^ 6 * (M - 3) ^ M := by
      rw [← hpow, ← hMM]; exact hA
    have h2 : 10 ^ 6 * (49787 * 10 ^ (K - 6)) ≤ 10 ^ 6 * (M - 3) ^ M := by
      calc 10 ^ 6 * (49787 * 10 ^ (K - 6)) = 49787 * (10 ^ 6 * 10 ^ (K - 6)) := by ring
        _ ≤ 10 ^ 6 * (M - 3) ^ M := h1
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  · have h1 : 10 ^ 6 * (M - 3) ^ M < 49788 * (10 ^ 6 * 10 ^ (K - 6)) := by
      rw [← hpow, ← hMM]; exact hB
    have h2 : 10 ^ 6 * (M - 3) ^ M < 10 ^ 6 * (49788 * 10 ^ (K - 6)) := by
      calc 10 ^ 6 * (M - 3) ^ M < 49788 * (10 ^ 6 * 10 ^ (K - 6)) := h1
        _ = 10 ^ 6 * (49788 * 10 ^ (K - 6)) := by ring
    exact Nat.lt_of_mul_lt_mul_left h2

-- ## Facts about `a`
-- Indices are passed as *hypotheses* (`h : m = n + 1`) rather than as `n + 1`
-- in the statement, so Lean never has to unify `a (5 + 2)` with `a 7` — the
-- numeral arithmetic happens in goals where `a` does not occur.

private lemma a_step (n : ℕ) : a (n + 2) = 10 ^ a (n + 1) := by simp [a]

private lemma a_ge (n : ℕ) : 11 ≤ a (n + 1) := by
  induction n with
  | zero =>
      have h1 : a 1 = 11 := by simp [a]
      show 11 ≤ a 1
      omega
  | succ k ih =>
      show 11 ≤ a (k + 2)
      rw [a_step k]
      calc (11:ℕ) ≤ 10 ^ 11 := by norm_num
        _ ≤ 10 ^ a (k + 1) := Nat.pow_le_pow_right (by norm_num) ih

private lemma a_step' (n m k : ℕ) (h1 : m = n + 1) (h2 : k = n + 2) :
    a k = 10 ^ a m := by
  subst h1; subst h2; exact a_step n

private lemma a_ge' (n m : ℕ) (h : m = n + 1) : 11 ≤ a m := by
  subst h; exact a_ge n

private lemma final (n m : ℕ) (h1 : a m = 10 ^ a n) (h2 : 11 ≤ a n) :
    (Nat.digits 10 ((10 ^ a n - 3) ^ a m)).reverse.take 5 = [4, 9, 7, 8, 7] := by
  rw [h1]
  exact main_lemma _ h2

theorem first_five_digits_of_pow :
    ((Nat.digits 10 ((10 ^ a 6 - 3) ^ a 7)).reverse.take 5) = [4, 9, 7, 8, 7] :=
  final 6 7 (a_step' 5 6 7 (by norm_num) (by norm_num)) (a_ge' 5 6 (by norm_num))
```
