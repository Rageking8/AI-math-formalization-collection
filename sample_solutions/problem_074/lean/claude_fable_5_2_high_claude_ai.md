# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `13 November 2026`\
Line count: `221`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def a : ℕ → ℕ
  | 0 => 0
  | 1 => 11
  | n + 2 => 10 ^ a (n + 1)

theorem first_five_digits_of_pow :
    ((Nat.digits 10 ((10 ^ a 6 - 3) ^ a 7)).reverse.take 5) = [4, 9, 7, 8, 7] := by
  -- Unfolding lemma for `a` (stated for a variable index so nothing huge is ever evaluated).
  have a_ss : ∀ n : ℕ, a (n + 2) = 10 ^ a (n + 1) := fun n => by rw [a]
  have a_ge : ∀ n : ℕ, 11 ≤ a (n + 1) := by
    intro n
    induction n with
    | zero => simp [a]
    | succ k ih =>
      rw [a_ss]
      have h : a (k + 1) < 10 ^ a (k + 1) := by
        apply Nat.lt_pow_self
        norm_num
      omega
  -- Leading digits of a number squeezed between `49787 * 10 ^ k` and `49788 * 10 ^ k`.
  have digits_aux : ∀ k n : ℕ, 49787 * 10 ^ k ≤ n → n < 49788 * 10 ^ k →
      ∃ l : List ℕ, Nat.digits 10 n = l ++ [7, 8, 7, 9, 4] := by
    intro k
    induction k with
    | zero =>
      intro n h1 h2
      have hn : n = 49787 := by omega
      subst hn
      exact ⟨[], by norm_num⟩
    | succ k ih =>
      intro n h1 h2
      rw [pow_succ] at h1 h2
      have hk : 0 < 10 ^ k := by positivity
      have hpos : 0 < n := by omega
      obtain ⟨l, hl⟩ := ih (n / 10) (by omega) (by omega)
      refine ⟨(n % 10) :: l, ?_⟩
      rw [Nat.digits_def' (by norm_num) hpos, hl]
      rfl
  -- The analytic estimate: `(1 - 3 / x) ^ x` is squeezed around `exp (-3)`.
  have real_bounds : ∀ (x : ℝ) (n : ℕ), (10 : ℝ) ^ 11 ≤ x → (n : ℝ) = x →
      49787 * x ^ n ≤ 10 ^ 6 * (x - 3) ^ n ∧ 10 ^ 6 * (x - 3) ^ n < 49788 * x ^ n := by
    intro x n hx hn
    have hx0 : 0 < x := by linarith [show (0 : ℝ) < 10 ^ 11 by norm_num]
    have hx3 : (10 : ℝ) ^ 10 ≤ x - 3 := by
      have : (10 : ℝ) ^ 10 + 3 ≤ 10 ^ 11 := by norm_num
      linarith
    have hx3' : 0 < x - 3 := by linarith [show (0 : ℝ) < 10 ^ 10 by norm_num]
    have hxn : 0 < x ^ n := by positivity
    have hfac : (x - 3) ^ n = x ^ n * (1 - 3 / x) ^ n := by
      rw [← mul_pow]
      congr 1
      field_simp
    have he3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    have he1 := Real.exp_one_gt_d9
    have he2 := Real.exp_one_lt_d9
    have hlo3 : (20.0855 : ℝ) < Real.exp 3 := by
      rw [he3]
      have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have ha : (2.7182818283 : ℝ) * 2.7182818283 < Real.exp 1 * Real.exp 1 := by
        nlinarith
      have hb : (2.7182818283 : ℝ) * 2.7182818283 * 2.7182818283 <
          Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        nlinarith
      have hc : (20.0855 : ℝ) < 2.7182818283 * 2.7182818283 * 2.7182818283 := by norm_num
      linarith
    have hhi3 : Real.exp 3 < (20.08554 : ℝ) := by
      rw [he3]
      have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have ha : Real.exp 1 * Real.exp 1 < (2.7182818286 : ℝ) * 2.7182818286 := by
        nlinarith
      have hb : Real.exp 1 * Real.exp 1 * Real.exp 1 <
          (2.7182818286 : ℝ) * 2.7182818286 * 2.7182818286 := by
        nlinarith
      have hc : (2.7182818286 : ℝ) * 2.7182818286 * 2.7182818286 < 20.08554 := by norm_num
      linarith
    have hm3 : 0 < Real.exp (-3) := Real.exp_pos _
    have hprod : Real.exp (-3) * Real.exp 3 = 1 := by
      rw [← Real.exp_add]
      norm_num
    constructor
    · -- lower bound
      have ht : 0 < 3 / (x - 3) := by positivity
      have hprod' : Real.exp (-(3 / (x - 3))) * Real.exp (3 / (x - 3)) = 1 := by
        rw [← Real.exp_add]
        simp
      have h1 : Real.exp (-(3 / (x - 3))) ≤ 1 - 3 / x := by
        have h := Real.add_one_le_exp (3 / (x - 3))
        have hid : (1 - 3 / x) * (3 / (x - 3) + 1) = 1 := by
          field_simp
          ring
        have hpos : 0 < Real.exp (-(3 / (x - 3))) := Real.exp_pos _
        have hle : Real.exp (-(3 / (x - 3))) * (3 / (x - 3) + 1) ≤
            (1 - 3 / x) * (3 / (x - 3) + 1) := by
          have hmul := mul_le_mul_of_nonneg_left h hpos.le
          rw [hprod'] at hmul
          rw [hid]
          exact hmul
        exact le_of_mul_le_mul_right hle (by linarith)
      have h2 : Real.exp (-(3 / (x - 3))) ^ n ≤ (1 - 3 / x) ^ n := by
        have := Real.exp_pos (-(3 / (x - 3)))
        gcongr
      have h3 : Real.exp (-(3 / (x - 3))) ^ n = Real.exp (-3) * Real.exp (-(9 / (x - 3))) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, hn]
        congr 1
        field_simp
        ring
      have h4 : 1 - 9 / (x - 3) ≤ Real.exp (-(9 / (x - 3))) := by
        have := Real.add_one_le_exp (-(9 / (x - 3)))
        linarith
      have h5 : (1 : ℝ) - 1 / 10 ^ 9 ≤ 1 - 9 / (x - 3) := by
        have hq : 9 / (x - 3) * (x - 3) = 9 := by field_simp
        have hq0 : 0 < 9 / (x - 3) := by positivity
        have : 9 / (x - 3) ≤ 1 / 10 ^ 9 := by
          by_contra hcon
          rw [not_le] at hcon
          have h10 : (1 : ℝ) / 10 ^ 9 * 10 ^ 10 = 10 := by norm_num
          have := mul_le_mul hcon.le hx3 (by norm_num) hq0.le
          linarith
        linarith
      have h6 : (49787 : ℝ) / 10 ^ 6 ≤ Real.exp (-3) * (1 - 1 / 10 ^ 9) := by
        have hlt : Real.exp (-3) * Real.exp 3 < Real.exp (-3) * 20.08554 :=
          mul_lt_mul_of_pos_left hhi3 hm3
        rw [hprod] at hlt
        norm_num
        linarith
      have h9 : (49787 : ℝ) / 10 ^ 6 ≤ (1 - 3 / x) ^ n := by
        calc (49787 : ℝ) / 10 ^ 6 ≤ Real.exp (-3) * (1 - 1 / 10 ^ 9) := h6
          _ ≤ Real.exp (-3) * Real.exp (-(9 / (x - 3))) :=
              mul_le_mul_of_nonneg_left (h5.trans h4) hm3.le
          _ = Real.exp (-(3 / (x - 3))) ^ n := h3.symm
          _ ≤ _ := h2
      rw [hfac]
      have := mul_le_mul_of_nonneg_left h9 hxn.le
      linarith
    · -- upper bound
      have h1 : 1 - 3 / x ≤ Real.exp (-(3 / x)) := by
        have := Real.add_one_le_exp (-(3 / x))
        linarith
      have h0 : 0 ≤ 1 - 3 / x := by
        have hq : 3 / x * x = 3 := by field_simp
        have hq0 : 0 < 3 / x := by positivity
        by_contra hcon
        rw [not_le] at hcon
        have h1' : (1 : ℝ) ≤ 3 / x := by linarith
        have := mul_le_mul h1' hx (by norm_num) hq0.le
        norm_num at this
        linarith
      have h2 : (1 - 3 / x) ^ n ≤ Real.exp (-(3 / x)) ^ n := by
        gcongr
      have h3 : Real.exp (-(3 / x)) ^ n = Real.exp (-3) := by
        rw [← Real.exp_nat_mul, hn]
        congr 1
        field_simp
      have h4 : Real.exp (-3) < 49788 / 10 ^ 6 := by
        have hlt : Real.exp (-3) * 20.0855 < Real.exp (-3) * Real.exp 3 :=
          mul_lt_mul_of_pos_left hlo3 hm3
        rw [hprod] at hlt
        norm_num
        linarith
      have h5 : (1 - 3 / x) ^ n < 49788 / 10 ^ 6 := by
        rw [h3] at h2
        linarith
      rw [hfac]
      have := mul_lt_mul_of_pos_left h5 hxn
      linarith
  -- The statement for a genuinely variable exponent `M` (kept as a real `∀`, so that the
  -- kernel never sees `a 6` substituted inside the computation).
  have key : ∀ M : ℕ, 11 ≤ M →
      ((Nat.digits 10 ((10 ^ M - 3) ^ (10 ^ M))).reverse.take 5) = [4, 9, 7, 8, 7] := by
    intro M hM
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = 10 ^ M := ⟨_, rfl⟩
    rw [← hN]
    have hN11 : 10 ^ 11 ≤ N := by
      rw [hN]
      exact Nat.pow_le_pow_right (by norm_num) hM
    have hN3 : 3 ≤ N := le_trans (by norm_num) hN11
    have hMN : 6 ≤ M * N := by nlinarith
    have hcast : ((N - 3 : ℕ) : ℝ) = (N : ℝ) - 3 := by
      rw [Nat.cast_sub hN3]
      norm_num
    have hx : (10 : ℝ) ^ 11 ≤ (N : ℝ) := by exact_mod_cast hN11
    obtain ⟨hlo, hhi⟩ := real_bounds (N : ℝ) N hx rfl
    have hpow : N ^ N = 10 ^ 6 * 10 ^ (M * N - 6) := by
      rw [← pow_add, Nat.add_sub_cancel' hMN, pow_mul, ← hN]
    have hlo' : 49787 * N ^ N ≤ 10 ^ 6 * (N - 3) ^ N := by
      have : ((49787 * N ^ N : ℕ) : ℝ) ≤ ((10 ^ 6 * (N - 3) ^ N : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, hcast]
        exact_mod_cast hlo
      exact_mod_cast this
    have hhi' : 10 ^ 6 * (N - 3) ^ N < 49788 * N ^ N := by
      have : ((10 ^ 6 * (N - 3) ^ N : ℕ) : ℝ) < ((49788 * N ^ N : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, hcast]
        exact_mod_cast hhi
      exact_mod_cast this
    rw [hpow] at hlo' hhi'
    have hpos6 : 0 < 10 ^ 6 := by norm_num
    obtain ⟨l, hl⟩ := digits_aux (M * N - 6) ((N - 3) ^ N)
      (Nat.le_of_mul_le_mul_left (by linarith) hpos6)
      (Nat.lt_of_mul_lt_mul_left (a := 10 ^ 6) (by linarith))
    rw [hl]
    simp
  -- Put everything together.
  -- (`a 7` and `a 6` are only ever related through explicit equations on the indices,
  -- so that neither the elaborator nor the kernel tries to evaluate these towers.)
  have a_ss' : ∀ m j k : ℕ, m = k + 2 → j = k + 1 → a m = 10 ^ a j := by
    intro m j k hm hj
    subst hm
    subst hj
    exact a_ss k
  have a_ge' : ∀ j k : ℕ, j = k + 1 → 11 ≤ a j := by
    intro j k hj
    subst hj
    exact a_ge k
  have h7 : a 7 = 10 ^ a 6 := a_ss' 7 6 5 (by norm_num) (by norm_num)
  have hM : 11 ≤ a 6 := a_ge' 6 5 (by norm_num)
  rw [h7]
  exact key (a 6) hM
```
