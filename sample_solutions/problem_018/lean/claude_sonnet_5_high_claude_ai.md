# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `7 September 2026`\
Line count: `96`\
Turn count: `1`

## Note

This solution uses `native_decide`.

## Solution

```lean4
import Mathlib

lemma digits_len_le_of_lt_pow :
    ∀ (k m : ℕ), m < 10 ^ k → (Nat.digits 10 m).length ≤ k := by
  intro k
  induction k with
  | zero =>
      intro m hm
      simp only [pow_zero, Nat.lt_one_iff] at hm
      subst hm
      simp
  | succ k ih =>
      intro m hm
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        simp
      · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h0]
        simp only [List.length_cons]
        have hdiv : m / 10 < 10 ^ k := by
          rw [pow_succ] at hm
          omega
        have hle := ih (m / 10) hdiv
        omega

lemma lt_pow_of_digits_len_le :
    ∀ (k m : ℕ), (Nat.digits 10 m).length ≤ k → m < 10 ^ k := by
  intro k
  induction k with
  | zero =>
      intro m hm
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        norm_num
      · exfalso
        rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h0] at hm
        simp only [List.length_cons] at hm
        omega
  | succ k ih =>
      intro m hm
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        positivity
      · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h0] at hm
        simp only [List.length_cons] at hm
        have hm' : (Nat.digits 10 (m / 10)).length ≤ k := by omega
        have hdiv := ih (m / 10) hm'
        have hmod : m % 10 < 10 := Nat.mod_lt m (by norm_num)
        have heq := Nat.div_add_mod m 10
        rw [pow_succ]
        omega

theorem no_nat_sq_cube_digits_one_through_nine_twice :
    ¬ ∃ (n : ℕ), List.Perm (Nat.digits 10 (n ^ 2) ++ Nat.digits 10 (n ^ 3))
      (List.range' 1 9 ++ List.range' 1 9) := by
  rintro ⟨n, hperm⟩
  have hlen : (Nat.digits 10 (n ^ 2)).length + (Nat.digits 10 (n ^ 3)).length = 18 := by
    have h := hperm.length_eq
    simp only [List.length_append, List.length_range'] at h
    omega
  have hn_lb : 2155 ≤ n := by
    by_contra hc
    push_neg at hc
    have hc' : n ≤ 2154 := by omega
    have h1 : n ^ 2 ≤ 2154 ^ 2 := Nat.pow_le_pow_left hc' 2
    have h2 : n ^ 3 ≤ 2154 ^ 3 := Nat.pow_le_pow_left hc' 3
    have h1' : n ^ 2 < 10 ^ 7 := lt_of_le_of_lt h1 (by norm_num)
    have h2' : n ^ 3 < 10 ^ 10 := lt_of_le_of_lt h2 (by norm_num)
    have l1 := digits_len_le_of_lt_pow 7 (n ^ 2) h1'
    have l2 := digits_len_le_of_lt_pow 10 (n ^ 3) h2'
    omega
  have hn_ub : n ≤ 3162 := by
    by_contra hc
    push_neg at hc
    have hc' : 3163 ≤ n := by omega
    have h1 : 3163 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hc' 2
    have h2 : 3163 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hc' 3
    have h1' : 10 ^ 7 ≤ n ^ 2 := le_trans (by norm_num) h1
    have h2' : 10 ^ 10 ≤ n ^ 3 := le_trans (by norm_num) h2
    have l1 : 8 ≤ (Nat.digits 10 (n ^ 2)).length := by
      by_contra hc2
      push_neg at hc2
      have hle : (Nat.digits 10 (n ^ 2)).length ≤ 7 := by omega
      have := lt_pow_of_digits_len_le 7 (n ^ 2) hle
      omega
    have l2 : 11 ≤ (Nat.digits 10 (n ^ 3)).length := by
      by_contra hc2
      push_neg at hc2
      have hle : (Nat.digits 10 (n ^ 3)).length ≤ 10 := by omega
      have := lt_pow_of_digits_len_le 10 (n ^ 3) hle
      omega
    omega
  have key : ∀ m ∈ Finset.Icc 2155 3162,
      ¬ List.Perm (Nat.digits 10 (m ^ 2) ++ Nat.digits 10 (m ^ 3))
        (List.range' 1 9 ++ List.range' 1 9) := by
    native_decide
  exact key n (Finset.mem_Icc.mpr ⟨hn_lb, hn_ub⟩) hperm
```
