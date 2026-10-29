# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `21 August 2026`\
Line count: `206`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def tetrate (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => a ^ (tetrate a n)

lemma aux_no_two_of_lt_ten {x : ℕ} (hx : x < 10) (hx2 : x ≠ 2) :
    2 ∉ Nat.digits 10 x := by
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp
  · have hd10 : x / 10 = 0 := by omega
    have hm10 : x % 10 = x := by omega
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h, hd10, hm10, Nat.digits_zero]
    intro hmem
    rcases List.mem_cons.mp hmem with h' | h'
    · exact hx2 h'.symm
    · simp at h'

lemma aux_no_two_concat (m : ℕ) : ∀ a x : ℕ, x < 10 ^ m → 2 ∉ Nat.digits 10 a →
    2 ∉ Nat.digits 10 x → 2 ∉ Nat.digits 10 (a * 10 ^ m + x) := by
  induction m with
  | zero =>
    intro a x hx ha _
    have hx0 : x = 0 := by
      simp only [pow_zero] at hx
      omega
    subst hx0
    simpa using ha
  | succ m ih =>
    intro a x hx ha hxd
    have h2 : (10:ℕ) ^ (m + 1) = 10 * 10 ^ m := by ring
    have hq : x / 10 < 10 ^ m := by omega
    have hqd : 2 ∉ Nat.digits 10 (x / 10) := by
      rcases Nat.eq_zero_or_pos x with h | h
      · subst h; simp
      · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h] at hxd
        exact fun hmem => hxd (List.mem_cons.mpr (Or.inr hmem))
    have hr : x % 10 ≠ 2 := by
      rcases Nat.eq_zero_or_pos x with h | h
      · subst h; norm_num
      · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h] at hxd
        intro hh
        exact hxd (List.mem_cons.mpr (Or.inl hh.symm))
    have hpow : a * 10 ^ (m + 1) = 10 * (a * 10 ^ m) := by ring
    have key : a * 10 ^ (m + 1) + x = 10 * (a * 10 ^ m + x / 10) + x % 10 := by omega
    rw [key]
    rcases Nat.eq_zero_or_pos (10 * (a * 10 ^ m + x / 10) + x % 10) with h0 | h0
    · rw [h0]; simp
    · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h0]
      have hmod : (10 * (a * 10 ^ m + x / 10) + x % 10) % 10 = x % 10 := by omega
      have hdiv : (10 * (a * 10 ^ m + x / 10) + x % 10) / 10 = a * 10 ^ m + x / 10 := by omega
      rw [hmod, hdiv]
      intro hmem
      rcases List.mem_cons.mp hmem with h' | h'
      · exact hr h'.symm
      · exact ih a (x / 10) hq ha hqd h'

lemma aux_nines (k : ℕ) : 2 ∉ Nat.digits 10 (10 ^ k - 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h1 : (1:ℕ) ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (10:ℕ) ^ (k + 1) = 10 ^ k * 10 := by ring
    have h3 : (10:ℕ) ^ 1 = 10 := by norm_num
    have key : 10 ^ (k + 1) - 1 = (10 ^ k - 1) * 10 ^ 1 + 9 := by rw [h3]; omega
    rw [key]
    exact aux_no_two_concat 1 (10 ^ k - 1) 9 (by norm_num) ih
      (aux_no_two_of_lt_ten (by norm_num) (by norm_num))

lemma aux_two_mul_le_pow (m : ℕ) : 2 * m ≤ 10 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have h1 : (1:ℕ) ≤ 10 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (10:ℕ) ^ (m + 1) = 10 ^ m * 10 := by ring
    omega

def bigP (n : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 n, (tetrate 10 k - 1)

def bigS (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, tetrate 10 k

lemma tetrate_zero' : tetrate 10 0 = 1 := rfl
lemma tetrate_one' : tetrate 10 1 = 10 := rfl
lemma tetrate_succ' (n : ℕ) : tetrate 10 (n + 1) = 10 ^ tetrate 10 n := rfl

lemma bigP_one : bigP 1 = 9 := by simp [bigP, tetrate_one']

lemma bigS_one : bigS 1 = 1 := by simp [bigS, tetrate_zero']

lemma bigP_succ (n : ℕ) : bigP (n + 1) = bigP n * (tetrate 10 (n + 1) - 1) := by
  unfold bigP
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]

lemma bigS_succ (n : ℕ) : bigS (n + 1) = bigS n + tetrate 10 n := by
  unfold bigS
  rw [Finset.sum_range_succ]

lemma aux_step (p L m : ℕ) (hp0 : 0 < p) (hpL : p < 10 ^ L) (hLm : L ≤ m)
    (h1 : 2 ∉ Nat.digits 10 p) (h2 : 2 ∉ Nat.digits 10 (p - 1))
    (h3 : 2 ∉ Nat.digits 10 (10 ^ L - p)) (h4 : 2 ∉ Nat.digits 10 (10 ^ L - p - 1)) :
    0 < p * (10 ^ m - 1) ∧ p * (10 ^ m - 1) < 10 ^ (L + m) ∧
      2 ∉ Nat.digits 10 (p * (10 ^ m - 1)) ∧
      2 ∉ Nat.digits 10 (p * (10 ^ m - 1) - 1) ∧
      2 ∉ Nat.digits 10 (10 ^ (L + m) - p * (10 ^ m - 1)) ∧
      2 ∉ Nat.digits 10 (10 ^ (L + m) - p * (10 ^ m - 1) - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = L + d := ⟨m - L, by omega⟩
  have hp1 : 1 ≤ p := hp0
  have hL1 : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h
      simp only [pow_zero] at hpL
      omega
    · exact h
  have hdpos : (1:ℕ) ≤ 10 ^ d := Nat.one_le_pow _ _ (by norm_num)
  have hone : (1:ℕ) ≤ 10 ^ (L + d) := Nat.one_le_pow _ _ (by norm_num)
  have h10L : (10:ℕ) ≤ 10 ^ L := by
    calc (10:ℕ) = 10 ^ 1 := (pow_one 10).symm
      _ ≤ 10 ^ L := by
          apply Nat.pow_le_pow_right (by norm_num)
          omega
  have hLd : (10:ℕ) ^ L ≤ 10 ^ (L + d) := by
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  have hpm : p < 10 ^ (L + d) := lt_of_lt_of_le hpL hLd
  have hc1 : 1 ≤ 10 ^ L - p := by omega
  have hc2 : 1 ≤ 10 ^ (L + d) - p := by omega
  have hX1 : 1 ≤ p * (10 ^ (L + d) - 1) := by
    have h9 : 1 ≤ 10 ^ (L + d) - 1 := by omega
    calc (1:ℕ) = 1 * 1 := by norm_num
      _ ≤ p * (10 ^ (L + d) - 1) := Nat.mul_le_mul hp1 h9
  have hXlt : p * (10 ^ (L + d) - 1) < 10 ^ (L + (L + d)) := by
    have h5 : p * (10 ^ (L + d) - 1) < 10 ^ L * 10 ^ (L + d) :=
      calc p * (10 ^ (L + d) - 1) ≤ p * 10 ^ (L + d) :=
            Nat.mul_le_mul (le_refl p) (Nat.sub_le _ _)
        _ < 10 ^ L * 10 ^ (L + d) := mul_lt_mul_of_pos_right hpL (by omega)
    calc p * (10 ^ (L + d) - 1) < 10 ^ L * 10 ^ (L + d) := h5
      _ = 10 ^ (L + (L + d)) := (pow_add 10 L (L + d)).symm
  have hY1 : 1 ≤ 10 ^ (L + (L + d)) - p * (10 ^ (L + d) - 1) := by omega
  have hBeq : (10 ^ d - 1) * 10 ^ L + (10 ^ L - p) = 10 ^ (L + d) - p := by
    zify [hdpos, hpL.le, hpm.le]
    ring
  have hB1eq : (10 ^ d - 1) * 10 ^ L + (10 ^ L - p - 1) = 10 ^ (L + d) - p - 1 := by
    zify [hdpos, hpL.le, hpm.le, hc1, hc2]
    ring
  have e1 : p * (10 ^ (L + d) - 1) = (p - 1) * 10 ^ (L + d) + (10 ^ (L + d) - p) := by
    zify [hone, hp1, hpm.le]
    ring
  have e2 : p * (10 ^ (L + d) - 1) - 1
      = (p - 1) * 10 ^ (L + d) + (10 ^ (L + d) - p - 1) := by
    zify [hone, hp1, hpm.le, hX1, hc2]
    ring
  have e3 : 10 ^ (L + (L + d)) - p * (10 ^ (L + d) - 1)
      = (10 ^ L - p) * 10 ^ (L + d) + p := by
    zify [hone, hXlt.le, hpL.le]
    ring
  have e4 : 10 ^ (L + (L + d)) - p * (10 ^ (L + d) - 1) - 1
      = (10 ^ L - p) * 10 ^ (L + d) + (p - 1) := by
    zify [hone, hXlt.le, hpL.le, hY1, hp1]
    ring
  have hBdig : 2 ∉ Nat.digits 10 (10 ^ (L + d) - p) := by
    rw [← hBeq]
    exact aux_no_two_concat L (10 ^ d - 1) (10 ^ L - p) (by omega) (aux_nines d) h3
  have hB1dig : 2 ∉ Nat.digits 10 (10 ^ (L + d) - p - 1) := by
    rw [← hB1eq]
    exact aux_no_two_concat L (10 ^ d - 1) (10 ^ L - p - 1) (by omega) (aux_nines d) h4
  refine ⟨by omega, hXlt, ?_, ?_, ?_, ?_⟩
  · rw [e1]
    exact aux_no_two_concat (L + d) (p - 1) (10 ^ (L + d) - p) (by omega) h2 hBdig
  · rw [e2]
    exact aux_no_two_concat (L + d) (p - 1) (10 ^ (L + d) - p - 1) (by omega) h2 hB1dig
  · rw [e3]
    exact aux_no_two_concat (L + d) (10 ^ L - p) p (by omega) h3 h1
  · rw [e4]
    exact aux_no_two_concat (L + d) (10 ^ L - p) (p - 1) (by omega) h3 h2

lemma aux_main (n : ℕ) :
    0 < bigP (n + 1) ∧ bigP (n + 1) < 10 ^ bigS (n + 1) ∧
    bigS (n + 1) ≤ tetrate 10 (n + 1) ∧
    2 ∉ Nat.digits 10 (bigP (n + 1)) ∧ 2 ∉ Nat.digits 10 (bigP (n + 1) - 1) ∧
    2 ∉ Nat.digits 10 (10 ^ bigS (n + 1) - bigP (n + 1)) ∧
    2 ∉ Nat.digits 10 (10 ^ bigS (n + 1) - bigP (n + 1) - 1) := by
  induction n with
  | zero =>
    show 0 < bigP 1 ∧ bigP 1 < 10 ^ bigS 1 ∧ bigS 1 ≤ tetrate 10 1 ∧
      2 ∉ Nat.digits 10 (bigP 1) ∧ 2 ∉ Nat.digits 10 (bigP 1 - 1) ∧
      2 ∉ Nat.digits 10 (10 ^ bigS 1 - bigP 1) ∧
      2 ∉ Nat.digits 10 (10 ^ bigS 1 - bigP 1 - 1)
    rw [bigP_one, bigS_one, tetrate_one']
    refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩ <;>
      exact aux_no_two_of_lt_ten (by norm_num) (by norm_num)
  | succ n ih =>
    obtain ⟨hp0, hpL, hSle, hd1, hd2, hd3, hd4⟩ := ih
    have hPs : bigP (n + 1 + 1) = bigP (n + 1) * (10 ^ tetrate 10 (n + 1) - 1) := by
      rw [bigP_succ, tetrate_succ' (n + 1)]
    have hSs : bigS (n + 1 + 1) = bigS (n + 1) + tetrate 10 (n + 1) := bigS_succ (n + 1)
    have hTs : tetrate 10 (n + 1 + 1) = 10 ^ tetrate 10 (n + 1) := tetrate_succ' (n + 1)
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
      aux_step (bigP (n + 1)) (bigS (n + 1)) (tetrate 10 (n + 1)) hp0 hpL hSle hd1 hd2 hd3 hd4
    have hgrow := aux_two_mul_le_pow (tetrate 10 (n + 1))
    rw [hPs, hSs, hTs]
    exact ⟨c1, c2, by omega, c3, c4, c5, c6⟩

theorem product_tetrate_sub_one_no_digit_two (n : ℕ) (hn : 0 < n) :
    2 ∉ Nat.digits 10 (∏ k ∈ Finset.Icc 1 n, (tetrate 10 k - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (aux_main m).2.2.2.1
```
