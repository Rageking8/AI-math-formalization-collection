# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `16 August 2026`\
Line count: `145`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem digit_sum_divides (n : ℕ) (hn : 0 < n)
    (h : n ^ 2 + (Nat.digits 10 n).sum ^ 2 ∣ n ^ 4 + (Nat.digits 10 n).sum ^ 4) :
      (Nat.digits 10 n).sum ∣ n := by
  by_contra hns
  have hn0 : n ≠ 0 := hn.ne'
  -- Main arithmetic fact
  have main : ∀ a b : ℕ, 0 < a → 0 < b → ¬ b ∣ a →
      a ^ 2 + b ^ 2 ∣ a ^ 4 + b ^ 4 → 8 * a ^ 2 < b ^ 4 := by
    intro a b ha hb hdvd hdd
    -- work over ℤ for the subtractions
    have hddZ : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) ∣ ((a : ℤ) ^ 4 + (b : ℤ) ^ 4) := by
      exact_mod_cast hdd
    have hsq : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) ∣ ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) ^ 2 :=
      dvd_pow_self _ (by norm_num : (2 : ℕ) ≠ 0)
    have hd1Z : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) ∣ 2 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2 := by
      have h1 := dvd_sub hsq hddZ
      have e : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) ^ 2 - ((a : ℤ) ^ 4 + (b : ℤ) ^ 4)
          = 2 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2 := by ring
      rwa [e] at h1
    have hd2Z : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) ∣ 2 * (b : ℤ) ^ 4 := by
      have h3 : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) ∣
          2 * (b : ℤ) ^ 2 * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) := dvd_mul_left _ _
      have h4 := dvd_sub h3 hd1Z
      have e : 2 * (b : ℤ) ^ 2 * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) - 2 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2
          = 2 * (b : ℤ) ^ 4 := by ring
      rwa [e] at h4
    have hd3Z : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) ∣ 2 * (a : ℤ) ^ 4 := by
      have h3 : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) ∣
          2 * (a : ℤ) ^ 2 * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) := dvd_mul_left _ _
      have h4 := dvd_sub h3 hd1Z
      have e : 2 * (a : ℤ) ^ 2 * ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) - 2 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2
          = 2 * (a : ℤ) ^ 4 := by ring
      rwa [e] at h4
    have hd2 : a ^ 2 + b ^ 2 ∣ 2 * b ^ 4 := by exact_mod_cast hd2Z
    have hd3 : a ^ 2 + b ^ 2 ∣ 2 * a ^ 4 := by exact_mod_cast hd3Z
    -- gcd descent
    have hgpos : 0 < Nat.gcd a b :=
      Nat.pos_of_ne_zero fun hh => by
        have h0 := Nat.eq_zero_of_gcd_eq_zero_left hh
        omega
    obtain ⟨d, x, y, hdpos, hcop, hx, hy⟩ :
        ∃ d x y : ℕ, 0 < d ∧ Nat.Coprime x y ∧ a = d * x ∧ b = d * y :=
      ⟨Nat.gcd a b, a / Nat.gcd a b, b / Nat.gcd a b, hgpos,
        Nat.coprime_div_gcd_div_gcd hgpos,
        (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm,
        (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm⟩
    have hc4 : Nat.gcd (x ^ 4) (y ^ 4) = 1 := Nat.Coprime.pow 4 4 hcop
    have hgcd4 : Nat.gcd (a ^ 4) (b ^ 4) = d ^ 4 := by
      rw [hx, hy, mul_pow, mul_pow, Nat.gcd_mul_left, hc4, mul_one]
    have hdvd4 : a ^ 2 + b ^ 2 ∣ 2 * d ^ 4 := by
      have h5 := Nat.dvd_gcd hd3 hd2
      rwa [Nat.gcd_mul_left, hgcd4] at h5
    have hd4pos : 0 < d ^ 4 := pow_pos hdpos 4
    have hle : a ^ 2 + b ^ 2 ≤ 2 * d ^ 4 := Nat.le_of_dvd (by omega) hdvd4
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hy
      omega
    have hy1 : y ≠ 1 := by
      rintro rfl
      exact hdvd ⟨x, by rw [hx, hy]; ring⟩
    have h2d : 2 * d ≤ b := by
      have hy2 : 2 ≤ y := by omega
      calc 2 * d = d * 2 := by ring
        _ ≤ d * y := Nat.mul_le_mul le_rfl hy2
        _ = b := hy.symm
    have h16 : 16 * d ^ 4 ≤ b ^ 4 := by
      have hpw := Nat.pow_le_pow_left h2d 4
      calc 16 * d ^ 4 = (2 * d) ^ 4 := by ring
        _ ≤ b ^ 4 := hpw
    have hb2 : 0 < b ^ 2 := pow_pos hb 2
    linarith
  -- growth lemma
  have grow : ∀ m : ℕ, (m + 4) ^ 4 ≤ 10 ^ (2 * m + 3) := by
    intro m
    induction m with
    | zero => norm_num
    | succ k ih =>
      have h1 : (k + 1 + 4) ^ 4 ≤ (2 * (k + 4)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      have h2 : (2 * (k + 4)) ^ 4 = 16 * (k + 4) ^ 4 := by ring
      have h3 : 16 * (k + 4) ^ 4 ≤ 16 * 10 ^ (2 * k + 3) := Nat.mul_le_mul le_rfl ih
      have h4 : (10 : ℕ) ^ (2 * (k + 1) + 3) = 100 * 10 ^ (2 * k + 3) := by
        rw [show 2 * (k + 1) + 3 = 2 + (2 * k + 3) by ring, pow_add]
        norm_num
      have h5 : (16 : ℕ) * 10 ^ (2 * k + 3) ≤ 100 * 10 ^ (2 * k + 3) :=
        Nat.mul_le_mul (by norm_num) le_rfl
      linarith
  -- digit sum bounded by 9 * length
  have hgen : ∀ l : List ℕ, (∀ x ∈ l, x ≤ 9) → l.sum ≤ 9 * l.length := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih =>
      intro hall
      have h1 : a ≤ 9 := hall a (by simp)
      have h2 : t.sum ≤ 9 * t.length := ih fun x hx => hall x (by simp [hx])
      rw [List.sum_cons, List.length_cons]
      omega
  have hne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn0
  have hspos : 0 < (Nat.digits 10 n).sum := by
    have hmem : (Nat.digits 10 n).getLast hne ∈ Nat.digits 10 n := List.getLast_mem hne
    have hlast : (Nat.digits 10 n).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 10 hn0
    have hlee : (Nat.digits 10 n).getLast hne ≤ (Nat.digits 10 n).sum :=
      List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
    omega
  have key : 8 * n ^ 2 < (Nat.digits 10 n).sum ^ 4 := main n _ hn hspos hns h
  have hsum9 : (Nat.digits 10 n).sum ≤ 9 * (Nat.log 10 n + 1) := by
    have h1 : ∀ x ∈ Nat.digits 10 n, x ≤ 9 := by
      intro x hx
      have := Nat.digits_lt_base (by norm_num) hx
      omega
    have h2 := hgen _ h1
    rw [Nat.digits_len 10 n (by norm_num) hn0] at h2
    exact h2
  have hlogle : Nat.log 10 n ≤ 2 := by
    by_contra hc
    push_neg at hc
    obtain ⟨m, hm⟩ : ∃ m, Nat.log 10 n = m + 3 := ⟨Nat.log 10 n - 3, by omega⟩
    have hs' : (Nat.digits 10 n).sum ≤ 9 * (m + 4) := by
      rw [hm] at hsum9; omega
    have hs4 : (Nat.digits 10 n).sum ^ 4 ≤ (9 * (m + 4)) ^ 4 := Nat.pow_le_pow_left hs' 4
    have e1 : (9 * (m + 4)) ^ 4 = 6561 * (m + 4) ^ 4 := by ring
    have hgrow : (m + 4) ^ 4 ≤ 10 ^ (2 * m + 3) := grow m
    have h6561 : 6561 * (m + 4) ^ 4 ≤ 6561 * 10 ^ (2 * m + 3) := Nat.mul_le_mul le_rfl hgrow
    have hnge : (10 : ℕ) ^ (m + 3) ≤ n := by
      have hp := Nat.pow_log_le_self 10 hn0
      rwa [hm] at hp
    have hn2 : ((10 : ℕ) ^ (m + 3)) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hnge 2
    have e2 : ((10 : ℕ) ^ (m + 3)) ^ 2 = 1000 * 10 ^ (2 * m + 3) := by
      rw [← pow_mul, show (m + 3) * 2 = 3 + (2 * m + 3) by ring, pow_add]
      norm_num
    have hT : 0 < (10 : ℕ) ^ (2 * m + 3) := pow_pos (by norm_num) _
    linarith
  have hs27 : (Nat.digits 10 n).sum ≤ 27 := by omega
  have hn257 : n ≤ 257 := by
    by_contra hc
    push_neg at hc
    have h1 : (Nat.digits 10 n).sum ^ 4 ≤ 27 ^ 4 := Nat.pow_le_pow_left hs27 4
    have h2 : 258 ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
    norm_num at h1 h2
    linarith
  clear main grow hgen hne hspos key hsum9 hlogle hs27 hn0
  interval_cases n <;> revert h hns <;> norm_num
```
