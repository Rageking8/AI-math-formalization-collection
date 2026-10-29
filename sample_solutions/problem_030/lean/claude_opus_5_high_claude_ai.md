# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `4 August 2026`\
Line count: `251`\
Turn count: `3`

## Note

The conversation contained 2 "Continue" messages not included in the turn count.

## Solution

```lean4
import Mathlib

theorem digitSum_le_aux : ∀ (k n : ℕ), n ≤ k → (Nat.digits 10 n).sum ≤ n := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by omega
    subst hn0
    simp
  | succ k ih =>
    intro n hn
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h, List.sum_cons]
      have h1 : n / 10 ≤ k := by omega
      have h2 := ih (n / 10) h1
      omega

theorem digitSum_le (n : ℕ) : (Nat.digits 10 n).sum ≤ n := digitSum_le_aux n n le_rfl

theorem digitSum_pos_aux : ∀ (k n : ℕ), n ≤ k → 0 < n → 0 < (Nat.digits 10 n).sum := by
  intro k
  induction k with
  | zero => intro n hn h; omega
  | succ k ih =>
    intro n hn h
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h, List.sum_cons]
    rcases Nat.eq_zero_or_pos (n % 10) with h1 | h1
    · have h2 : 0 < n / 10 := by omega
      have h3 : n / 10 ≤ k := by omega
      have h4 := ih (n / 10) h3 h2
      omega
    · omega

theorem digitSum_pos (n : ℕ) (h : 0 < n) : 0 < (Nat.digits 10 n).sum :=
  digitSum_pos_aux n n le_rfl h

theorem digitSum_pow : ∀ (k n : ℕ), n < 10 ^ k → (Nat.digits 10 n).sum ≤ 9 * k := by
  intro k
  induction k with
  | zero =>
    intro n hn
    simp only [pow_zero, Nat.lt_one_iff] at hn
    subst hn
    simp
  | succ k ih =>
    intro n hn
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn' : n < 10 * 10 ^ k := by rw [pow_succ] at hn; linarith
      have h1 : n / 10 < 10 ^ k := Nat.div_lt_of_lt_mul hn'
      have h2 := ih (n / 10) h1
      rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h, List.sum_cons]
      omega

theorem digitSum_modEq_three (n : ℕ) : (Nat.digits 10 n).sum ≡ n [MOD 3] :=
  (Nat.modEq_digits_sum 3 10 (by norm_num) n).symm

theorem mod3_case_aux : ∀ ra rb rc : ℕ, ra < 3 → rb < 3 → rc < 3 →
    (ra * ra + rb * rb + rc * rc) % 3 = (ra * rb * rc) % 3 → ra = 0 ∧ rb = 0 ∧ rc = 0 := by
  intro ra rb rc h1 h2 h3 h
  interval_cases ra <;> interval_cases rb <;> interval_cases rc <;> omega

theorem exp_growth_aux : ∀ k, 4 ≤ k → 162 * (k + 1) ^ 2 < 10 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : 162 * (n + 1 + 1) ^ 2 ≤ 10 * (162 * (n + 1) ^ 2) := by
      nlinarith [sq_nonneg n, Nat.zero_le n, hn]
    have h3 : 10 * (162 * (n + 1) ^ 2) < 10 * 10 ^ n :=
      mul_lt_mul_of_pos_left ih (by norm_num)
    have h4 := lt_of_le_of_lt h2 h3
    have hps : (10:ℕ) ^ (n + 1) = 10 * 10 ^ n := by rw [pow_succ]; ring
    rw [hps]
    exact h4

theorem log_bound_aux (k : ℕ) (h : 10 ^ k ≤ 162 * (k + 1) ^ 2) : k ≤ 3 := by
  by_contra hk
  push_neg at hk
  exact absurd h (not_le.mpr (exp_growth_aux k (by omega)))

theorem key3_aux (m n : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n) : 3 * n + m ≤ m * n + 3 := by
  obtain ⟨d, rfl⟩ : ∃ d, m = 3 + d := ⟨m - 3, by omega⟩
  have hd : d * 1 ≤ d * n := Nat.mul_le_mul (le_refl d) hn
  linarith

set_option maxHeartbeats 1000000 in
theorem sorted_main (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hbc : b ≤ c)
    (ha2 : a % 2 = 1) (hb2 : b % 2 = 1) (hc2 : c % 2 = 1)
    (heq : a * (Nat.digits 10 a).sum + b * (Nat.digits 10 b).sum + c * (Nat.digits 10 c).sum
      = a * b * c) :
    a = 3 ∧ b = 3 ∧ c = 3 := by
  have hsa_le : (Nat.digits 10 a).sum ≤ a := digitSum_le a
  have hsb_le : (Nat.digits 10 b).sum ≤ b := digitSum_le b
  have hsc_le : (Nat.digits 10 c).sum ≤ c := digitSum_le c
  have hsa_pos : 0 < (Nat.digits 10 a).sum := digitSum_pos a ha
  have hsb_pos : 0 < (Nat.digits 10 b).sum := digitSum_pos b hb
  have hsc_pos : 0 < (Nat.digits 10 c).sum := digitSum_pos c hc
  have hm3 : a * a + b * b + c * c ≡ a * b * c [MOD 3] := by
    have h := Nat.ModEq.add (Nat.ModEq.add
        (Nat.ModEq.mul (Nat.ModEq.refl a) (digitSum_modEq_three a))
        (Nat.ModEq.mul (Nat.ModEq.refl b) (digitSum_modEq_three b)))
        (Nat.ModEq.mul (Nat.ModEq.refl c) (digitSum_modEq_three c))
    rw [heq] at h
    exact h.symm
  have hfin : ((a % 3) * (a % 3) + (b % 3) * (b % 3) + (c % 3) * (c % 3)) % 3
      = ((a % 3) * (b % 3) * (c % 3)) % 3 := by
    have ea : a % 3 ≡ a [MOD 3] := Nat.mod_modEq a 3
    have eb : b % 3 ≡ b [MOD 3] := Nat.mod_modEq b 3
    have ec : c % 3 ≡ c [MOD 3] := Nat.mod_modEq c 3
    have A := ((ea.mul ea).add (eb.mul eb)).add (ec.mul ec)
    have B := (ea.mul eb).mul ec
    exact A.trans (hm3.trans B.symm)
  obtain ⟨e1, e2, e3⟩ :=
    mod3_case_aux (a % 3) (b % 3) (c % 3) (by omega) (by omega) (by omega) hfin
  have ha3 : 3 ≤ a := by omega
  have hb3 : 3 ≤ b := by omega
  have hc3 : 3 ≤ c := by omega
  have key : c * (a * b) = a * (Nat.digits 10 a).sum + b * (Nat.digits 10 b).sum
      + c * (Nat.digits 10 c).sum := by rw [heq]; ring
  have hA : a * b ≤ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum + (Nat.digits 10 c).sum := by
    have h1 : a * (Nat.digits 10 a).sum ≤ c * (Nat.digits 10 a).sum :=
      Nat.mul_le_mul (hab.trans hbc) (le_refl _)
    have h2 : b * (Nat.digits 10 b).sum ≤ c * (Nat.digits 10 b).sum :=
      Nat.mul_le_mul hbc (le_refl _)
    have h4 : c * (a * b) ≤ c * ((Nat.digits 10 a).sum + (Nat.digits 10 b).sum
        + (Nat.digits 10 c).sum) := by
      rw [key]; linarith
    exact Nat.le_of_mul_le_mul_left h4 hc
  have hB : (Nat.digits 10 c).sum < a * b := by
    by_contra hcon
    push_neg at hcon
    have h5 : c * (a * b) ≤ c * (Nat.digits 10 c).sum := Nat.mul_le_mul (le_refl c) hcon
    rw [key] at h5
    have hp1 : 0 < a * (Nat.digits 10 a).sum := mul_pos ha hsa_pos
    have hp2 : 0 < b * (Nat.digits 10 b).sum := mul_pos hb hsb_pos
    linarith
  have hC : c ≤ a * (Nat.digits 10 a).sum + b * (Nat.digits 10 b).sum := by
    have h5 : c * ((Nat.digits 10 c).sum + 1) ≤ c * (a * b) :=
      Nat.mul_le_mul (le_refl c) (by omega)
    rw [key] at h5
    linarith
  have hcb : c ≤ 2 * (b * b) := by
    have h1 : a * (Nat.digits 10 a).sum ≤ b * b := Nat.mul_le_mul hab (hsa_le.trans hab)
    have h2 : b * (Nat.digits 10 b).sum ≤ b * b := Nat.mul_le_mul (le_refl b) hsb_le
    linarith
  have h3b : 3 * b ≤ a * b := Nat.mul_le_mul ha3 (le_refl b)
  have hbsc : b ≤ (Nat.digits 10 c).sum := by linarith
  have hlog : c < 10 ^ (Nat.log 10 c + 1) := Nat.lt_pow_succ_log_self (by norm_num) c
  have hsc_bd : (Nat.digits 10 c).sum ≤ 9 * (Nat.log 10 c + 1) := digitSum_pow _ c hlog
  have hk3 : Nat.log 10 c ≤ 3 := by
    apply log_bound_aux
    have h1 : 10 ^ Nat.log 10 c ≤ c := Nat.pow_log_le_self 10 (by omega)
    have h2 : b ≤ 9 * (Nat.log 10 c + 1) := le_trans hbsc hsc_bd
    have h3 : b * b ≤ (9 * (Nat.log 10 c + 1)) * (9 * (Nat.log 10 c + 1)) := Nat.mul_le_mul h2 h2
    linarith
  have hsc36 : (Nat.digits 10 c).sum ≤ 36 := by linarith
  have hb19 : b ≤ 19 := by
    have h1 : 3 * b + a ≤ a * b + 3 := key3_aux a b ha3 (by omega)
    have h2 : 2 * b ≤ 39 := by linarith
    omega
  have hbb : b * b ≤ 19 * 19 := Nat.mul_le_mul hb19 hb19
  have hc722 : c < 1000 := by linarith
  have hsc27 : (Nat.digits 10 c).sum ≤ 27 := by
    have hp : (10:ℕ) ^ 3 = 1000 := by norm_num
    have h1 : c < 10 ^ 3 := by rw [hp]; exact hc722
    have h2 := digitSum_pow 3 c h1
    omega
  have haeq : a = 3 := by
    by_contra hne
    have ha9 : 9 ≤ a := by omega
    have h1 : 9 * b ≤ a * b := Nat.mul_le_mul ha9 (le_refl b)
    have h2 : a * b ≤ a + b + 27 := by linarith
    linarith
  subst haeq
  have d3 : (Nat.digits 10 3).sum = 3 := by norm_num
  rw [d3] at heq hC
  have hbcase : b = 3 ∨ b = 9 ∨ b = 15 := by omega
  rcases hbcase with rfl | rfl | rfl
  · rw [d3] at heq hC
    have hc18 : c ≤ 18 := by omega
    have hccase : c = 3 ∨ c = 9 ∨ c = 15 := by omega
    rcases hccase with rfl | rfl | rfl
    · exact ⟨rfl, rfl, rfl⟩
    · exfalso
      rw [show (Nat.digits 10 9).sum = 9 by norm_num] at heq
      omega
    · exfalso
      rw [show (Nat.digits 10 15).sum = 6 by norm_num] at heq
      omega
  · exfalso
    rw [show (Nat.digits 10 9).sum = 9 by norm_num] at heq hC
    have hc90 : c ≤ 90 := by omega
    have hsc18 : (Nat.digits 10 c).sum ≤ 18 := by
      have hp : (10:ℕ) ^ 2 = 100 := by norm_num
      have h1 : c < 10 ^ 2 := by rw [hp]; omega
      have h2 := digitSum_pow 2 c h1
      omega
    have h3 : c * (Nat.digits 10 c).sum ≤ c * 18 := Nat.mul_le_mul (le_refl c) hsc18
    have hc10 : c ≤ 10 := by linarith
    have hc9 : c = 9 := by omega
    subst hc9
    rw [show (Nat.digits 10 9).sum = 9 by norm_num] at heq
    omega
  · exfalso
    rw [show (Nat.digits 10 15).sum = 6 by norm_num] at heq hC
    have hc99 : c ≤ 99 := by omega
    have hsc18 : (Nat.digits 10 c).sum ≤ 18 := by
      have hp : (10:ℕ) ^ 2 = 100 := by norm_num
      have h1 : c < 10 ^ 2 := by rw [hp]; omega
      have h2 := digitSum_pow 2 c h1
      omega
    have h3 : c * (Nat.digits 10 c).sum ≤ c * 18 := Nat.mul_le_mul (le_refl c) hsc18
    linarith

set_option maxHeartbeats 1000000 in
theorem odd_digit_sum_eq_xyz_iff (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxo : Odd x) (hyo : Odd y) (hzo : Odd z) :
      x * (Nat.digits 10 x).sum + y * (Nat.digits 10 y).sum + z * (Nat.digits 10 z).sum = x * y * z ↔
      x = 3 ∧ y = 3 ∧ z = 3 := by
  have hx2 : x % 2 = 1 := Nat.odd_iff.mp hxo
  have hy2 : y % 2 = 1 := Nat.odd_iff.mp hyo
  have hz2 : z % 2 = 1 := Nat.odd_iff.mp hzo
  constructor
  · intro heq
    rcases le_total x y with h1 | h1
    · rcases le_total y z with h2 | h2
      · exact sorted_main x y z hx hy hz h1 h2 hx2 hy2 hz2 heq
      · rcases le_total x z with h3 | h3
        · obtain ⟨e1, e2, e3⟩ :=
            sorted_main x z y hx hz hy h3 h2 hx2 hz2 hy2 (by linarith)
          exact ⟨e1, e3, e2⟩
        · obtain ⟨e1, e2, e3⟩ :=
            sorted_main z x y hz hx hy h3 h1 hz2 hx2 hy2 (by linarith)
          exact ⟨e2, e3, e1⟩
    · rcases le_total x z with h2 | h2
      · obtain ⟨e1, e2, e3⟩ :=
          sorted_main y x z hy hx hz h1 h2 hy2 hx2 hz2 (by linarith)
        exact ⟨e2, e1, e3⟩
      · rcases le_total y z with h3 | h3
        · obtain ⟨e1, e2, e3⟩ :=
            sorted_main y z x hy hz hx h3 h2 hy2 hz2 hx2 (by linarith)
          exact ⟨e3, e1, e2⟩
        · obtain ⟨e1, e2, e3⟩ :=
            sorted_main z y x hz hy hx h3 h1 hz2 hy2 hx2 (by linarith)
          exact ⟨e3, e2, e1⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num
```
