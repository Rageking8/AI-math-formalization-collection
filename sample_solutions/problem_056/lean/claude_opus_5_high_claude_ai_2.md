# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `2 September 2026`\
Line count: `158`\
Turn count: `3`

## Note

The solution is more verbose as the model is explicitly told not to use `native_decide`. The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem digit_sum_divides (n : ℕ) (hn : 0 < n)
    (h : n ^ 2 + (Nat.digits 10 n).sum ^ 2 ∣ n ^ 4 + (Nat.digits 10 n).sum ^ 4) :
      (Nat.digits 10 n).sum ∣ n := by
  by_contra hcon
  have pow10 : ∀ m : ℕ, m < 10 ^ m := by
    intro m; induction m with
    | zero => norm_num
    | succ k ih =>
      have h1 : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
      rw [pow_succ]; linarith
  have key : ∀ k m : ℕ, m < 10 ^ k → (Nat.digits 10 m).sum ≤ 9 * k := by
    intro k; induction k with
    | zero => intro m hm; rw [pow_zero, Nat.lt_one_iff] at hm; subst hm; simp
    | succ k ih =>
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp
      · have hq : m / 10 < 10 ^ k := by rw [pow_succ] at hm; omega
        have h2 := ih (m / 10) hq
        rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hm0]
        simp only [List.sum_cons]; omega
  have key3 : ∀ m : ℕ, m < 1000 → (Nat.digits 10 m).sum ≤ 27 := by simpa using key 3
  have pos : ∀ k m : ℕ, m < 10 ^ k → 0 < m → 0 < (Nat.digits 10 m).sum := by
    intro k; induction k with
    | zero => intro m hm hm0; exfalso; rw [pow_zero] at hm; omega
    | succ k ih =>
      intro m hm hm0
      have hq : m / 10 < 10 ^ k := by rw [pow_succ] at hm; omega
      rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hm0]
      simp only [List.sum_cons]
      rcases Nat.eq_zero_or_pos (m / 10) with h0 | h0
      · omega
      · have h2 := ih (m / 10) hq h0; omega
  have dig : ∀ k m : ℕ, m < 10 ^ k → 258 ≤ m → (Nat.digits 10 m).sum ^ 4 < 8 * m ^ 2 := by
    intro k; induction k with
    | zero => intro m hm h258; exfalso; rw [pow_zero] at hm; omega
    | succ k ih =>
      intro m hm h258
      rcases Nat.lt_or_ge m 1000 with hsmall | hbig
      · have e1 : (Nat.digits 10 m).sum ^ 4 ≤ 531441 := by
          calc (Nat.digits 10 m).sum ^ 4 ≤ 27 ^ 4 := Nat.pow_le_pow_left (key3 m hsmall) 4
            _ = 531441 := by norm_num
        have e2 : 66564 ≤ m ^ 2 := by
          calc (66564 : ℕ) = 258 ^ 2 := by norm_num
            _ ≤ m ^ 2 := Nat.pow_le_pow_left h258 2
        linarith
      · have hm0 : 0 < m := by omega
        have hq : m / 10 < 10 ^ k := by rw [pow_succ] at hm; omega
        rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hm0]
        simp only [List.sum_cons]
        rcases Nat.lt_or_ge (m / 10) 258 with hlt | hge
        · have h27 : (Nat.digits 10 (m / 10)).sum ≤ 27 := key3 _ (by omega)
          have e1 : (m % 10 + (Nat.digits 10 (m / 10)).sum) ^ 4 ≤ 1679616 := by
            calc (m % 10 + (Nat.digits 10 (m / 10)).sum) ^ 4 ≤ 36 ^ 4 :=
                  Nat.pow_le_pow_left (by omega) 4
              _ = 1679616 := by norm_num
          have e2 : 1000000 ≤ m ^ 2 := by
            calc (1000000 : ℕ) = 1000 ^ 2 := by norm_num
              _ ≤ m ^ 2 := Nat.pow_le_pow_left hbig 2
          linarith
        · have IH := ih (m / 10) hq hge
          have hdm : m / 10 * 10 ≤ m := Nat.div_mul_le_self m 10
          have e2 : 100 * (m / 10) ^ 2 ≤ m ^ 2 := by nlinarith [Nat.mul_le_mul hdm hdm]
          have hp : 1 ≤ (m / 10) ^ 2 := Nat.one_le_pow 2 (m / 10) (by omega)
          rcases Nat.lt_or_ge ((Nat.digits 10 (m / 10)).sum) 9 with h9 | h9
          · have e1 : (m % 10 + (Nat.digits 10 (m / 10)).sum) ^ 4 ≤ 83521 := by
              calc (m % 10 + (Nat.digits 10 (m / 10)).sum) ^ 4 ≤ 17 ^ 4 :=
                    Nat.pow_le_pow_left (by omega) 4
                _ = 83521 := by norm_num
            have e3 : 6656400 ≤ m ^ 2 := by
              calc (6656400 : ℕ) = 2580 ^ 2 := by norm_num
                _ ≤ m ^ 2 := Nat.pow_le_pow_left (by omega) 2
            linarith
          · have e1 : (m % 10 + (Nat.digits 10 (m / 10)).sum) ^ 4
                ≤ 16 * (Nat.digits 10 (m / 10)).sum ^ 4 := by
              calc (m % 10 + (Nat.digits 10 (m / 10)).sum) ^ 4
                  ≤ (2 * (Nat.digits 10 (m / 10)).sum) ^ 4 := Nat.pow_le_pow_left (by omega) 4
                _ = 16 * (Nat.digits 10 (m / 10)).sum ^ 4 := by ring
            linarith
  have cancel : ∀ x y z : ℕ, x ∣ y → x ∣ y + z → x ∣ z := by
    rintro x y z ⟨p, rfl⟩ ⟨q, hq⟩
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · exact ⟨0, by simpa using hq⟩
    · have h5 : x * p ≤ x * q := Nat.le.intro hq
      obtain ⟨r, rfl⟩ := Nat.le.dest (Nat.le_of_mul_le_mul_left h5 hx)
      rw [Nat.mul_add] at hq
      exact ⟨r, Nat.add_left_cancel hq⟩
  have main : ∀ N S : ℕ, 0 < N → 0 < S → ¬ S ∣ N → N ^ 2 + S ^ 2 ∣ N ^ 4 + S ^ 4 →
      8 * N ^ 2 < S ^ 4 := by
    intro N S hN hS hnd hdvd
    obtain ⟨g, a, b, hgpos, hcop, rfl, rfl⟩ :
        ∃ g a b, 0 < g ∧ Nat.Coprime a b ∧ N = g * a ∧ S = g * b := by
      have hgpos : 0 < Nat.gcd N S :=
        Nat.pos_of_ne_zero fun h0 => by rw [Nat.gcd_eq_zero_iff] at h0; omega
      exact ⟨Nat.gcd N S, N / Nat.gcd N S, S / Nat.gcd N S, hgpos,
        Nat.coprime_div_gcd_div_gcd hgpos,
        (Nat.mul_div_cancel' (Nat.gcd_dvd_left N S)).symm,
        (Nat.mul_div_cancel' (Nat.gcd_dvd_right N S)).symm⟩
    have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hS)
    have hb2 : 2 ≤ b := by
      rcases Nat.lt_or_ge b 2 with h1 | h1
      · have hb1 : b = 1 := by omega
        subst hb1
        exact absurd ⟨a, by ring⟩ hnd
      · exact h1
    have h1 : (g * a) ^ 2 + (g * b) ^ 2 ∣ 2 * ((g * a) ^ 2 * (g * b) ^ 2) := by
      refine cancel _ ((g * a) ^ 4 + (g * b) ^ 4) _ hdvd ?_
      have e : ((g * a) ^ 4 + (g * b) ^ 4) + 2 * ((g * a) ^ 2 * (g * b) ^ 2)
          = ((g * a) ^ 2 + (g * b) ^ 2) ^ 2 := by ring
      rw [e]
      exact ⟨(g * a) ^ 2 + (g * b) ^ 2, by ring⟩
    have h2 : (g * a) ^ 2 + (g * b) ^ 2 ∣ 2 * (g * b) ^ 4 :=
      cancel _ (2 * ((g * a) ^ 2 * (g * b) ^ 2)) _ h1 ⟨2 * (g * b) ^ 2, by ring⟩
    have h4 : a ^ 2 + b ^ 2 ∣ 2 * g ^ 2 * b ^ 4 := by
      obtain ⟨c, hc⟩ := h2
      refine ⟨c, Nat.eq_of_mul_eq_mul_left (pow_pos hgpos 2) ?_⟩
      calc g ^ 2 * (2 * g ^ 2 * b ^ 4) = 2 * (g * b) ^ 4 := by ring
        _ = ((g * a) ^ 2 + (g * b) ^ 2) * c := hc
        _ = g ^ 2 * ((a ^ 2 + b ^ 2) * c) := by ring
    have hcop1 : Nat.Coprime (a ^ 2 + b ^ 2) b := by
      have h5 : Nat.gcd (a ^ 2) b = 1 := Nat.Coprime.pow_left 2 hcop
      have hd1 : Nat.gcd (a ^ 2 + b ^ 2) b ∣ b := Nat.gcd_dvd_right _ _
      have hd3 : Nat.gcd (a ^ 2 + b ^ 2) b ∣ b ^ 2 := dvd_pow hd1 (by norm_num)
      have hd2 : Nat.gcd (a ^ 2 + b ^ 2) b ∣ b ^ 2 + a ^ 2 := by
        have e : b ^ 2 + a ^ 2 = a ^ 2 + b ^ 2 := by ring
        rw [e]; exact Nat.gcd_dvd_left _ _
      have hd4 : Nat.gcd (a ^ 2 + b ^ 2) b ∣ a ^ 2 := cancel _ (b ^ 2) (a ^ 2) hd3 hd2
      have hd5 : Nat.gcd (a ^ 2 + b ^ 2) b ∣ 1 := by
        have h7 := Nat.dvd_gcd hd4 hd1
        rwa [h5] at h7
      show Nat.gcd (a ^ 2 + b ^ 2) b = 1
      exact Nat.dvd_one.mp hd5
    have hcop2 : Nat.Coprime (a ^ 2 + b ^ 2) (b ^ 4) := Nat.Coprime.pow_right 4 hcop1
    have h7 : a ^ 2 + b ^ 2 ≤ 2 * g ^ 2 := by
      refine Nat.le_of_dvd ?_ (Nat.Coprime.dvd_of_dvd_mul_right hcop2 h4)
      have := pow_pos hgpos 2; omega
    have hbb : 4 ≤ b ^ 2 := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ b ^ 2 := Nat.pow_le_pow_left hb2 2
    have hb4 : 16 ≤ b ^ 4 := by
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ b ^ 4 := Nat.pow_le_pow_left hb2 4
    have hg1 : 1 ≤ g ^ 2 := Nat.one_le_pow _ _ hgpos
    have step1 : 8 * g ^ 2 * (a ^ 2 + 4) ≤ 8 * g ^ 2 * (2 * g ^ 2) :=
      Nat.mul_le_mul le_rfl (by linarith)
    have step2 : g ^ 4 * 16 ≤ g ^ 4 * b ^ 4 := Nat.mul_le_mul le_rfl hb4
    nlinarith [step1, step2, hg1]
  have hs0 : 0 < (Nat.digits 10 n).sum := pos n n (pow10 n) hn
  have hbig := main n _ hn hs0 hcon h
  have hle : n ≤ 257 := by
    by_contra hgt
    have hd := dig n n (pow10 n) (by omega)
    linarith
  clear hbig hs0
  revert h hcon
  interval_cases n <;> norm_num
```
