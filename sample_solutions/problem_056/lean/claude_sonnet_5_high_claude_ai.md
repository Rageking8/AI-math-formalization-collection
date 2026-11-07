# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `23 September 2026`\
Line count: `175`\
Turn count: `3 + external edit`

## Note

This solution uses `native_decide`. The model's output lacked `import Mathlib` at the top, causing errors. The conversation contained 1 "Continue" message not included in the turn count.

## Fixed solution

```lean4
import Mathlib

theorem digit_sum_divides (n : ℕ) (hn : 0 < n)
    (h : n ^ 2 + (Nat.digits 10 n).sum ^ 2 ∣ n ^ 4 + (Nat.digits 10 n).sum ^ 4) :
      (Nat.digits 10 n).sum ∣ n := by
  -- Helper 1: digit-sum / digit-length facts, proved by strong induction.
  have digit_bound : ∀ m : ℕ, 0 < m →
      (Nat.digits 10 m).sum ≤ 9 * (Nat.digits 10 m).length ∧
      10 ^ (Nat.digits 10 m).length ≤ 10 * m ∧
      m < 10 ^ (Nat.digits 10 m).length ∧
      0 < (Nat.digits 10 m).sum := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro hm
      have hdig : Nat.digits 10 m = m % 10 :: Nat.digits 10 (m / 10) :=
        Nat.digits_def' (by norm_num) hm
      rcases Nat.eq_zero_or_pos (m / 10) with hz | hpos
      · have hm10 : m < 10 := by
          have hdm : 10 * (m / 10) + m % 10 = m := Nat.div_add_mod m 10
          have hmlt : m % 10 < 10 := Nat.mod_lt m (by norm_num)
          omega
        have hdig0 : Nat.digits 10 (m / 10) = [] := by rw [hz]; exact Nat.digits_zero 10
        rw [hdig, hdig0]
        have hmod : m % 10 = m := Nat.mod_eq_of_lt hm10
        simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, pow_one]
        rw [hmod]
        omega
      · have hlt : m / 10 < m := Nat.div_lt_self hm (by norm_num)
        obtain ⟨ih1, ih2, ih3, ih4⟩ := IH (m / 10) hlt hpos
        rw [hdig]
        simp only [List.sum_cons, List.length_cons]
        have hmod_lt : m % 10 < 10 := Nat.mod_lt m (by norm_num)
        have hdm : 10 * (m / 10) + m % 10 = m := Nat.div_add_mod m 10
        have hpe : (10:ℕ) ^ ((Nat.digits 10 (m/10)).length + 1)
                  = 10 * 10 ^ (Nat.digits 10 (m/10)).length := by ring
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · rw [hpe]; omega
        · rw [hpe]; omega
        · omega
  -- Helper 2: coprimality of a²+b² with b² (and, by symmetry, with a²).
  have coprime_add_sq_right : ∀ a b : ℕ, Nat.Coprime a b → Nat.Coprime (a^2+b^2) (b^2) := by
    intro a b hab
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpsum : p ∣ a^2+b^2 := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpb2 : p ∣ b^2 := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hpa2 : p ∣ a^2 := by
      have hpsum' : p ∣ b^2 + a^2 := by rw [Nat.add_comm]; exact hpsum
      exact (Nat.dvd_add_right hpb2).mp hpsum'
    have hpb : p ∣ b := hp.dvd_of_dvd_pow hpb2
    have hpa : p ∣ a := hp.dvd_of_dvd_pow hpa2
    have hcommon : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
    rw [hab] at hcommon
    exact hp.one_lt.ne' (Nat.dvd_one.mp hcommon)
  have coprime_add_sq_left : ∀ a b : ℕ, Nat.Coprime a b → Nat.Coprime (a^2+b^2) (a^2) := by
    intro a b hab
    have h1 := coprime_add_sq_right b a hab.symm
    have h2 : b^2+a^2 = a^2+b^2 := by ring
    rwa [h2] at h1
  -- Helper 3: exponential beats quartic, for the length bound.
  have growth : ∀ j : ℕ, 1312200 * (j+5)^4 < 10^(2*(j+5)) := by
    intro j
    induction j with
    | zero => norm_num
    | succ k ih =>
      have hb : (k+1+5) ≤ 2*(k+5) := by omega
      have h1 : (k+1+5)^4 ≤ (2*(k+5))^4 := Nat.pow_le_pow_left hb 4
      have h2 : (2*(k+5):ℕ)^4 = 16*(k+5)^4 := by ring
      have h16 : (k+1+5)^4 ≤ 16*(k+5)^4 := by rw [h2] at h1; exact h1
      have h100 : (16:ℕ)*(k+5)^4 ≤ 100*(k+5)^4 := by
        have : (16:ℕ) ≤ 100 := by norm_num
        exact Nat.mul_le_mul this (le_refl _)
      have hfin : (k+1+5)^4 ≤ 100*(k+5)^4 := le_trans h16 h100
      have h5 : 1312200*(k+1+5)^4 ≤ 1312200*(100*(k+5)^4) :=
        Nat.mul_le_mul (le_refl _) hfin
      have h6 : (1312200:ℕ)*(100*(k+5)^4) = 100*(1312200*(k+5)^4) := by ring
      have h7 : (100:ℕ)*(1312200*(k+5)^4) < 100*10^(2*(k+5)) :=
        mul_lt_mul_of_pos_left ih (by norm_num)
      have h8 : (100:ℕ)*10^(2*(k+5)) = 10^(2*(k+1+5)) := by ring
      calc 1312200*(k+1+5)^4 ≤ 1312200*(100*(k+5)^4) := h5
        _ = 100*(1312200*(k+5)^4) := h6
        _ < 100*10^(2*(k+5)) := h7
        _ = 10^(2*(k+1+5)) := h8
  -- Now the main argument.
  set s := (Nat.digits 10 n).sum with hs_def
  obtain ⟨hs_le, hlen_lb, hn_ub, hs_pos⟩ := digit_bound n hn
  rw [← hs_def] at hs_le hs_pos
  set L := (Nat.digits 10 n).length with hL_def
  -- Step 1: n²+s² ∣ 2n²s².
  have hsq_eq : (n^2+s^2)^2 = (n^4+s^4) + 2*n^2*s^2 := by ring
  have hdvd1 : n^2+s^2 ∣ (n^2+s^2)^2 := dvd_pow_self _ (by norm_num)
  rw [hsq_eq] at hdvd1
  have hdvd2 : n^2+s^2 ∣ 2*n^2*s^2 := (Nat.dvd_add_right h).mp hdvd1
  -- Step 2: gcd decomposition.
  set g := Nat.gcd n s with hg_def
  have hg_pos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | hpos
    · exfalso; rw [hg_def] at h0
      have := Nat.gcd_eq_zero_iff.mp h0
      omega
    · exact hpos
  set n' := n / g with hn'_def
  set s' := s / g with hs'_def
  have hcop : Nat.Coprime n' s' := Nat.coprime_div_gcd_div_gcd hg_pos
  have hn_eq : n = g * n' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n s)).symm
  have hs_eq : s = g * s' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right n s)).symm
  have hn2s2_eq : n^2+s^2 = g^2*(n'^2+s'^2) := by rw [hn_eq, hs_eq]; ring
  have h2n2s2_eq : 2*n^2*s^2 = g^2*(2*g^2*n'^2*s'^2) := by rw [hn_eq, hs_eq]; ring
  have hdvd3 : g^2*(n'^2+s'^2) ∣ g^2*(2*g^2*n'^2*s'^2) := by
    rw [← hn2s2_eq, ← h2n2s2_eq]; exact hdvd2
  obtain ⟨t, ht⟩ := hdvd3
  have hg2_pos : 0 < g^2 := by positivity
  have ht2 : g^2*(2*g^2*n'^2*s'^2) = g^2*((n'^2+s'^2)*t) := by rw [ht]; ring
  have ht3 : 2*g^2*n'^2*s'^2 = (n'^2+s'^2)*t := Nat.eq_of_mul_eq_mul_left hg2_pos ht2
  have hdvd4 : n'^2+s'^2 ∣ 2*g^2*n'^2*s'^2 := ⟨t, ht3⟩
  have hcopL : Nat.Coprime (n'^2+s'^2) (n'^2) := coprime_add_sq_left n' s' hcop
  have hcopR : Nat.Coprime (n'^2+s'^2) (s'^2) := coprime_add_sq_right n' s' hcop
  have hcopP : Nat.Coprime (n'^2+s'^2) (n'^2*s'^2) := hcopL.mul_right hcopR
  have hdvd4' : n'^2+s'^2 ∣ (2*g^2)*(n'^2*s'^2) := by
    have heq : 2*g^2*n'^2*s'^2 = (2*g^2)*(n'^2*s'^2) := by ring
    rwa [heq] at hdvd4
  have hkey : n'^2+s'^2 ∣ 2*g^2 := hcopP.dvd_of_dvd_mul_right hdvd4'
  have hle : n'^2+s'^2 ≤ 2*g^2 := Nat.le_of_dvd (by positivity) hkey
  have hn'2_le : n'^2 ≤ 2*g^2 := by omega
  have hn2_eq : n^2 = g^2*n'^2 := by rw [hn_eq]; ring
  have hn2_le4 : n^2 ≤ 2*g^4 := by
    rw [hn2_eq]
    have step : g^2*n'^2 ≤ g^2*(2*g^2) := Nat.mul_le_mul (le_refl _) hn'2_le
    calc g^2*n'^2 ≤ g^2*(2*g^2) := step
      _ = 2*g^4 := by ring
  have hg_le_s : g ≤ s := Nat.le_of_dvd hs_pos (by rw [hg_def]; exact Nat.gcd_dvd_right n s)
  have hg4_le_s4 : g^4 ≤ s^4 := Nat.pow_le_pow_left hg_le_s 4
  have hn2_le_s4 : n^2 ≤ 2*s^4 := by
    calc n^2 ≤ 2*g^4 := hn2_le4
      _ ≤ 2*s^4 := by omega
  -- Step 3: bound the digit-length L, hence bound n.
  have hL4 : L ≤ 4 := by
    by_contra hL_ge
    push_neg at hL_ge
    obtain ⟨j, hj⟩ : ∃ j, L = j+5 := ⟨L-5, by omega⟩
    rw [hj] at hs_le hlen_lb
    have e1 : (10:ℕ)^(2*(j+5)) ≤ 100*n^2 := by
      have hsqle : (10^(j+5):ℕ)^2 ≤ (10*n)^2 := Nat.pow_le_pow_left hlen_lb 2
      have heq1 : (10:ℕ)^(2*(j+5)) = (10^(j+5))^2 := by ring
      have heq2 : ((10:ℕ)*n)^2 = 100*n^2 := by ring
      rw [heq1, ← heq2]; exact hsqle
    have e2 : (100:ℕ)*n^2 ≤ 200*s^4 := by
      have hm := Nat.mul_le_mul (le_refl (100:ℕ)) hn2_le_s4
      calc (100:ℕ)*n^2 ≤ 100*(2*s^4) := hm
        _ = 200*s^4 := by ring
    have e3 : s^4 ≤ 6561*(j+5)^4 := by
      have hp := Nat.pow_le_pow_left hs_le 4
      calc s^4 ≤ (9*(j+5))^4 := hp
        _ = 6561*(j+5)^4 := by ring
    have e4 : (200:ℕ)*s^4 ≤ 1312200*(j+5)^4 := by
      have hm := Nat.mul_le_mul (le_refl (200:ℕ)) e3
      calc (200:ℕ)*s^4 ≤ 200*(6561*(j+5)^4) := hm
        _ = 1312200*(j+5)^4 := by ring
    have e5 : (10:ℕ)^(2*(j+5)) ≤ 1312200*(j+5)^4 :=
      calc (10:ℕ)^(2*(j+5)) ≤ 100*n^2 := e1
        _ ≤ 200*s^4 := e2
        _ ≤ 1312200*(j+5)^4 := e4
    exact absurd e5 (not_le.mpr (growth j))
  have hn_lt : n < 10000 := by
    calc n < 10^L := hn_ub
      _ ≤ 10^4 := Nat.pow_le_pow_right (by norm_num) hL4
      _ = 10000 := by norm_num
  -- Step 4: finite check.
  have key : ∀ m : ℕ, m < 10000 → 0 < m →
      (m^2 + (Nat.digits 10 m).sum^2 ∣ m^4 + (Nat.digits 10 m).sum^4) →
      (Nat.digits 10 m).sum ∣ m := by native_decide
  rw [hs_def]
  exact key n hn_lt hn h
```
