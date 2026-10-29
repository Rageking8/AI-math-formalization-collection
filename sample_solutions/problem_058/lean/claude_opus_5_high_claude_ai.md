# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `17 August 2026`\
Line count: `107`\
Turn count: `2`

## Solution

```lean4
import Mathlib

open BigOperators

theorem no_pos_int_satisfies_digit_sum_eq :
    ¬ ∃ (n : ℕ), 1 < n ∧
      (1 / (n : ℝ)) * (∑ k ∈ Finset.Icc 1 n, ((Nat.digits 10 k).length : ℝ)) =
      ((Nat.digits 10 n).length : ℝ) - 1 / ((n : ℝ) ^ (1 / 4 : ℝ) - 1) := by
  rintro ⟨n, hn, heq⟩
  have hn2 : 2 ≤ n := by omega
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have hn0' : (n:ℝ) ≠ 0 := ne_of_gt hn0
  obtain ⟨D, hD⟩ : ∃ D, (Nat.digits 10 n).length = D := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, (∑ k ∈ Finset.Icc 1 n, (Nat.digits 10 k).length) = S := ⟨_, rfl⟩
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, (n:ℝ) ^ (1/4 : ℝ) = x := ⟨_, rfl⟩
  have hsumcast : (∑ k ∈ Finset.Icc 1 n, ((Nat.digits 10 k).length : ℝ)) = (S : ℝ) := by
    rw [← hS]; push_cast; try ring
  rw [hD, hxdef, hsumcast] at heq
  have hxnn : (0:ℝ) ≤ x := by rw [← hxdef]; positivity
  have hx4 : x ^ (4:ℕ) = (n:ℝ) := by
    have h1 : x * x = (n:ℝ) ^ (1/2 : ℝ) := by
      rw [← hxdef, ← Real.rpow_add hn0]; norm_num
    have h2 : x ^ (4:ℕ) = (x*x)*(x*x) := by ring
    rw [h2, h1, ← Real.rpow_add hn0]; norm_num
  have hx1 : 1 < x := by
    by_contra hcon
    push_neg at hcon
    have hxx : (0:ℝ) ≤ x * x := mul_nonneg hxnn hxnn
    have ha : x * x ≤ 1 := by nlinarith
    have hb : (x*x) * (x*x) ≤ 1 := by nlinarith
    have hc : (n:ℝ) = (x*x)*(x*x) := by rw [← hx4]; ring
    linarith
  have hxm1 : (0:ℝ) < x - 1 := by linarith
  have hx0' : x - 1 ≠ 0 := ne_of_gt hxm1
  have hSle : S ≤ n * D := by
    rw [← hS, ← hD]
    calc (∑ k ∈ Finset.Icc 1 n, (Nat.digits 10 k).length)
        ≤ ∑ _k ∈ Finset.Icc 1 n, (Nat.digits 10 n).length :=
          Finset.sum_le_sum (fun k hk => Nat.le_digits_len_le 10 k n (Finset.mem_Icc.mp hk).2)
      _ = n * (Nat.digits 10 n).length := by
          rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]
  obtain ⟨T, hT⟩ : ∃ T, n * D - S = T := ⟨_, rfl⟩
  have hTcast : (T:ℝ) = (n:ℝ) * (D:ℝ) - (S:ℝ) := by
    rw [← hT, Nat.cast_sub hSle]; push_cast; try ring
  have c1 : (1/(n:ℝ)) * (n:ℝ) = 1 := one_div_mul_cancel hn0'
  have c2 : (1/(x-1)) * (x-1) = 1 := one_div_mul_cancel hx0'
  have h3 : (S:ℝ) * (x-1) = (D:ℝ)*(n:ℝ)*(x-1) - (n:ℝ) := by
    calc (S:ℝ) * (x-1) = ((1/(n:ℝ)) * (n:ℝ)) * ((S:ℝ)*(x-1)) := by rw [c1]; ring
      _ = ((1/(n:ℝ)) * (S:ℝ)) * ((n:ℝ)*(x-1)) := by ring
      _ = ((D:ℝ) - 1/(x-1)) * ((n:ℝ)*(x-1)) := by rw [heq]
      _ = (D:ℝ)*(n:ℝ)*(x-1) - ((1/(x-1))*(x-1))*(n:ℝ) := by ring
      _ = (D:ℝ)*(n:ℝ)*(x-1) - (n:ℝ) := by rw [c2]; ring
  have key : (n:ℝ) = (T:ℝ) * (x - 1) := by rw [hTcast]; linarith
  have hTnn : (0:ℝ) ≤ (T:ℝ) := Nat.cast_nonneg T
  have hTne : (T:ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at key
    linarith
  have hTpos : (0:ℝ) < (T:ℝ) := lt_of_le_of_ne hTnn (Ne.symm hTne)
  have hxval : x = ((T:ℝ) + (n:ℝ))/(T:ℝ) := by
    field_simp
    linarith
  have hmem : x ∈ Set.range ((↑) : ℚ → ℝ) :=
    ⟨((T:ℚ) + (n:ℚ))/(T:ℚ), by push_cast; rw [hxval]⟩
  have hnotirr : ¬ Irrational x := fun hirr => hirr hmem
  have hx4' : x ^ (4:ℕ) = ((n:ℤ):ℝ) := by rw [hx4]; simp
  obtain ⟨y, hy⟩ : ∃ y : ℤ, x = y := by
    by_contra hcon
    exact hnotirr (irrational_nrt_of_notint_nrt 4 (n:ℤ) hx4' hcon (by norm_num))
  have hy1 : (1:ℝ) < (y:ℝ) := by rw [← hy]; exact hx1
  have hy2 : (2:ℤ) ≤ y := by
    have h : (1:ℤ) < y := by exact_mod_cast hy1
    omega
  have hnEq : y^4 = (n:ℤ) := by
    have h : ((y:ℝ))^(4:ℕ) = (n:ℝ) := by rw [← hy]; exact hx4
    exact_mod_cast h
  have hkeyZ : (n:ℤ) = (T:ℤ) * (y - 1) := by
    have h : (n:ℝ) = (T:ℝ) * ((y:ℝ) - 1) := by rw [← hy]; exact key
    exact_mod_cast h
  have hy4 : y^4 = (T:ℤ) * (y - 1) := by rw [hnEq]; exact hkeyZ
  have hdvd : (y - 1) ∣ (1:ℤ) := ⟨(T:ℤ) - (y^3+y^2+y+1), by linear_combination hy4⟩
  have hyle : y - 1 ≤ 1 := Int.le_of_dvd one_pos hdvd
  have hyEq : y = 2 := by omega
  have hnZ : (n:ℤ) = 16 := by rw [← hnEq, hyEq]; norm_num
  have hn16 : n = 16 := by exact_mod_cast hnZ
  have hT16 : T = 16 := by
    have ha : (n:ℤ) = (T:ℤ) := by rw [hkeyZ, hyEq]; ring
    have hb : (T:ℤ) = 16 := by rw [← ha]; exact hnZ
    exact_mod_cast hb
  subst hn16
  have hD2 : D = 2 := by rw [← hD]; norm_num
  rw [hD2, hT16] at hT
  have hS16 : S = 16 := by omega
  have hone : ∀ k ∈ Finset.Icc 1 16, (1:ℕ) ≤ (Nat.digits 10 k).length := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hmono := Nat.le_digits_len_le 10 1 k hk.1
    have h1 : (Nat.digits 10 1).length = 1 := by norm_num
    omega
  have hten : ∃ i ∈ Finset.Icc 1 16, (1:ℕ) < (Nat.digits 10 i).length :=
    ⟨10, by simp, by norm_num⟩
  have hlt : (∑ _k ∈ Finset.Icc 1 16, (1:ℕ)) < ∑ k ∈ Finset.Icc 1 16, (Nat.digits 10 k).length :=
    Finset.sum_lt_sum hone hten
  have hcard : (∑ _k ∈ Finset.Icc 1 16, (1:ℕ)) = 16 := by simp
  rw [hcard, hS] at hlt
  omega
```
