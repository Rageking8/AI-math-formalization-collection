# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `29 July 2026`\
Line count: `48`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_distinct_irreducible_two_over_n_sum :
    ¬ ∃ (S : Finset ℕ), (∀ n ∈ S, n > 0 ∧ Nat.Coprime 2 n) ∧
      (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) = 5 / 121 := by
  rintro ⟨S, hS, hsum⟩
  have key : ∀ T : Finset ℕ, (∀ n ∈ T, n > 0 ∧ Nat.Coprime 2 n) →
      ∃ a b : ℤ, (∃ l : ℤ, b = 2 * l + 1) ∧
        (∑ n ∈ T, (2 : ℚ) / (n : ℚ)) = 2 * (a : ℚ) / (b : ℚ) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨0, 1, ⟨0, by norm_num⟩, by simp⟩
    | @insert m T hm ih =>
        intro h
        obtain ⟨a, b, ⟨l, hl⟩, hEq⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
        obtain ⟨hmpos, hmcop⟩ := h m (Finset.mem_insert_self m T)
        have h1 : Nat.gcd 2 m = 1 := hmcop
        have h2 : m % 2 = 1 := by
          rcases Nat.even_or_odd m with he | ho
          · exfalso
            obtain ⟨c, hc⟩ := he
            have hd : 2 ∣ m := ⟨c, by omega⟩
            have h4 := Nat.gcd_eq_left hd
            omega
          · exact Nat.odd_iff.mp ho
        have h3 : m = 2 * (m / 2) + 1 := by omega
        have hk : (m : ℤ) = 2 * ((m / 2 : ℕ) : ℤ) + 1 := by exact_mod_cast h3
        have hmn : m ≠ 0 := by omega
        have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hmn
        have hbz : b ≠ 0 := by omega
        have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hbz
        refine ⟨b + a * (m : ℤ), (m : ℤ) * b,
          ⟨2 * ((m / 2 : ℕ) : ℤ) * l + ((m / 2 : ℕ) : ℤ) + l, by rw [hk, hl]; ring⟩, ?_⟩
        rw [Finset.sum_insert hm, hEq]
        push_cast
        rw [div_add_div _ _ hm0 hb0,
          div_eq_div_iff (mul_ne_zero hm0 hb0) (mul_ne_zero hm0 hb0)]
        ring
  obtain ⟨a, b, ⟨l, hl⟩, hEq⟩ := key S hS
  rw [hEq] at hsum
  have hbz : b ≠ 0 := by omega
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hbz
  rw [div_eq_div_iff hb0 (by norm_num : (121 : ℚ) ≠ 0)] at hsum
  have hz : (2 * a * 121 : ℤ) = 5 * b := by exact_mod_cast hsum
  have hz2 : 242 * a = 5 * b := by linear_combination hz
  omega
```
