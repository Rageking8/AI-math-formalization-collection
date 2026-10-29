# Claude Fable 5 (Arena AI)

Model: `claude-fable-5` (via Arena AI)\
Date: `2 August 2026`\
Line count: `46`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_distinct_irreducible_two_over_n_sum :
    ¬ ∃ (S : Finset ℕ), (∀ n ∈ S, n > 0 ∧ Nat.Coprime 2 n) ∧
      (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) = 5 / 121 := by
  rintro ⟨S, hS, hsum⟩
  -- Key claim: any such sum can be written as 2*m/d with d odd and positive
  have key : ∀ (T : Finset ℕ), (∀ n ∈ T, n > 0 ∧ Nat.Coprime 2 n) →
      ∃ (m : ℤ) (d : ℕ), Odd d ∧ 0 < d ∧
        (∑ n ∈ T, (2 : ℚ) / (n : ℚ)) = 2 * (m : ℚ) / (d : ℚ) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨0, 1, odd_one, Nat.one_pos, by simp⟩
    | @insert a T ha ih =>
        intro hT
        obtain ⟨m, d, hdodd, hdpos, hEq⟩ :=
          ih (fun n hn => hT n (Finset.mem_insert_of_mem hn))
        obtain ⟨hapos, hacop⟩ := hT a (Finset.mem_insert_self a T)
        have h2 : ¬ (2 ∣ a) := (Nat.prime_two.coprime_iff_not_dvd).mp hacop
        have haodd : Odd a := by
          rcases Nat.even_or_odd a with he | ho
          · exact absurd he.two_dvd h2
          · exact ho
        have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hapos.ne'
        have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
        refine ⟨(d : ℤ) + m * (a : ℤ), a * d, haodd.mul hdodd,
          Nat.mul_pos hapos hdpos, ?_⟩
        rw [Finset.sum_insert ha, hEq, div_add_div _ _ ha0 hd0,
          div_eq_div_iff (mul_ne_zero ha0 hd0)
            (Nat.cast_ne_zero.mpr (Nat.mul_pos hapos hdpos).ne' :
              ((a * d : ℕ) : ℚ) ≠ 0)]
        push_cast
        ring
  obtain ⟨m, d, hdodd, hdpos, hEq⟩ := key S hS
  rw [hEq] at hsum
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  rw [div_eq_div_iff hd0 (by norm_num : (121 : ℚ) ≠ 0)] at hsum
  -- hsum : 2 * m * 121 = 5 * d  in ℚ; transfer to ℤ
  have hz : (2 * m * 121 : ℤ) = 5 * (d : ℤ) := by exact_mod_cast hsum
  obtain ⟨k, hk⟩ := hdodd
  have hk' : (d : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  have h5 : (5 : ℤ) * (d : ℤ) = 10 * (k : ℤ) + 5 := by rw [hk']; ring
  have h242 : (242 : ℤ) * m = 10 * (k : ℤ) + 5 := by linarith
  omega
```
