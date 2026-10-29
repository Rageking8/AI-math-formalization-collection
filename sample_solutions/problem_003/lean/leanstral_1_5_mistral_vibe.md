# Leanstral 1.5 (Mistral Vibe)

Model: `Leanstral 1.5` (via Mistral Vibe)\
Date: `2 August 2026`\
Line count: `72`\
Turn count: `Not applicable`

## Solution

```lean4
import Mathlib

theorem no_distinct_irreducible_two_over_n_sum :
    ¬ ∃ (S : Finset ℕ), (∀ n ∈ S, n > 0 ∧ Nat.Coprime 2 n) ∧
      (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) = 5 / 121 := by
  intro h
  rcases h with ⟨S, hS, hsum⟩
  -- Each n in S is coprime to 2, hence not divisible by 2
  have h_odd : ∀ n ∈ S, ¬ 2 ∣ n := by
    intro n hn
    rcases hS n hn with ⟨_, hcop⟩
    intro h2dvd
    have hgcd : Nat.gcd 2 n = 2 := Nat.gcd_eq_left h2dvd
    have hgcd1 : Nat.gcd 2 n = 1 := Nat.Coprime.gcd_eq_one hcop
    rw [hgcd] at hgcd1
    norm_num at hgcd1
  -- Each n is positive
  have h_pos : ∀ n ∈ S, 0 < n := fun n hn => (hS n hn).1
  -- Product of all n in S
  let P := Finset.prod S id
  -- P is odd (not divisible by 2)
  have hP_odd : ¬ 2 ∣ P := by
    dsimp [P]
    have h_prod_odd : ∀ T : Finset ℕ, (∀ n ∈ T, ¬ 2 ∣ n) → ¬ 2 ∣ (Finset.prod T id) := by
      intro T hT
      induction' T using Finset.induction_on with a T' haT' ih
      · norm_num
      · intro h2
        rw [Finset.prod_insert haT'] at h2
        have ha_odd : ¬ 2 ∣ a := hT a (Finset.mem_insert_self a T')
        have hT'_odd : ∀ n ∈ T', ¬ 2 ∣ n := fun n hn => hT n (Finset.mem_insert_of_mem hn)
        rcases (Nat.prime_two.dvd_mul.mp h2) with (h | h)
        · exact ha_odd h
        · exact ih hT'_odd h
    exact h_prod_odd S h_odd
  -- From the sum equation, derive an integer equation
  have hsum_int : (∑ n ∈ S, (242 : ℤ) * (P / n : ℕ)) = (5 : ℤ) * (P : ℤ) := by
    -- Work in ℚ first, then convert to ℤ
    have h_eq_rat : (∑ n ∈ S, ((242 : ℚ) * ((P / n : ℕ) : ℚ))) = (5 : ℚ) * (P : ℚ) := by
      -- Rewrite P/n using Nat.cast_div
      have hLHS : (∑ n ∈ S, ((242 : ℚ) * ((P / n : ℕ) : ℚ))) = (∑ n ∈ S, ((242 : ℚ) * ((P : ℚ) / (n : ℚ)))) := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        have hn_dvd : n ∣ P := Finset.dvd_prod_of_mem id hn
        have hn_ne_zero : (n : ℚ) ≠ 0 := by exact_mod_cast (h_pos n hn).ne.symm
        rw [Nat.cast_div hn_dvd hn_ne_zero]
      rw [hLHS]
      -- Now show: ∑ 242*P/n = 121*P * ∑ 2/n
      have h242 : (242 : ℚ) = 2 * 121 := by norm_num
      calc
        (∑ n ∈ S, ((242 : ℚ) * ((P : ℚ) / (n : ℚ)))) = (121 : ℚ) * (P : ℚ) * (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) := by
          simp [Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, h242]
        _ = (121 : ℚ) * (P : ℚ) * (5 / 121) := by rw [hsum]
        _ = (5 : ℚ) * (P : ℚ) := by ring
    -- Now both sides are integer expressions cast to ℚ, so we can cast to ℤ
    exact_mod_cast h_eq_rat
  -- LHS is even (242 is even)
  have hLHS_even : 2 ∣ (∑ n ∈ S, (242 : ℤ) * (P / n : ℕ)) := by
    have h242_even : 2 ∣ (242 : ℤ) := by norm_num
    refine Finset.dvd_sum (fun n hn => ?_)
    exact h242_even.mul_right _
  -- RHS is odd (5 is odd, P is odd)
  have hRHS_odd : ¬ 2 ∣ (5 : ℤ) * (P : ℤ) := by
    have h5_odd : ¬ 2 ∣ (5 : ℤ) := by norm_num
    have hP_odd_int : ¬ 2 ∣ (P : ℤ) := by exact_mod_cast hP_odd
    intro h2
    have hprime : Prime (2 : ℤ) := by norm_num
    rcases hprime.dvd_or_dvd h2 with (h | h)
    · exact h5_odd h
    · exact hP_odd_int h
  -- Contradiction: LHS is even but RHS is odd
  rw [hsum_int] at hLHS_even
  exact hRHS_odd hLHS_even
```
