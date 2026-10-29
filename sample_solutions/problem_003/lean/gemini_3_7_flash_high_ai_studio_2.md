# Gemini 3.7 Flash High (AI Studio)

Model: `Gemini 3.7 Flash High` (via AI Studio)\
Date: `23 August 2026`\
Line count: `36`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_distinct_irreducible_two_over_n_sum :
    ¬ ∃ (S : Finset ℕ), (∀ n ∈ S, n > 0 ∧ Nat.Coprime 2 n) ∧
      (∑ n ∈ S, (2 : ℚ) / (n : ℚ)) = 5 / 121 := by
  rintro ⟨S, hS_odd, hS_sum⟩
  have h_prop : ∀ (T : Finset ℕ), (∀ n ∈ T, n > 0 ∧ Nat.Coprime 2 n) →
      ∃ (A B : ℕ), Odd B ∧ B > 0 ∧ (∑ n ∈ T, (2 : ℚ) / (n : ℚ)) = (2 * A : ℚ) / (B : ℚ) := by
    intro T
    refine Finset.induction_on T ?base ?step
    · intro _
      refine ⟨0, 1, ⟨0, rfl⟩, by omega, ?_⟩
      simp
    · intro a s ha ih h_all
      have ha_pos : a > 0 := (h_all a (Finset.mem_insert_self a s)).1
      have ha_coprime : Nat.Coprime 2 a := (h_all a (Finset.mem_insert_self a s)).2
      have ha_odd : Odd a := Nat.coprime_two_left.mp ha_coprime
      have hs_all : ∀ n ∈ s, n > 0 ∧ Nat.Coprime 2 n := fun n hn => h_all n (Finset.mem_insert_of_mem hn)
      obtain ⟨A, B, hB_odd, hB_pos, h_sum⟩ := ih hs_all
      refine ⟨A * a + B, B * a, Odd.mul hB_odd ha_odd, by positivity, ?_⟩
      rw [Finset.sum_insert ha, h_sum]
      have ha_ne : (a : ℚ) ≠ 0 := by positivity
      have hB_ne : (B : ℚ) ≠ 0 := by positivity
      push_cast
      field_simp [ha_ne, hB_ne]
      ring
  obtain ⟨A, B, hB_odd, hB_pos, h_sum⟩ := h_prop S hS_odd
  rw [hS_sum] at h_sum
  have hB_ne : (B : ℚ) ≠ 0 := by positivity
  have h_cross := (div_eq_div_iff (by norm_num) hB_ne).mp h_sum
  have h_nat : 5 * B = 2 * A * 121 := by
    apply Nat.cast_inj (R := ℚ).mp
    push_cast
    linear_combination h_cross
  rcases hB_odd with ⟨k, rfl⟩
  omega
```
