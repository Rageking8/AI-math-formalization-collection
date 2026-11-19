# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `15 November 2026`\
Line count: `104`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def IsEgyptianFractionDecomp (q : ℚ) (l : List ℕ) : Prop :=
  l.Pairwise (· < ·) ∧ (∀ x ∈ l, 2 ≤ x) ∧ (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = q

theorem egyptian_fraction_311_457_tight_lower_bound :
    (∀ l : List ℕ, IsEgyptianFractionDecomp (311 / 457) l → ∃ n ∈ l, 3199 ≤ n) ∧
      (∃ l : List ℕ, IsEgyptianFractionDecomp (311 / 457) l ∧ ∀ n ∈ l, n ≤ 3199) := by
  constructor
  · rintro l ⟨hpair, hge, hsum⟩
    by_contra hcon0
    have hcon : ∀ n ∈ l, n < 3199 := by
      intro n hn
      by_contra hlt
      exact hcon0 ⟨n, hn, by omega⟩
    -- Sums of unit fractions with denominators prime to 457 have denominator prime to 457.
    have key : ∀ t : Finset ℕ, (∀ n ∈ t, ¬ 457 ∣ n) →
        ∃ N : ℤ, ∃ D : ℕ, ¬ 457 ∣ D ∧ ∑ n ∈ t, (1 : ℚ) / (n : ℚ) = (N : ℚ) / (D : ℚ) := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · intro _
        exact ⟨0, 1, by norm_num, by simp⟩
      · intro a t ha ih h
        obtain ⟨N, D, hD, hs⟩ := ih (fun n hn => h n (Finset.mem_insert_of_mem hn))
        have ha' : ¬ 457 ∣ a := h a (Finset.mem_insert_self a t)
        refine ⟨N * a + D, D * a, ?_, ?_⟩
        · intro hdvd
          rcases (Nat.Prime.dvd_mul (by norm_num)).1 hdvd with h1 | h1
          · exact hD h1
          · exact ha' h1
        · rw [Finset.sum_insert ha, hs]
          have hD0 : (D : ℚ) ≠ 0 := by
            intro h0
            apply hD
            have : D = 0 := by exact_mod_cast h0
            simp [this]
          have ha0 : (a : ℚ) ≠ 0 := by
            intro h0
            apply ha'
            have : a = 0 := by exact_mod_cast h0
            simp [this]
          push_cast
          field_simp
          ring
    have hnodup : l.Nodup := hpair.imp (fun h => Nat.ne_of_lt h)
    have hsum' : ∑ n ∈ l.toFinset, (1 : ℚ) / (n : ℚ) = 311 / 457 := by
      rw [List.sum_toFinset _ hnodup]
      exact hsum
    rw [← Finset.sum_filter_add_sum_filter_not l.toFinset (fun n => 457 ∣ n)] at hsum'
    -- the part with denominators prime to 457
    obtain ⟨N, D, hD, hs1⟩ := key (l.toFinset.filter (fun n => ¬ 457 ∣ n)) (by
      intro n hn
      exact (Finset.mem_filter.1 hn).2)
    -- the part with denominators divisible by 457
    have hsub : l.toFinset.filter (fun n => 457 ∣ n) ⊆
        ({457, 914, 1371, 1828, 2285, 2742} : Finset ℕ) := by
      intro n hn
      rw [Finset.mem_filter, List.mem_toFinset] at hn
      obtain ⟨hnl, k, rfl⟩ := hn
      have h1 := hge _ hnl
      have h2 := hcon _ hnl
      have hk1 : 1 ≤ k := by omega
      have hk6 : k ≤ 6 := by omega
      interval_cases k <;> simp
    have hs2 : ∑ n ∈ l.toFinset.filter (fun n => 457 ∣ n), (1 : ℚ) / (n : ℚ)
        = ((∑ n ∈ l.toFinset.filter (fun n => 457 ∣ n), 27420 / n : ℕ) : ℚ) / 27420 := by
      rw [Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hn' := hsub hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn'
      rcases hn' with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hT : ∑ n ∈ l.toFinset.filter (fun n => 457 ∣ n), 27420 / n ≤ 147 := by
      calc ∑ n ∈ l.toFinset.filter (fun n => 457 ∣ n), 27420 / n
          ≤ ∑ n ∈ ({457, 914, 1371, 1828, 2285, 2742} : Finset ℕ), 27420 / n :=
            Finset.sum_le_sum_of_subset hsub
        _ = 147 := by decide
    rw [hs1, hs2] at hsum'
    generalize (∑ n ∈ l.toFinset.filter (fun n => 457 ∣ n), 27420 / n) = T at hsum' hT
    have hD0 : (D : ℚ) ≠ 0 := by
      intro h0
      apply hD
      have : D = 0 := by exact_mod_cast h0
      simp [this]
    have h1 : (N : ℚ) / (D : ℚ) = 311 / 457 - (T : ℚ) / 27420 := by linarith
    have h2 := (div_eq_iff hD0).1 h1
    have hQ : ((18660 : ℚ) - (T : ℚ)) * (D : ℚ) = 457 * (60 * (N : ℚ)) := by
      rw [h2]
      ring
    have hZ : ((18660 : ℤ) - (T : ℤ)) * (D : ℤ) = 457 * (60 * N) := by
      have hc : ((((18660 : ℤ) - (T : ℤ)) * (D : ℤ) : ℤ) : ℚ) = ((457 * (60 * N) : ℤ) : ℚ) := by
        push_cast
        exact hQ
      exact Int.cast_injective hc
    have hdvd : ((457 : ℕ) : ℤ) ∣ ((18660 : ℤ) - (T : ℤ)) * (D : ℤ) :=
      ⟨60 * N, by rw [hZ]; norm_num⟩
    rcases Int.Prime.dvd_mul' (by norm_num) hdvd with h | h
    · omega
    · omega
  · refine ⟨[2, 7, 28, 914, 1828, 3199], ⟨?_, ?_, ?_⟩, ?_⟩
    · decide
    · decide
    · norm_num
    · decide
```
