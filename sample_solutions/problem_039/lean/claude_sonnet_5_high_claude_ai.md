# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `14 September 2026`\
Line count: `56`\
Turn count: `1 + external edit`

## Note

The model's output lacked `import Mathlib` at the top, causing errors.

## Fixed solution

```lean4
import Mathlib

theorem infinite_tan_zero_iff_rat (x : ℝ) :
    Set.Infinite { n : ℕ | n > 0 ∧ Real.tan ((n : ℝ) * Real.pi * x) = 0 } ↔ ∃ q : ℚ, x = q := by
  constructor
  · intro hinf
    obtain ⟨n, hpos, htan⟩ := hinf.nonempty
    rw [Real.tan_eq_sin_div_cos, div_eq_zero_iff] at htan
    have hsin2 : Real.sin (2 * ((n : ℝ) * Real.pi * x)) = 0 := by
      rw [Real.sin_two_mul]
      rcases htan with h | h <;> rw [h] <;> ring
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin2
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    have h2n0 : (2 * (n : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero hn0
    have heq : (k : ℝ) = 2 * (n : ℝ) * x := by
      have h2 : (k : ℝ) * Real.pi = (2 * (n : ℝ) * x) * Real.pi := by
        first
        | linear_combination hk
        | linear_combination -hk
      exact mul_right_cancel₀ Real.pi_ne_zero h2
    refine ⟨(k : ℚ) / (2 * (n : ℚ)), ?_⟩
    push_cast
    rw [eq_div_iff h2n0]
    linear_combination -heq
  · rintro ⟨q, rfl⟩
    have hd_pos : 0 < q.den := by
      first
      | exact q.den_pos
      | exact Nat.pos_of_ne_zero q.den_nz
    have hd0 : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
    have hqd : (q.num : ℝ) = (q : ℝ) * (q.den : ℝ) := by
      have h : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := by exact_mod_cast Rat.num_div_den q
      rw [div_eq_iff hd0] at h
      exact h
    have hinj : Function.Injective (fun m : ℕ => q.den * (m + 1)) := by
      intro a b hab
      have h := mul_left_cancel₀ hd_pos.ne' hab
      omega
    have hmem : ∀ m : ℕ, (fun m : ℕ => q.den * (m + 1)) m ∈
        { n : ℕ | n > 0 ∧ Real.tan ((n : ℝ) * Real.pi * (q : ℝ)) = 0 } := by
      intro m
      simp only [Set.mem_setOf_eq]
      refine ⟨mul_pos hd_pos (Nat.succ_pos m), ?_⟩
      rw [Real.tan_eq_sin_div_cos]
      have hcast : (↑(q.den * (m + 1)) : ℝ) * Real.pi * (q : ℝ)
          = (((↑(m + 1) : ℤ) * q.num : ℤ) : ℝ) * Real.pi := by
        push_cast
        rw [hqd]
        ring
      have hsin : Real.sin ((↑(q.den * (m + 1)) : ℝ) * Real.pi * (q : ℝ)) = 0 := by
        rw [hcast]
        exact Real.sin_eq_zero_iff.mpr ⟨(↑(m + 1) : ℤ) * q.num, rfl⟩
      rw [hsin, zero_div]
    have hrange : (Set.range (fun m : ℕ => q.den * (m + 1))).Infinite :=
      Set.infinite_range_of_injective hinj
    exact hrange.mono (Set.range_subset_iff.mpr hmem)
```
