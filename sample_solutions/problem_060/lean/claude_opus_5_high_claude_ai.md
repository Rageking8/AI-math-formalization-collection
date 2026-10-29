# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `17 August 2026`\
Line count: `106`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem factorial_inequality (n : ℕ) (hn : 0 < n) :
    ((n.factorial.factorial : ℝ) / ((n ^ 2 - 1).factorial : ℝ) < (n : ℝ) ^ (n.factorial + n ^ 3)) ↔
      n = 2 ∨ n = 3 ∨ n = 4 := by
  -- `i ! * (i+1)^j ≤ (i+j)!`
  have pow_le : ∀ i j : ℕ, i.factorial * (i + 1) ^ j ≤ (i + j).factorial := by
    intro i j
    induction j with
    | zero => simp
    | succ k ih =>
      have h1 : i.factorial * (i + 1) ^ (k + 1) = i.factorial * (i + 1) ^ k * (i + 1) := by ring
      rw [h1]
      calc i.factorial * (i + 1) ^ k * (i + 1)
          ≤ (i + k).factorial * (i + k + 1) := Nat.mul_le_mul ih (by omega)
        _ = (i + k + 1).factorial := by rw [Nat.factorial_succ]; ring
        _ = (i + (k + 1)).factorial := by rw [← Nat.add_assoc]
  -- `m^3 + 2m^2 ≤ m!` for `m ≥ 6`
  have key : ∀ m : ℕ, 6 ≤ m → m ^ 3 + 2 * m ^ 2 ≤ m.factorial := by
    intro m
    induction m with
    | zero => exact fun h => absurd h (by norm_num)
    | succ k ih =>
      intro hk1
      rcases Nat.lt_or_ge k 6 with hk | hk
      · have hk5 : k = 5 := by omega
        subst hk5
        norm_num [Nat.factorial]
      · have h := ih hk
        have hstep : (k + 1) ^ 2 + 2 * (k + 1) ≤ k ^ 3 + 2 * k ^ 2 := by
          nlinarith [hk, Nat.mul_le_mul hk hk]
        calc (k + 1) ^ 3 + 2 * (k + 1) ^ 2
            = (k + 1) * ((k + 1) ^ 2 + 2 * (k + 1)) := by ring
          _ ≤ (k + 1) * (k ^ 3 + 2 * k ^ 2) := Nat.mul_le_mul (le_refl _) hstep
          _ ≤ (k + 1) * k.factorial := Nat.mul_le_mul (le_refl _) h
          _ = (k + 1).factorial := (Nat.factorial_succ k).symm
  have arith : ∀ A B F : ℕ, 1 ≤ A → B + 2 * A ≤ F →
      A - 1 ≤ F ∧ A - 1 + 1 = A ∧ F + B ≤ 2 * (F - (A - 1)) := by
    intro A B F h1 h2
    refine ⟨by omega, by omega, by omega⟩
  -- the reverse inequality for `m = 1` and `m ≥ 5`
  have hmain : ∀ m : ℕ, 0 < m → m ≠ 2 → m ≠ 3 → m ≠ 4 →
      m ^ (m.factorial + m ^ 3) * (m ^ 2 - 1).factorial ≤ m.factorial.factorial := by
    intro m hm h2 h3 h4
    rcases Nat.lt_or_ge m 5 with hlt | hge
    · have hm1 : m = 1 := by omega
      subst hm1
      norm_num [Nat.factorial]
    · rcases Nat.lt_or_ge m 6 with hlt6 | hge6
      · have hm5 : m = 5 := by omega
        subst hm5
        set_option maxRecDepth 40000 in
        first
          | norm_num [Nat.factorial]
          | decide
      · have hsq : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
        have hfac : m ^ 3 + 2 * m ^ 2 ≤ m.factorial := key m hge6
        obtain ⟨hle, hsq', hexp⟩ := arith (m ^ 2) (m ^ 3) m.factorial hsq hfac
        have h0 : (m ^ 2 - 1).factorial * (m ^ 2 - 1 + 1) ^ (m.factorial - (m ^ 2 - 1))
            ≤ (m ^ 2 - 1 + (m.factorial - (m ^ 2 - 1))).factorial := pow_le _ _
        rw [Nat.add_sub_cancel' hle, hsq'] at h0
        have hpow : m ^ (m.factorial + m ^ 3) ≤ (m ^ 2) ^ (m.factorial - (m ^ 2 - 1)) := by
          rw [← pow_mul]
          first
            | exact Nat.pow_le_pow_right hm hexp
            | exact Nat.pow_le_pow_right (by omega) hexp
        calc m ^ (m.factorial + m ^ 3) * (m ^ 2 - 1).factorial
            ≤ (m ^ 2) ^ (m.factorial - (m ^ 2 - 1)) * (m ^ 2 - 1).factorial :=
              Nat.mul_le_mul hpow (le_refl _)
          _ = (m ^ 2 - 1).factorial * (m ^ 2) ^ (m.factorial - (m ^ 2 - 1)) := Nat.mul_comm _ _
          _ ≤ m.factorial.factorial := h0
  -- the statement in ℕ
  have hNat : (n.factorial.factorial < n ^ (n.factorial + n ^ 3) * (n ^ 2 - 1).factorial)
      ↔ (n = 2 ∨ n = 3 ∨ n = 4) := by
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      obtain ⟨h2, h3, h4⟩ := hc
      have hcon := hmain n hn h2 h3 h4
      exact absurd (Nat.lt_of_lt_of_le h hcon) (Nat.lt_irrefl _)
    · set_option maxRecDepth 40000 in
      rintro (rfl | rfl | rfl) <;>
        first
          | norm_num [Nat.factorial]
          | decide
  -- transfer to ℝ
  have hpos : (0:ℝ) < ((n ^ 2 - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n ^ 2 - 1)
  have divlt : ∀ a b c : ℝ, 0 < b → (a / b < c ↔ a < c * b) := by
    intro a b c hb
    have hb' : b ≠ 0 := ne_of_gt hb
    have hcancel : a / b * b = a := by field_simp
    constructor
    · intro h
      have h2 := mul_lt_mul_of_pos_right h hb
      rwa [hcancel] at h2
    · intro h
      have h2 : a / b * b < c * b := by rw [hcancel]; exact h
      exact lt_of_mul_lt_mul_right h2 (le_of_lt hb)
  rw [← hNat, divlt _ _ _ hpos]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h
```
