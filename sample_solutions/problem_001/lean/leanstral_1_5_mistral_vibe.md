# Leanstral 1.5 (Mistral Vibe)

Model: `Leanstral 1.5` (via Mistral Vibe)\
Date: `28 July 2026`\
Line count: `108`\
Turn count: `Not applicable`

## Solution

```lean4
import Mathlib

theorem ceil_pow_expr_odd (x : ℕ) :
    Odd ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ x⌉ := by
  let α : ℝ := ((5 : ℝ) + Real.sqrt 17) / 2
  let β : ℝ := ((5 : ℝ) - Real.sqrt 17) / 2
  have hβpos : 0 < β := by
    dsimp [β]
    have hsqrt : Real.sqrt 17 < 5 := by
      calc
        Real.sqrt 17 < Real.sqrt 25 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        _ = 5 := by norm_num
    linarith
  have hβlt1 : β < 1 := by
    dsimp [β]
    have hsqrt : 3 < Real.sqrt 17 := by
      calc
        3 = Real.sqrt 9 := by norm_num
        _ < Real.sqrt 17 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have h_add : α + β = 5 := by
    dsimp [α, β]
    ring
  have h_mul : α * β = 2 := by
    dsimp [α, β]
    have hsq : (Real.sqrt 17)^2 = 17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 from by norm_num)
    nlinarith
  have h_α_sq : α^2 = 5*α - 2 := by
    nlinarith
  have h_β_sq : β^2 = 5*β - 2 := by
    nlinarith
  -- define the integer sequence a_n by recurrence: a_0 = 2, a_1 = 5, a_{n+2} = 5*a_{n+1} - 2*a_n
  -- we use a function returning (a_n, a_{n+1})
  let f : ℕ → ℤ × ℤ :=
    Nat.rec (2, 5) (fun _ p => (p.2, 5 * p.2 - 2 * p.1))
  let a : ℕ → ℤ := fun n => (f n).1
  have ha0 : a 0 = 2 := rfl
  have ha1 : a 1 = 5 := by
    dsimp [a, f]
  have ha_succ_succ : ∀ n, a (n+2) = 5 * a (n+1) - 2 * a n := by
    intro n
    simp [a, f]
  have ha_eq : ∀ n, (a n : ℝ) = α^n + β^n := by
    intro n
    induction' n using Nat.strong_induction_on with n IH
    rcases n with (rfl | rfl | n)
    · -- n = 0
      simp [a, f, α, β]
      norm_num
    · -- n = 1
      simp [a, f, α, β, h_add]
    · -- n = n+2
      have IH0 : (a n : ℝ) = α^n + β^n := IH n (by omega)
      have IH1 : (a (n+1) : ℝ) = α^(n+1) + β^(n+1) := IH (n+1) (by omega)
      rw [ha_succ_succ n]
      push_cast
      rw [IH0, IH1]
      calc
        5*(α^(n+1) + β^(n+1)) - 2*(α^n + β^n)
            = (5*α - 2)*α^n + (5*β - 2)*β^n := by ring
        _ = α^2*α^n + β^2*β^n := by rw [h_α_sq, h_β_sq]
        _ = α^(n+2) + β^(n+2) := by ring
  by_cases hx : x = 0
  · -- x = 0 case
    subst hx
    have : ⌈α^0⌉ = (1 : ℤ) := by simp [α]
    rw [this]
    refine ⟨0, ?_⟩
    norm_num
  · -- x ≥ 1 case
    have hx1 : 1 ≤ x := Nat.one_le_of_lt (Nat.pos_of_ne_zero hx)
    have h_ceil : ⌈α^x⌉ = a x := by
      rw [Int.ceil_eq_iff]
      constructor
      · rw [ha_eq x]
        have hβpow_lt_one : β^x < 1 := by
          refine pow_lt_one₀ (by linarith) hβlt1 (Nat.pos_of_ne_zero hx).ne'
        linarith
      · rw [ha_eq x]
        have hβpow_pos : 0 < β^x := pow_pos hβpos x
        linarith
    rw [h_ceil]
    -- Now need to show Odd (a x) for x ≥ 1
    -- We prove by induction that ∀ n, Odd (a (n+1))
    have ha_odd_succ : ∀ n, Odd (a (n+1)) := by
      intro n
      induction' n using Nat.strong_induction_on with n IH
      rcases n with (rfl | rfl | n)
      · -- n = 0: a 1 = 5, odd
        simp [ha1]
        exact ⟨2, by norm_num⟩
      · -- n = 1: a 2 = 21, odd
        simp [ha_succ_succ 0, ha0, ha1]
        refine ⟨10, by norm_num⟩
      · -- n = n+2: a (n+3) = 5*a (n+2) - 2*a (n+1)
        have IH0 : Odd (a (n+1)) := IH n (by omega)
        have IH1 : Odd (a (n+2)) := IH (n+1) (by omega)
        rw [ha_succ_succ (n+1)]
        rcases IH0 with ⟨k0, h0⟩
        rcases IH1 with ⟨k1, h1⟩
        rw [h0, h1]
        refine ⟨5*k1 - 2*k0 + 1, ?_⟩
        ring
    -- Now we have a x is odd
    have hx' : ∃ n, x = n+1 := Nat.exists_eq_succ_of_ne_zero hx
    rcases hx' with ⟨n, hn⟩
    subst hn
    exact ha_odd_succ n
```
