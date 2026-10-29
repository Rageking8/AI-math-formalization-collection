# Claude Fable 5 (Arena AI)

Model: `claude-fable-5` (via Arena AI)\
Date: `24 July 2026`\
Line count: `127`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem digit_sum_pow_le (n x : ℕ) (hn : 0 < n) (hx : 0 < x) :
    (Nat.digits 10 (n ^ x)).sum ≤ ((Nat.digits 10 n).sum) ^ x := by
  -- basic recursion for digit sums
  have hrec : ∀ m : ℕ, 0 < m →
      (Nat.digits 10 m).sum = m % 10 + (Nat.digits 10 (m / 10)).sum := by
    intro m hm
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hm, List.sum_cons]
  -- subadditivity of digit sums, proved by bounded induction
  have key : ∀ N a b : ℕ, a + b ≤ N →
      (Nat.digits 10 (a + b)).sum ≤ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum := by
    intro N
    induction N with
    | zero =>
      intro a b hab
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha
      subst hb
      simp
    | succ N ih =>
      intro a b hab
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp
      have hab0 : 0 < a + b := by omega
      rw [hrec _ hab0, hrec _ ha, hrec _ hb]
      have hd : (a + b) / 10 = a / 10 + (b / 10 + (a % 10 + b % 10) / 10) := by
        omega
      have h1 : (Nat.digits 10 ((a + b) / 10)).sum ≤
          (Nat.digits 10 (a / 10)).sum +
            (Nat.digits 10 (b / 10 + (a % 10 + b % 10) / 10)).sum := by
        rw [hd]
        exact ih _ _ (by omega)
      have h2 : (Nat.digits 10 (b / 10 + (a % 10 + b % 10) / 10)).sum ≤
          (Nat.digits 10 (b / 10)).sum +
            (Nat.digits 10 ((a % 10 + b % 10) / 10)).sum :=
        ih _ _ (by omega)
      have h3 : (Nat.digits 10 ((a % 10 + b % 10) / 10)).sum ≤
          (a % 10 + b % 10) / 10 := by
        have hc : (a % 10 + b % 10) / 10 = 0 ∨ (a % 10 + b % 10) / 10 = 1 := by
          omega
        rcases hc with h | h
        · rw [h]; simp
        · rw [h, hrec 1 one_pos]; norm_num
      have hm : (a + b) % 10 + 10 * ((a % 10 + b % 10) / 10) = a % 10 + b % 10 := by
        omega
      omega
  have hadd : ∀ a b : ℕ,
      (Nat.digits 10 (a + b)).sum ≤ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum :=
    fun a b => key (a + b) a b le_rfl
  -- multiplying by 10 does not change the digit sum
  have hten : ∀ m : ℕ, (Nat.digits 10 (10 * m)).sum = (Nat.digits 10 m).sum := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have h1 : 10 * m % 10 = 0 := by omega
      have h2 : 10 * m / 10 = m := by omega
      rw [hrec (10 * m) (by omega), h1, h2, zero_add]
  -- scalar bound
  have hscal : ∀ k m : ℕ,
      (Nat.digits 10 (k * m)).sum ≤ k * (Nat.digits 10 m).sum := by
    intro k m
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : (k + 1) * m = k * m + m := by ring
      rw [hk]
      calc (Nat.digits 10 (k * m + m)).sum
          ≤ (Nat.digits 10 (k * m)).sum + (Nat.digits 10 m).sum := hadd _ _
        _ ≤ k * (Nat.digits 10 m).sum + (Nat.digits 10 m).sum :=
            Nat.add_le_add_right ih _
        _ = (k + 1) * (Nat.digits 10 m).sum := by ring
  -- submultiplicativity, by bounded induction on the first factor
  have hmulN : ∀ N a b : ℕ, a ≤ N →
      (Nat.digits 10 (a * b)).sum ≤ (Nat.digits 10 a).sum * (Nat.digits 10 b).sum := by
    intro N
    induction N with
    | zero =>
      intro a b ha
      have : a = 0 := by omega
      subst this
      simp
    | succ N ih =>
      intro a b ha
      rcases Nat.eq_zero_or_pos a with rfl | hpos
      · simp
      · have hsplit : a * b = 10 * (a / 10 * b) + a % 10 * b := by
          have h := Nat.div_add_mod a 10
          calc a * b = (10 * (a / 10) + a % 10) * b := by rw [h]
            _ = 10 * (a / 10 * b) + a % 10 * b := by ring
        rw [hsplit]
        calc (Nat.digits 10 (10 * (a / 10 * b) + a % 10 * b)).sum
            ≤ (Nat.digits 10 (10 * (a / 10 * b))).sum +
                (Nat.digits 10 (a % 10 * b)).sum := hadd _ _
          _ = (Nat.digits 10 (a / 10 * b)).sum +
                (Nat.digits 10 (a % 10 * b)).sum := by rw [hten]
          _ ≤ (Nat.digits 10 (a / 10)).sum * (Nat.digits 10 b).sum +
                a % 10 * (Nat.digits 10 b).sum :=
              Nat.add_le_add (ih (a / 10) b (by omega)) (hscal (a % 10) b)
          _ = (a % 10 + (Nat.digits 10 (a / 10)).sum) * (Nat.digits 10 b).sum := by
              ring
          _ = (Nat.digits 10 a).sum * (Nat.digits 10 b).sum := by
              rw [hrec a hpos]
  have hmul : ∀ a b : ℕ,
      (Nat.digits 10 (a * b)).sum ≤ (Nat.digits 10 a).sum * (Nat.digits 10 b).sum :=
    fun a b => hmulN a a b le_rfl
  -- final induction on the exponent
  have hpow : ∀ y : ℕ,
      (Nat.digits 10 (n ^ y)).sum ≤ ((Nat.digits 10 n).sum) ^ y := by
    intro y
    induction y with
    | zero =>
      simp only [pow_zero]
      have h1 : (Nat.digits 10 1).sum = 1 := by
        rw [hrec 1 one_pos]
        norm_num
      omega
    | succ y ih =>
      rw [pow_succ, pow_succ]
      calc (Nat.digits 10 (n ^ y * n)).sum
          ≤ (Nat.digits 10 (n ^ y)).sum * (Nat.digits 10 n).sum := hmul _ _
        _ ≤ ((Nat.digits 10 n).sum) ^ y * (Nat.digits 10 n).sum :=
            Nat.mul_le_mul ih le_rfl
  exact hpow x
```
