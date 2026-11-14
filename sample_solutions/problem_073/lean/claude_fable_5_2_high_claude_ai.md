# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `14 November 2026`\
Line count: `165`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def tetrate (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => a ^ (tetrate a n)

/-- `d` is one of the digits `0, 1, 8, 9`. -/
def TetS (d : ℕ) : Prop := d = 0 ∨ d = 1 ∨ d = 8 ∨ d = 9

/-- Every decimal digit of `m` is one of `0, 1, 8, 9`. -/
def TetG (m : ℕ) : Prop := ∀ i, TetS (m / 10 ^ i % 10)

lemma TetG_zero : TetG 0 := fun i => by simp [TetS]

lemma TetG_cons {a d : ℕ} (hd : d < 10) (hS : TetS d) (ha : TetG a) :
    TetG (10 * a + d) := by
  intro i
  cases i with
  | zero =>
    have : (10 * a + d) / 10 ^ 0 % 10 = d := by simp; omega
    rw [this]; exact hS
  | succ i =>
    have : (10 * a + d) / 10 ^ (i + 1) = a / 10 ^ i := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      congr 1
      omega
    rw [this]; exact ha i

lemma TetG_div {m : ℕ} (h : TetG m) : TetG (m / 10) := fun i => by
  have := h (i + 1)
  rwa [pow_succ', ← Nat.div_div_eq_div_mul] at this

lemma TetG_mod {m : ℕ} (h : TetG m) : TetS (m % 10) := by
  simpa using h 0

lemma TetG_compl : ∀ (M q : ℕ), q < 10 ^ M → TetG q → TetG (10 ^ M - 1 - q) := by
  intro M
  induction M with
  | zero =>
    intro q hq _
    have : 10 ^ 0 - 1 - q = 0 := by simp
    rw [this]; exact TetG_zero
  | succ M ih =>
    intro q hq hG
    rw [pow_succ] at hq ⊢
    generalize hX : 10 ^ M = X at *
    have e : X * 10 - 1 - q = 10 * (X - 1 - q / 10) + (9 - q % 10) := by omega
    rw [e]
    refine TetG_cons (by omega) ?_ (ih (q / 10) (by omega) (TetG_div hG))
    have := TetG_mod hG
    unfold TetS at *
    omega

lemma TetG_concat : ∀ (M a b : ℕ), b < 10 ^ M → TetG a → TetG b →
    TetG (a * 10 ^ M + b) := by
  intro M
  induction M with
  | zero =>
    intro a b hb ha _
    have : a * 10 ^ 0 + b = a := by simp at hb ⊢; omega
    rw [this]; exact ha
  | succ M ih =>
    intro a b hb ha hG
    rw [pow_succ] at hb
    have e : a * 10 ^ (M + 1) + b = 10 * (a * 10 ^ M + b / 10) + b % 10 := by
      have h1 : a * 10 ^ (M + 1) = 10 * (a * 10 ^ M) := by ring
      rw [h1]; omega
    rw [e]
    exact TetG_cons (by omega) (TetG_mod hG) (ih a (b / 10) (by omega) ha (TetG_div hG))

lemma tetrate_prod_key : ∀ n : ℕ, 1 ≤ n → ∃ q r : ℕ,
    ∏ k ∈ Finset.Icc 1 n, (tetrate 10 k - 1) = 10 * q + r ∧ (r = 1 ∨ r = 9) ∧ TetG q ∧
      10 * q + r < 10 ^ (tetrate 10 n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨0, 9, ?_, Or.inr rfl, TetG_zero, ?_⟩
    · simp [tetrate]
    · simp [tetrate]
  | succ n hn ih =>
    obtain ⟨q, r, hP, hr, hq, hlt⟩ := ih
    rw [Finset.prod_Icc_succ_top (by omega), hP]
    have hT : tetrate 10 (n + 1) = 10 ^ (tetrate 10 n) := rfl
    rw [hT]
    have hNpos : 1 ≤ tetrate 10 n := by
      cases n with
      | zero => simp [tetrate]
      | succ m => show 1 ≤ 10 ^ (tetrate 10 m); exact Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨M, hM⟩ : ∃ M, tetrate 10 n = M + 1 := ⟨tetrate 10 n - 1, by omega⟩
    rw [hM] at hlt ⊢
    have hML : M < 10 ^ M := Nat.lt_pow_self (by norm_num)
    have hX : (10 : ℕ) ^ (M + 1) = 10 * 10 ^ M := by ring
    -- size bound
    have hbound : (10 * q + r) * (10 ^ (M + 1) - 1) < 10 ^ (10 ^ (M + 1)) := by
      have h1 : (10 * q + r) * (10 ^ (M + 1) - 1) < 10 ^ (M + 1) * 10 ^ (M + 1) := by
        have hpos : 0 < 10 ^ (M + 1) := by positivity
        calc (10 * q + r) * (10 ^ (M + 1) - 1)
            ≤ (10 * q + r) * 10 ^ (M + 1) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ < 10 ^ (M + 1) * 10 ^ (M + 1) := Nat.mul_lt_mul_of_pos_right hlt hpos
      have h2 : 10 ^ (M + 1) * 10 ^ (M + 1) ≤ 10 ^ (10 ^ (M + 1)) := by
        rw [← pow_add]
        apply Nat.pow_le_pow_right (by norm_num)
        rw [hX]; omega
      exact lt_of_lt_of_le h1 h2
    rw [hX] at hlt
    generalize hXe : 10 ^ M = X at *
    have hqX : q < X := by rcases hr with rfl | rfl <;> omega
    have hc : TetG (X - 1 - q) := by
      rw [← hXe]; exact TetG_compl M q (by rw [hXe]; exact hqX) hq
    have hcl : X - 1 - q < 10 ^ M := by rw [hXe]; omega
    refine ⟨(10 * q + (r - 1)) * X + (X - 1 - q), 10 - r, ?_, ?_, ?_, ?_⟩
    · rw [hX]
      rcases hr with rfl | rfl
      · have h1 : (10 * q + 1) * (10 * X - 1) = (10 * q + 1) * (10 * X) - (10 * q + 1) :=
          Nat.mul_sub_one _ _
        have h2 : (10 * q + 1) * (10 * X) = 100 * (q * X) + 10 * X := by ring
        have h3 : (10 * q + (1 - 1)) * X = 10 * (q * X) := by ring
        rw [h1, h2, h3]
        have : q * X ≥ 0 := Nat.zero_le _
        omega
      · have h1 : (10 * q + 9) * (10 * X - 1) = (10 * q + 9) * (10 * X) - (10 * q + 9) :=
          Nat.mul_sub_one _ _
        have h2 : (10 * q + 9) * (10 * X) = 100 * (q * X) + 90 * X := by ring
        have h3 : (10 * q + (9 - 1)) * X = 10 * (q * X) + 8 * X := by ring
        rw [h1, h2, h3]
        omega
    · omega
    · have ha : TetG (10 * q + (r - 1)) := by
        refine TetG_cons (by omega) ?_ hq
        unfold TetS; omega
      have h := TetG_concat M _ _ hcl ha hc
      rw [hXe] at h
      exact h
    · -- transfer the size bound through the equation
      have heq : (10 * q + r) * (10 ^ (M + 1) - 1) =
          10 * ((10 * q + (r - 1)) * X + (X - 1 - q)) + (10 - r) := by
        rw [hX]
        rcases hr with rfl | rfl
        · have h1 : (10 * q + 1) * (10 * X - 1) = (10 * q + 1) * (10 * X) - (10 * q + 1) :=
            Nat.mul_sub_one _ _
          have h2 : (10 * q + 1) * (10 * X) = 100 * (q * X) + 10 * X := by ring
          have h3 : (10 * q + (1 - 1)) * X = 10 * (q * X) := by ring
          rw [h1, h2, h3]
          omega
        · have h1 : (10 * q + 9) * (10 * X - 1) = (10 * q + 9) * (10 * X) - (10 * q + 9) :=
            Nat.mul_sub_one _ _
          have h2 : (10 * q + 9) * (10 * X) = 100 * (q * X) + 90 * X := by ring
          have h3 : (10 * q + (9 - 1)) * X = 10 * (q * X) + 8 * X := by ring
          rw [h1, h2, h3]
          omega
      rw [← heq]; exact hbound

theorem product_tetrate_sub_one_no_digit_two (n : ℕ) (hn : 0 < n) :
    2 ∉ Nat.digits 10 (∏ k ∈ Finset.Icc 1 n, (tetrate 10 k - 1)) := by
  obtain ⟨q, r, hP, hr, hq, -⟩ := tetrate_prod_key n hn
  intro h2
  rw [hP] at h2
  have hG : TetG (10 * q + r) :=
    TetG_cons (by omega) (by unfold TetS; omega) hq
  obtain ⟨i, hi, hd⟩ := List.mem_iff_getElem.mp h2
  have h3 := Nat.getD_digits (10 * q + r) i (b := 10) (by norm_num)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hd] at h3
  have h4 := hG i
  unfold TetS at h4
  omega
```
