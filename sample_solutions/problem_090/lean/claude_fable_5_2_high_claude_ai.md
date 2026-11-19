# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `15 November 2026`\
Line count: `84`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def concat (a b : ℕ) : ℕ :=
  a * 10 ^ (Nat.toDigits 10 b).length + b

theorem no_positive_integers_concat_mod :
    ¬ ∃ (a b : ℕ), 1 < a ∧ 1 < b ∧ (concat a (b ^ 3) ≡
      a ^ 2 + b [MOD (a * b) ^ 4 - 7]) := by
  -- the number of decimal digits `m` of `n > 0` satisfies `n < 10 ^ m ≤ 10 * n`
  have key : ∀ (fuel n : ℕ) (acc : List Char), n < fuel → 0 < n →
      ∃ m, (Nat.toDigitsCore 10 fuel n acc).length = acc.length + m ∧
        n < 10 ^ m ∧ 10 ^ m ≤ 10 * n := by
    intro fuel
    induction fuel with
    | zero => intro n acc h; exact absurd h (Nat.not_lt_zero n)
    | succ f ih =>
      intro n acc hn hpos
      by_cases h0 : n / 10 = 0
      · refine ⟨1, ?_, ?_, ?_⟩
        · simp only [Nat.toDigitsCore, h0, ite_true, List.length_cons]
        · omega
        · omega
      · obtain ⟨m, hm1, hm2, hm3⟩ :=
          ih (n / 10) (Nat.digitChar (n % 10) :: acc) (by omega) (by omega)
        refine ⟨m + 1, ?_, ?_, ?_⟩
        · simp only [Nat.toDigitsCore, h0, ite_false]
          rw [hm1, List.length_cons]
          omega
        · rw [Nat.pow_succ]; omega
        · rw [Nat.pow_succ]; omega
  rintro ⟨a, b, ha, hb, h⟩
  -- basic facts about `c = b ^ 3`
  have hbb : 4 ≤ b * b := Nat.mul_le_mul hb hb
  have hc4 : 4 * b ≤ b ^ 3 := by
    have h1 : 4 * b ≤ b * b * b := Nat.mul_le_mul_right b hbb
    have h2 : b ^ 3 = b * b * b := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    omega
  have hcpos : 0 < b ^ 3 := by omega
  obtain ⟨m, hm1, hm2, hm3⟩ := key (b ^ 3 + 1) (b ^ 3) [] (Nat.lt_succ_self _) hcpos
  have hlen : (Nat.toDigits 10 (b ^ 3)).length = m := by
    have h1 : (Nat.toDigits 10 (b ^ 3)).length
        = (Nat.toDigitsCore 10 (b ^ 3 + 1) (b ^ 3) []).length := rfl
    rw [h1, hm1, List.length_nil, Nat.zero_add]
  have hconcat : concat a (b ^ 3) = a * 10 ^ m + b ^ 3 := by
    unfold concat
    rw [hlen]
  rw [hconcat] at h
  -- size estimates for the modulus
  have haa : 4 ≤ a * a := Nat.mul_le_mul ha ha
  have haP : a * 10 ^ m ≤ a * (10 * b ^ 3) := Nat.mul_le_mul_left a hm3
  have hac : 2 * b ^ 3 ≤ a * b ^ 3 := Nat.mul_le_mul_right (b ^ 3) ha
  have e1 : (a * b) ^ 4 = (a * a * a * b) * (a * b ^ 3) := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm]
  have e2 : (a * b) ^ 4 = (a * a * (b * b) * (b * b)) * (a * a) := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm]
  have h16 : 16 ≤ a * a * a * b :=
    Nat.mul_le_mul (Nat.mul_le_mul haa ha) hb
  have h64 : 64 ≤ a * a * (b * b) * (b * b) :=
    Nat.mul_le_mul (Nat.mul_le_mul haa hbb) hbb
  have b1 : 16 * (a * b ^ 3) ≤ (a * b) ^ 4 := by
    rw [e1]; exact Nat.mul_le_mul_right _ h16
  have b2 : 64 * (a * a) ≤ (a * b) ^ 4 := by
    rw [e2]; exact Nat.mul_le_mul_right _ h64
  have hmul : a * (10 * b ^ 3) = 10 * (a * b ^ 3) := Nat.mul_left_comm a 10 (b ^ 3)
  have hsq : a ^ 2 = a * a := by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  have lt1 : a * 10 ^ m + b ^ 3 < (a * b) ^ 4 - 7 := by omega
  have lt2 : a ^ 2 + b < (a * b) ^ 4 - 7 := by omega
  have heq : a * 10 ^ m + b ^ 3 = a ^ 2 + b := by
    have h' : (a * 10 ^ m + b ^ 3) % ((a * b) ^ 4 - 7) = (a ^ 2 + b) % ((a * b) ^ 4 - 7) := h
    rwa [Nat.mod_eq_of_lt lt1, Nat.mod_eq_of_lt lt2] at h'
  -- the equation forces `10 ^ m < a`, which makes the right-hand side too large
  rw [hsq] at heq
  have hPa : 10 ^ m < a := by
    apply Nat.lt_of_not_le
    intro hle
    have : a * a ≤ a * 10 ^ m := Nat.mul_le_mul_left a hle
    omega
  have h3 : a * (10 ^ m + 1) ≤ a * a := Nat.mul_le_mul_left a hPa
  rw [Nat.mul_add, Nat.mul_one] at h3
  omega
```
