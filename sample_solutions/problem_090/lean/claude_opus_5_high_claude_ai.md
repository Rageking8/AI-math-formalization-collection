# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `13 September 2026`\
Line count: `153`\
Turn count: `2`

## Solution

```lean4
import Mathlib

def concat (a b : ℕ) : ℕ :=
  a * 10 ^ (Nat.toDigits 10 b).length + b

theorem myConcat_toDigitsCore_len :
    ∀ (fuel n : ℕ) (ds : List Char), 0 < n → n < fuel →
    ∃ k : ℕ, (Nat.toDigitsCore 10 fuel n ds).length = k + ds.length ∧
      n < 10 ^ k ∧ 10 ^ k ≤ 10 * n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n ds h0 h1
    exact absurd h1 (Nat.not_lt_zero n)
  | succ f ih =>
    intro n ds h0 h1
    by_cases hn : n / 10 = 0
    · have hlt : n < 10 := by omega
      have hlen : (Nat.toDigitsCore 10 (f + 1) n ds).length = ds.length + 1 := by
        first
          | (simp [Nat.toDigitsCore, hn]; done)
          | (unfold Nat.toDigitsCore; simp [hn]; done)
          | (rw [Nat.toDigitsCore]; simp [hn]; done)
          | simp [Nat.toDigitsCore, hn]
      refine ⟨1, by omega, ?_, ?_⟩
      · rw [pow_one]; exact hlt
      · rw [pow_one]; omega
    · have h2 : 0 < n / 10 := Nat.pos_of_ne_zero hn
      have h3 : n / 10 < f := by omega
      obtain ⟨k, hk1, hk2, hk3⟩ := ih (n / 10) (Nat.digitChar (n % 10) :: ds) h2 h3
      have heq : Nat.toDigitsCore 10 (f + 1) n ds
          = Nat.toDigitsCore 10 f (n / 10) (Nat.digitChar (n % 10) :: ds) := by
        first
          | (simp [Nat.toDigitsCore, hn]; done)
          | (unfold Nat.toDigitsCore; simp [hn]; done)
          | (rw [Nat.toDigitsCore]; simp [hn]; done)
          | simp [Nat.toDigitsCore, hn]
      refine ⟨k + 1, ?_, ?_, ?_⟩
      · rw [heq, hk1]
        simp only [List.length_cons]
        omega
      · have h8 : n / 10 + 1 ≤ 10 ^ k := hk2
        calc n < (n / 10 + 1) * 10 := by omega
          _ ≤ 10 ^ k * 10 := Nat.mul_le_mul h8 (le_refl 10)
          _ = 10 ^ (k + 1) := by ring
      · have h10 : 10 * (n / 10) ≤ n := by omega
        calc (10:ℕ) ^ (k + 1) = 10 * 10 ^ k := by ring
          _ ≤ 10 * (10 * (n / 10)) := Nat.mul_le_mul (le_refl 10) hk3
          _ ≤ 10 * n := Nat.mul_le_mul (le_refl 10) h10

theorem myConcat_len_bounds (n : ℕ) (hn : 0 < n) :
    n < 10 ^ (Nat.toDigits 10 n).length ∧ 10 ^ (Nat.toDigits 10 n).length ≤ 10 * n := by
  have h0 : Nat.toDigits 10 n = Nat.toDigitsCore 10 (n + 1) n [] := by
    first
      | rfl
      | (simp [Nat.toDigits]; done)
      | (unfold Nat.toDigits; done)
  obtain ⟨k, hk1, hk2, hk3⟩ :=
    myConcat_toDigitsCore_len (n + 1) n [] hn (Nat.lt_succ_self n)
  have hlen : (Nat.toDigits 10 n).length = k := by
    rw [h0, hk1]
    simp
  rw [hlen]
  exact ⟨hk2, hk3⟩

theorem myConcat_final_step {x y Q : ℕ} (h : x ≡ y [MOD Q - 7]) (hQ : 256 ≤ Q)
    (hx : 0 < x) (hy : 0 < y) (hxQ : x + 7 ≤ Q) (hyQ : y + 7 ≤ Q) (hne : x ≠ y) : False := by
  rcases le_total x y with hle | hle
  · have hdvd : (Q - 7) ∣ y - x := (Nat.modEq_iff_dvd' hle).mp h
    have hpos : 0 < y - x := by omega
    have hle2 := Nat.le_of_dvd hpos hdvd
    omega
  · have hdvd : (Q - 7) ∣ x - y := (Nat.modEq_iff_dvd' hle).mp h.symm
    have hpos : 0 < x - y := by omega
    have hle2 := Nat.le_of_dvd hpos hdvd
    omega

theorem myConcat_main_aux (a b P : ℕ) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hlow : b ^ 3 < P) (hhigh : P ≤ 10 * b ^ 3)
    (hmod : a * P + b ^ 3 ≡ a ^ 2 + b [MOD (a * b) ^ 4 - 7]) : False := by
  have hb3 : 8 ≤ b ^ 3 := by
    calc (8:ℕ) = 2 ^ 3 := by norm_num
      _ ≤ b ^ 3 := Nat.pow_le_pow_left hb2 3
  have ha3 : 8 ≤ a ^ 3 := by
    calc (8:ℕ) = 2 ^ 3 := by norm_num
      _ ≤ a ^ 3 := Nat.pow_le_pow_left ha2 3
  have hasq : 4 ≤ a ^ 2 := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ a ^ 2 := Nat.pow_le_pow_left ha2 2
  have hbsq : 4 ≤ b ^ 2 := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ b ^ 2 := Nat.pow_le_pow_left hb2 2
  have hbb2 : b ≤ b ^ 2 := by
    have h1 : 2 * b ≤ b * b := Nat.mul_le_mul hb2 (le_refl b)
    linarith
  have hbb3 : b < b ^ 3 := by
    have h1 : (4:ℕ) ≤ b * b := by
      calc (4:ℕ) = 2 * 2 := by norm_num
        _ ≤ b * b := Nat.mul_le_mul hb2 hb2
    have h2 : 4 * b ≤ (b * b) * b := Nat.mul_le_mul h1 (le_refl b)
    linarith
  have hQ : (256:ℕ) ≤ (a * b) ^ 4 := by
    have h4 : 4 ≤ a * b := by
      calc (4:ℕ) = 2 * 2 := by norm_num
        _ ≤ a * b := Nat.mul_le_mul ha2 hb2
    calc (256:ℕ) = 4 ^ 4 := by norm_num
      _ ≤ (a * b) ^ 4 := Nat.pow_le_pow_left h4 4
  have hx7 : a * P + b ^ 3 + 7 ≤ (a * b) ^ 4 := by
    have h1 : a * P ≤ a * (10 * b ^ 3) := Nat.mul_le_mul (le_refl a) hhigh
    have h2 : 16 ≤ a ^ 3 * b := by
      calc (16:ℕ) = 8 * 2 := by norm_num
        _ ≤ a ^ 3 * b := Nat.mul_le_mul ha3 hb2
    have h3 : 16 * (a * b ^ 3) ≤ (a ^ 3 * b) * (a * b ^ 3) := Nat.mul_le_mul h2 (le_refl _)
    have h5 : 2 * b ^ 3 ≤ a * b ^ 3 := Nat.mul_le_mul ha2 (le_refl _)
    linarith
  have hy7 : a ^ 2 + b + 7 ≤ (a * b) ^ 4 := by
    have hw : 16 ≤ a ^ 2 * b ^ 2 := by
      calc (16:ℕ) = 4 * 4 := by norm_num
        _ ≤ a ^ 2 * b ^ 2 := Nat.mul_le_mul hasq hbsq
    have hw2 : 16 * (a ^ 2 * b ^ 2) ≤ (a ^ 2 * b ^ 2) * (a ^ 2 * b ^ 2) :=
      Nat.mul_le_mul hw (le_refl _)
    have hw4 : 4 * a ^ 2 ≤ a ^ 2 * b ^ 2 := by
      have h := Nat.mul_le_mul (le_refl (a ^ 2)) hbsq
      linarith
    have hw5 : 4 * b ≤ a ^ 2 * b ^ 2 := Nat.mul_le_mul hasq hbb2
    linarith
  have hne : a * P + b ^ 3 ≠ a ^ 2 + b := by
    intro h
    have hlt1 : a * P < a * a := by nlinarith
    have hlt2 : P < a := by
      first
        | exact lt_of_mul_lt_mul_left hlt1 (Nat.zero_le a)
        | exact Nat.lt_of_mul_lt_mul_left hlt1
    have hlt2' : P + 1 ≤ a := hlt2
    have h3a : a * (P + 1) ≤ a * a := Nat.mul_le_mul (le_refl a) hlt2'
    nlinarith
  have hxpos : 0 < a * P + b ^ 3 :=
    lt_of_lt_of_le (by linarith : (0:ℕ) < b ^ 3) (Nat.le_add_left _ _)
  have hypos : 0 < a ^ 2 + b :=
    lt_of_lt_of_le (by linarith : (0:ℕ) < a ^ 2) (Nat.le_add_right _ _)
  exact myConcat_final_step hmod hQ hxpos hypos hx7 hy7 hne

theorem no_positive_integers_concat_mod :
    ¬ ∃ (a b : ℕ), 1 < a ∧ 1 < b ∧ (concat a (b ^ 3) ≡
      a ^ 2 + b [MOD (a * b) ^ 4 - 7]) := by
  rintro ⟨a, b, ha, hb, hmod⟩
  have ha2 : 2 ≤ a := by omega
  have hb2 : 2 ≤ b := by omega
  have hb3pos : 0 < b ^ 3 := pow_pos (show 0 < b by omega) 3
  obtain ⟨hlow, hhigh⟩ := myConcat_len_bounds (b ^ 3) hb3pos
  have hc : concat a (b ^ 3) = a * 10 ^ (Nat.toDigits 10 (b ^ 3)).length + b ^ 3 := rfl
  rw [hc] at hmod
  exact myConcat_main_aux a b (10 ^ (Nat.toDigits 10 (b ^ 3)).length) ha2 hb2 hlow hhigh hmod
```
