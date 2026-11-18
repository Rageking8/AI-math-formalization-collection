# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `14 November 2026`\
Line count: `188`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def concat (a b : ℕ) : ℕ :=
  a * 10 ^ (Nat.toDigits 10 b).length + b

def preconditions (n a b c : ℕ) : Prop :=
  (1 < a ∧ ¬Nat.Prime a) ∧ (1 < b ∧ ¬Nat.Prime b) ∧ (1 < c ∧ ¬Nat.Prime c) ∧
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a + b + c > n

theorem tight_upper_bound_concat_div_prod (n : ℕ) (hn : 0 < n) :
    (∀ a b c : ℕ, preconditions n a b c →
      (concat (concat a b) c : ℚ) / (a * b * c : ℚ) ≤ 4101 / 40) ∧
      (∃ a b c : ℕ, preconditions n a b c ∧
      (concat (concat a b) c : ℚ) / (a * b * c : ℚ) = 4101 / 40) := by
  -- The number of decimal digits of `m` is at most `k` iff `m < 10 ^ k`.
  have key : ∀ m k : ℕ, 0 < k → ((Nat.toDigits 10 m).length ≤ k ↔ m < 10 ^ k) := by
    first
      | exact fun m k hk => Nat.length_toDigits_le_iff (by norm_num) hk
      | (
        have low : ∀ (fuel : Nat), 0 < fuel → ∀ (m : Nat) (ds : List Char),
            ds.length < (Nat.toDigitsCore 10 fuel m ds).length := by
          intro fuel
          induction fuel with
          | zero => intro h; exact absurd h (Nat.lt_irrefl _)
          | succ f ih =>
            intro _ m ds
            simp only [Nat.toDigitsCore]
            split
            · simp
            · by_cases hf : f = 0
              · subst hf
                simp [Nat.toDigitsCore]
              · have h := ih (by omega) (m / 10) (Nat.digitChar (m % 10) :: ds)
                simp only [List.length_cons] at h
                omega
        have aux : ∀ (fuel m : Nat) (ds : List Char) (k : Nat), m < fuel → 0 < k →
            ((Nat.toDigitsCore 10 fuel m ds).length ≤ k + ds.length ↔ m < 10 ^ k) := by
          intro fuel
          induction fuel with
          | zero => intro m ds k h; omega
          | succ f ih =>
            intro m ds k hm hk
            simp only [Nat.toDigitsCore]
            split
            · rename_i h
              have h10 : 10 ^ 1 ≤ 10 ^ k := Nat.pow_le_pow_right (by omega) hk
              simp only [List.length_cons]
              omega
            · rename_i h
              by_cases hk1 : k = 1
              · subst hk1
                have hl := low f (by omega) (m / 10) (Nat.digitChar (m % 10) :: ds)
                simp only [List.length_cons] at hl
                omega
              · have hi := ih (m / 10) (Nat.digitChar (m % 10) :: ds) (k - 1) (by omega) (by omega)
                simp only [List.length_cons] at hi
                have e : 10 ^ k = 10 ^ (k - 1) * 10 := by
                  have hk' : k = (k - 1) + 1 := by omega
                  rw [hk', Nat.pow_succ]
                  simp
                rw [e]
                have e' : k + ds.length = k - 1 + (ds.length + 1) := by omega
                rw [e', hi]
                omega
        intro m k hk
        have h := aux (m + 1) m [] k (Nat.lt_succ_self m) hk
        simpa [Nat.toDigits] using h)
  -- `10 ^ (number of digits of b) ≤ 10 * b` for positive `b`.
  have hA : ∀ b : ℕ, 0 < b → 10 ^ (Nat.toDigits 10 b).length ≤ 10 * b := by
    intro b hb
    by_cases hL : (Nat.toDigits 10 b).length ≤ 1
    · have h1 : 10 ^ (Nat.toDigits 10 b).length ≤ 10 ^ 1 :=
        Nat.pow_le_pow_right (by norm_num) hL
      have h2 : (10 : ℕ) ^ 1 = 10 := by norm_num
      omega
    · obtain ⟨k, hk⟩ : ∃ k, (Nat.toDigits 10 b).length = k + 2 :=
        ⟨(Nat.toDigits 10 b).length - 2, by omega⟩
      have h := key b (k + 1) (Nat.succ_pos k)
      rw [hk] at h ⊢
      have h2 : 10 ^ (k + 1) ≤ b := by
        by_contra hlt
        have h3 := h.mpr (lt_of_not_ge hlt)
        omega
      have e : 10 ^ (k + 2) = 10 ^ (k + 1) * 10 := by ring
      rw [e]
      omega
  -- One-digit numbers.
  have hA' : ∀ b : ℕ, b < 10 → 10 ^ (Nat.toDigits 10 b).length ≤ 10 := by
    intro b hb
    have h2 : (10 : ℕ) ^ 1 = 10 := by norm_num
    have h := (key b 1 Nat.one_pos).mpr (by rw [h2]; exact hb)
    have h1 : 10 ^ (Nat.toDigits 10 b).length ≤ 10 ^ 1 :=
      Nat.pow_le_pow_right (by norm_num) h
    omega
  -- A composite number is at least 4.
  have hcomp : ∀ a : ℕ, 1 < a → ¬Nat.Prime a → 4 ≤ a := by
    intro a h1 hp
    by_contra h
    have h23 : a = 2 ∨ a = 3 := by omega
    rcases h23 with rfl | rfl
    · exact hp Nat.prime_two
    · exact hp Nat.prime_three
  constructor
  · -- Upper bound.
    rintro a b c ⟨⟨ha1, hap⟩, ⟨hb1, hbp⟩, ⟨hc1, hcp⟩, -, -, -, -⟩
    have ha := hcomp a ha1 hap
    have hb := hcomp b hb1 hbp
    have hc := hcomp c hc1 hcp
    have hQ := hA c (by omega)
    have hnat : 40 * ((a * 10 ^ (Nat.toDigits 10 b).length + b) *
        10 ^ (Nat.toDigits 10 c).length + c) ≤ 4101 * (a * b * c) := by
      generalize 10 ^ (Nat.toDigits 10 c).length = Q at hQ ⊢
      have h3 : 4 * b * c ≤ a * b * c :=
        Nat.mul_le_mul_right c (Nat.mul_le_mul_right b ha)
      by_cases hb10 : b < 10
      · have hP := hA' b hb10
        generalize 10 ^ (Nat.toDigits 10 b).length = P at hP ⊢
        have h1 : (a * P + b) * Q ≤ (a * 10 + b) * (10 * c) :=
          Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left a hP) b) hQ
        have h2 : a * 4 * c ≤ a * b * c :=
          Nat.mul_le_mul_right c (Nat.mul_le_mul_left a hb)
        have h4 : 1 * c ≤ a * b * c :=
          Nat.mul_le_mul_right c (Nat.mul_pos (by omega) (by omega))
        nlinarith [h1, h2, h3, h4]
      · have hP := hA b (by omega)
        generalize 10 ^ (Nat.toDigits 10 b).length = P at hP ⊢
        have h1 : (a * P + b) * Q ≤ (a * (10 * b) + b) * (10 * c) :=
          Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left a hP) b) hQ
        have h5 : 10 * c ≤ b * c := Nat.mul_le_mul_right c (by omega)
        nlinarith [h1, h3, h5]
    have ha' : (0 : ℚ) < (a : ℚ) := by exact_mod_cast (by omega : 0 < a)
    have hb' : (0 : ℚ) < (b : ℚ) := by exact_mod_cast (by omega : 0 < b)
    have hc' : (0 : ℚ) < (c : ℚ) := by exact_mod_cast (by omega : 0 < c)
    have hpos : (0 : ℚ) < (a : ℚ) * b * c := mul_pos (mul_pos ha' hb') hc'
    have hq : (40 : ℚ) * ((((a : ℚ) * 10 ^ (Nat.toDigits 10 b).length + b) *
        10 ^ (Nat.toDigits 10 c).length + c)) ≤ 4101 * ((a : ℚ) * b * c) := by
      exact_mod_cast hnat
    have hcast : ((concat (concat a b) c : ℕ) : ℚ) =
        ((a : ℚ) * 10 ^ (Nat.toDigits 10 b).length + b) *
          10 ^ (Nat.toDigits 10 c).length + c := by
      simp only [concat]
      push_cast
      ring
    rw [hcast]
    first
      | rw [div_le_iff₀ hpos]
      | rw [div_le_iff hpos]
    linarith
  · -- The bound is attained at `a = 4`, `b = 10`, `c = 10 ^ (n + 2)`.
    have hn' : n < 10 ^ n := by
      first
        | exact Nat.lt_pow_self (by norm_num)
        | exact Nat.lt_pow_self (by norm_num) n
    have e2 : 10 ^ (n + 2) = 100 * 10 ^ n := by ring
    have e3 : 10 ^ (n + 3) = 1000 * 10 ^ n := by ring
    have hL10 : (Nat.toDigits 10 10).length = 2 := by
      have h1 := (key 10 2 (by norm_num)).mpr (by norm_num)
      have h2 := key 10 1 (by norm_num)
      have h3 : ¬(Nat.toDigits 10 10).length ≤ 1 := fun h => by
        have := h2.mp h
        norm_num at this
      omega
    have hLc : (Nat.toDigits 10 (10 ^ (n + 2))).length = n + 3 := by
      have h1 := (key (10 ^ (n + 2)) (n + 3) (by omega)).mpr (by rw [e2, e3]; omega)
      have h2 := key (10 ^ (n + 2)) (n + 2) (by omega)
      have h3 : ¬(Nat.toDigits 10 (10 ^ (n + 2))).length ≤ n + 2 := fun h =>
        lt_irrefl _ (h2.mp h)
      omega
    have np4 : ¬Nat.Prime 4 := fun hp => by
      have h := Nat.Prime.eq_one_or_self_of_dvd hp 2 ⟨2, by norm_num⟩
      omega
    have np10 : ¬Nat.Prime 10 := fun hp => by
      have h := Nat.Prime.eq_one_or_self_of_dvd hp 2 ⟨5, by norm_num⟩
      omega
    refine ⟨4, 10, 10 ^ (n + 2), ⟨⟨by norm_num, np4⟩, ⟨by norm_num, np10⟩,
      ⟨by omega, ?_⟩, by norm_num, by omega, by omega, by omega⟩, ?_⟩
    · intro hp
      have h := Nat.Prime.eq_one_or_self_of_dvd hp 2 ⟨50 * 10 ^ n, by ring⟩
      omega
    · have hcast : ((concat (concat 4 10) (10 ^ (n + 2)) : ℕ) : ℚ) =
          4101 * (10 : ℚ) ^ (n + 2) := by
        simp only [concat]
        rw [hL10, hLc]
        push_cast
        ring
      rw [hcast, div_eq_iff (by positivity)]
      push_cast
      ring
```
