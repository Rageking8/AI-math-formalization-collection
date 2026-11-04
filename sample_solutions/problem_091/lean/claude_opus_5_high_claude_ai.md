# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `13 September 2026`\
Line count: `209`\
Turn count: `2`

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
  -- m < 10 ^ m
  have hpow : ∀ m : ℕ, m < 10 ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ k ih =>
      have h1 : 1 ≤ (10:ℕ) ^ k := Nat.one_le_pow _ _ (by norm_num)
      have h2 : (10:ℕ) ^ (k + 1) = 10 ^ k * 10 := by ring
      omega
  -- digit count analysis of the core routine
  have core : ∀ (fuel : ℕ) (m : ℕ) (ds : List Char), m < 10 ^ fuel →
      ∃ k, (Nat.toDigitsCore 10 (fuel + 1) m ds).length = ds.length + k ∧
        m < 10 ^ k ∧ (0 < m → 10 ^ k ≤ 10 * m) := by
    intro fuel
    induction fuel with
    | zero =>
      intro m ds hm
      have hm0 : m = 0 := by simpa using hm
      subst hm0
      refine ⟨1, ?_, by norm_num, fun h => absurd h (lt_irrefl 0)⟩
      show (Nat.toDigitsCore 10 (0 + 1) 0 ds).length = ds.length + 1
      first
        | rfl
        | simp [Nat.toDigitsCore]
    | succ f ih =>
      intro m ds hm
      have hpk : (10:ℕ) ^ (f + 1) = 10 ^ f * 10 := by ring
      have hstep : Nat.toDigitsCore 10 (f + 1 + 1) m ds =
          if m / 10 = 0 then Nat.digitChar (m % 10) :: ds
          else Nat.toDigitsCore 10 (f + 1) (m / 10) (Nat.digitChar (m % 10) :: ds) := by
        first
          | rfl
          | simp [Nat.toDigitsCore]
      rw [hstep]
      by_cases h : m / 10 = 0
      · rw [if_pos h]
        have h1 : (10:ℕ) ^ 1 = 10 := pow_one 10
        exact ⟨1, by simp, by omega, fun hm' => by omega⟩
      · rw [if_neg h]
        have hlt : m / 10 < 10 ^ f := by omega
        obtain ⟨k, hk1, hk2, hk3⟩ := ih (m / 10) (Nat.digitChar (m % 10) :: ds) hlt
        have hk : (10:ℕ) ^ (k + 1) = 10 ^ k * 10 := by ring
        refine ⟨k + 1, ?_, by omega, ?_⟩
        · rw [hk1]
          simp only [List.length_cons]
          omega
        · intro hposm
          have hpos' : 0 < m / 10 := by omega
          have h3 := hk3 hpos'
          omega
  have spec : ∀ m : ℕ, 0 < m →
      m < 10 ^ (Nat.toDigits 10 m).length ∧ 10 ^ (Nat.toDigits 10 m).length ≤ 10 * m := by
    intro m hm
    obtain ⟨k, hk1, hk2, hk3⟩ := core m m [] (hpow m)
    have h0 : Nat.toDigits 10 m = Nat.toDigitsCore 10 (m + 1) m [] := by
      first
        | rfl
        | simp [Nat.toDigits]
    have hL : (Nat.toDigits 10 m).length = k := by
      rw [h0, hk1]; simp
    rw [hL]
    exact ⟨hk2, hk3 hm⟩
  have hlen_pow : ∀ k : ℕ, (Nat.toDigits 10 (10 ^ k)).length = k + 1 := by
    intro k
    obtain ⟨h1, h2⟩ := spec (10 ^ k) (by positivity)
    have hp : 0 < (10:ℕ) ^ k := by positivity
    by_contra hne
    by_cases hlt : (Nat.toDigits 10 (10 ^ k)).length < k + 1
    · have h3 : (10:ℕ) ^ (Nat.toDigits 10 (10 ^ k)).length ≤ 10 ^ k := by
        first
          | exact Nat.pow_le_pow_right (by norm_num) (by omega)
          | exact Nat.pow_le_pow_right (by omega) (by omega)
          | (gcongr <;> omega)
      omega
    · have h4 : (10:ℕ) ^ (k + 2) ≤ 10 ^ (Nat.toDigits 10 (10 ^ k)).length := by
        first
          | exact Nat.pow_le_pow_right (by norm_num) (by omega)
          | exact Nat.pow_le_pow_right (by omega) (by omega)
          | (gcongr <;> omega)
      have e : (10:ℕ) ^ (k + 2) = 10 * (10 * 10 ^ k) := by ring
      omega
  have hcomp : ∀ x : ℕ, 1 < x → ¬ Nat.Prime x → 4 ≤ x := by
    intro x h1 h2
    by_contra hcon
    push_neg at hcon
    interval_cases x
    · exact h2 (by norm_num)
    · exact h2 (by norm_num)
  constructor
  · intro a b c hpre
    first
      | unfold preconditions at hpre
      | simp only [preconditions] at hpre
    obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩, hab, hbc, hac, hsum⟩ := hpre
    have ha4 : 4 ≤ a := hcomp a ha1 ha2
    have hb4 : 4 ≤ b := hcomp b hb1 hb2
    have hc4 : 4 ≤ c := hcomp c hc1 hc2
    obtain ⟨hb_lt, hb_le⟩ := spec b (by omega)
    obtain ⟨hc_lt, hc_le⟩ := spec c (by omega)
    have key : 40 * concat (concat a b) c ≤ 4101 * (a * b * c) := by
      unfold concat
      by_cases hb10 : 10 ≤ b
      · have f1 : a * (10 ^ (Nat.toDigits 10 b).length * 10 ^ (Nat.toDigits 10 c).length)
            ≤ a * (100 * (b * c)) := by
          refine Nat.mul_le_mul (le_refl a) ?_
          calc 10 ^ (Nat.toDigits 10 b).length * 10 ^ (Nat.toDigits 10 c).length
              ≤ (10 * b) * (10 * c) := Nat.mul_le_mul hb_le hc_le
            _ = 100 * (b * c) := by ring
        have f2 : b * 10 ^ (Nat.toDigits 10 c).length ≤ b * (10 * c) :=
          Nat.mul_le_mul (le_refl b) hc_le
        have f3 : 40 * c ≤ 4 * b * c :=
          Nat.mul_le_mul (show (40:ℕ) ≤ 4 * b by omega) (le_refl c)
        have f4 : 404 * (b * c) ≤ 101 * a * (b * c) :=
          Nat.mul_le_mul (show (404:ℕ) ≤ 101 * a by omega) (le_refl (b * c))
        nlinarith [f1, f2, f3, f4]
      · have hten : (10:ℕ) ^ (Nat.toDigits 10 b).length = 10 := by
          have hlt2 : (Nat.toDigits 10 b).length < 2 := by
            by_contra hcon
            push_neg at hcon
            have h100 : (10:ℕ) ^ 2 ≤ 10 ^ (Nat.toDigits 10 b).length := by
              first
                | exact Nat.pow_le_pow_right (by norm_num) hcon
                | exact Nat.pow_le_pow_right (by omega) hcon
                | (gcongr <;> omega)
            have e : (10:ℕ) ^ 2 = 100 := by norm_num
            omega
          have hgt0 : 0 < (Nat.toDigits 10 b).length := by
            by_contra hcon
            push_neg at hcon
            have hz : (Nat.toDigits 10 b).length = 0 := by omega
            rw [hz, pow_zero] at hb_lt
            omega
          have hone : (Nat.toDigits 10 b).length = 1 := by omega
          rw [hone, pow_one]
        rw [hten]
        have f1 : a * 10 ^ (Nat.toDigits 10 c).length ≤ a * (10 * c) :=
          Nat.mul_le_mul (le_refl a) hc_le
        have f2 : b * 10 ^ (Nat.toDigits 10 c).length ≤ b * (10 * c) :=
          Nat.mul_le_mul (le_refl b) hc_le
        have f3 : 4 * c ≤ a * c := Nat.mul_le_mul ha4 (le_refl c)
        have f4 : a * c * 4 ≤ a * c * b := Nat.mul_le_mul (le_refl (a * c)) hb4
        have f5 : b * c ≤ 9 * c := Nat.mul_le_mul (show b ≤ 9 by omega) (le_refl c)
        have f6 : 0 ≤ a * b * c := Nat.zero_le _
        nlinarith [f1, f2, f3, f4, f5, f6]
    have hA : (0:ℚ) < (a:ℚ) := by exact_mod_cast (show 0 < a by omega)
    have hB : (0:ℚ) < (b:ℚ) := by exact_mod_cast (show 0 < b by omega)
    have hC : (0:ℚ) < (c:ℚ) := by exact_mod_cast (show 0 < c by omega)
    have hpos : (0:ℚ) < (a:ℚ) * (b:ℚ) * (c:ℚ) := mul_pos (mul_pos hA hB) hC
    have key' : (40:ℚ) * ((concat (concat a b) c : ℕ) : ℚ)
        ≤ 4101 * ((a:ℚ) * (b:ℚ) * (c:ℚ)) := by exact_mod_cast key
    first
      | rw [div_le_div_iff hpos (by norm_num : (0:ℚ) < 40)]
      | rw [div_le_div_iff₀ hpos (by norm_num : (0:ℚ) < 40)]
      | rw [div_le_iff hpos]
      | rw [div_le_iff₀ hpos]
    linarith
  · have hbig : (100:ℕ) ≤ 10 ^ (n + 2) := by
      calc (100:ℕ) = 10 ^ 2 := by norm_num
        _ ≤ 10 ^ (n + 2) := by
            first
              | exact Nat.pow_le_pow_right (by norm_num) (by omega)
              | exact Nat.pow_le_pow_right (by omega) (by omega)
              | (gcongr <;> omega)
    have hn2 : n < 10 ^ (n + 2) := by
      have h1 := hpow n
      have h2 : (10:ℕ) ^ n ≤ 10 ^ (n + 2) := by
        first
          | exact Nat.pow_le_pow_right (by norm_num) (by omega)
          | exact Nat.pow_le_pow_right (by omega) (by omega)
          | (gcongr <;> omega)
      omega
    refine ⟨4, 10, 10 ^ (n + 2), ?_, ?_⟩
    · first
        | unfold preconditions
        | simp only [preconditions]
      refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by omega, ?_⟩,
        by norm_num, by omega, by omega, by omega⟩
      intro hp
      have hd : (2:ℕ) ∣ 10 := by norm_num
      have h2 : (2:ℕ) ∣ 10 ^ (n + 2) := dvd_pow hd (by omega)
      rcases Nat.Prime.eq_one_or_self_of_dvd hp 2 h2 with h | h <;> omega
    · have hL10 : (Nat.toDigits 10 10).length = 2 := by
        have h := hlen_pow 1
        simpa using h
      have hval : concat (concat 4 10) (10 ^ (n + 2)) = 4101 * 10 ^ (n + 2) := by
        unfold concat
        rw [hL10, hlen_pow (n + 2)]
        ring
      rw [hval]
      have hX : ((10:ℚ)) ^ (n + 2) ≠ 0 := by positivity
      push_cast
      first
        | (rw [div_eq_div_iff (by positivity) (by norm_num : (40:ℚ) ≠ 0)]; ring)
        | (field_simp; try ring)
        | field_simp
```
