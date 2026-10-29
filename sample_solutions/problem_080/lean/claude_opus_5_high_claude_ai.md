# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `26 August 2026`\
Line count: `183`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem factorial_add_one_div_eq_iff_x_two_y_three
    (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
      ((x + y - 1).factorial + 1 : ℚ) / (x + y : ℚ) + 59 =
      (x.factorial : ℚ) ^ (y + 3) ↔ x = 2 ∧ y = 3 := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
    have hsub : a + 1 + y - 1 = a + y := by omega
    rw [hsub] at h
    have hcast : ((a + 1 : ℕ) : ℚ) + (y : ℚ) = ((a + 1 + y : ℕ) : ℚ) := by push_cast; ring
    rw [hcast] at h
    have hN : ((a + 1 + y : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h4 : (((a + y).factorial : ℚ) + 1) / ((a + 1 + y : ℕ) : ℚ)
        = ((a + 1).factorial : ℚ) ^ (y + 3) - 59 := by linarith
    have h5 : ((a + y).factorial : ℚ) + 1
        = (((a + 1).factorial : ℚ) ^ (y + 3) - 59) * ((a + 1 + y : ℕ) : ℚ) := by
      rw [← h4]; field_simp
    have key : (a + y).factorial + 1 + 59 * (a + 1 + y)
        = ((a + 1).factorial) ^ (y + 3) * (a + 1 + y) := by
      have h7 : (((a + y).factorial + 1 + 59 * (a + 1 + y) : ℕ) : ℚ)
          = ((((a + 1).factorial) ^ (y + 3) * (a + 1 + y) : ℕ) : ℚ) := by
        push_cast
        push_cast at h5
        linear_combination h5
      exact_mod_cast h7
    clear h h4 h5 hcast hN hsub
    have two_pow_gt : ∀ m : ℕ, m < 2 ^ m := by
      intro m
      induction m with
      | zero => norm_num
      | succ m ih =>
        have h1 : (2:ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
        omega
    have pow_ge : ∀ b m : ℕ, 2 ≤ b → m + 1 ≤ b ^ m := by
      intro b m hb
      have h1 : (2:ℕ) ^ m ≤ b ^ m := Nat.pow_le_pow_left hb m
      have h2 := two_pow_gt m
      omega
    have pow_dvd : ∀ m : ℕ, ((a + 1).factorial) ^ m ∣ ((a + 1) * m).factorial := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have h2 := Nat.factorial_mul_factorial_dvd_factorial_add ((a + 1) * m) (a + 1)
        have h3 : (a + 1) * m + (a + 1) = (a + 1) * (m + 1) := by ring
        rw [h3] at h2
        have h4 : ((a + 1).factorial) ^ (m + 1)
            = ((a + 1).factorial) ^ m * (a + 1).factorial := pow_succ _ _
        rw [h4]
        exact dvd_trans (mul_dvd_mul_right ih _) h2
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exfalso
      have h1 : (0 + 1).factorial = 1 := by decide
      rw [h1, one_pow, one_mul] at key
      have h2 := Nat.factorial_pos (0 + y)
      omega
    have hkex : ∀ q z : ℕ, z ≤ q → 1 ≤ z →
        ∃ k, 1 ≤ k ∧ z ≤ k * (a + 1) ∧ k * (a + 1) ≤ a + z := by
      intro q
      induction q with
      | zero => intro z hz hz1; exfalso; omega
      | succ q ih =>
        intro z hz hz1
        by_cases hc : z ≤ a + 1
        · exact ⟨1, le_refl 1, by omega, by omega⟩
        · obtain ⟨k', hk1', hk2', hk3'⟩ := ih (z - (a + 1)) (by omega) (by omega)
          have he : (k' + 1) * (a + 1) = k' * (a + 1) + (a + 1) := by ring
          exact ⟨k' + 1, by omega, by omega, by omega⟩
    obtain ⟨k, hk3, hy_le, hk1⟩ := hkex y y (le_refl y) hy
    have hk4 : k ≤ y + 3 := by
      by_contra hc
      push_neg at hc
      have h8 : (y + 4) * (a + 1) ≤ k * (a + 1) := Nat.mul_le_mul (by omega) (le_refl (a + 1))
      have h9 : (y + 4) * (a + 1) = y * a + y + 4 * a + 4 := by ring
      omega
    have hdvd1 : ((a + 1).factorial) ^ k ∣ (a + y).factorial := by
      refine dvd_trans (pow_dvd k) (Nat.factorial_dvd_factorial ?_)
      calc (a + 1) * k = k * (a + 1) := Nat.mul_comm _ _
        _ ≤ a + y := hk1
    have hdvd2 : ((a + 1).factorial) ^ k ∣ ((a + 1).factorial) ^ (y + 3) * (a + 1 + y) :=
      dvd_mul_of_dvd_left (pow_dvd_pow _ hk4) _
    have hdvd3 : ((a + 1).factorial) ^ k ∣ 1 + 59 * (a + 1 + y) := by
      have heq : (a + y).factorial + (1 + 59 * (a + 1 + y))
          = ((a + 1).factorial) ^ (y + 3) * (a + 1 + y) := by omega
      rw [← heq] at hdvd2
      first
        | exact (Nat.dvd_add_right hdvd1).mp hdvd2
        | exact (Nat.dvd_add_right_iff hdvd1).mp hdvd2
        | simpa [Nat.dvd_add_right hdvd1] using hdvd2
    have hle : ((a + 1).factorial) ^ k ≤ 1 + 59 * (a + 1 + y) := Nat.le_of_dvd (by omega) hdvd3
    have e0 : (a + 1) * (k + 1) = k * (a + 1) + (a + 1) := by ring
    have hle2 : ((a + 1).factorial) ^ k ≤ 59 * ((a + 1) * (k + 1)) + 1 := by omega
    rcases le_or_gt 5 a with ha5 | ha5
    · exfalso
      have hfact_gen : ∀ m : ℕ, 120 * (m + 6) ≤ (m + 6).factorial := by
        intro m
        induction m with
        | zero => norm_num [Nat.factorial]
        | succ m ih =>
          have h1 : m + 1 + 6 = (m + 6) + 1 := by ring
          rw [h1, Nat.factorial_succ]
          have h2 : 120 * ((m + 6) + 1) ≤ ((m + 6) + 1) * (120 * (m + 6)) := by
            calc 120 * ((m + 6) + 1) = ((m + 6) + 1) * 120 := by ring
              _ ≤ ((m + 6) + 1) * (120 * (m + 6)) := Nat.mul_le_mul (le_refl _) (by omega)
          exact le_trans h2 (Nat.mul_le_mul (le_refl _) ih)
      have hfact : 120 * (a + 1) ≤ (a + 1).factorial := by
        obtain ⟨m, hm⟩ : ∃ m, a + 1 = m + 6 := ⟨a - 5, by omega⟩
        rw [hm]; exact hfact_gen m
      obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hF2 : 2 ≤ (a + 1).factorial := by omega
      have hp1 : (2:ℕ) ^ j ≤ ((a + 1).factorial) ^ j := Nat.pow_le_pow_left hF2 j
      have hp2 : (a + 1).factorial * 2 ^ j ≤ ((a + 1).factorial) ^ k := by
        calc (a + 1).factorial * 2 ^ j
            ≤ (a + 1).factorial * ((a + 1).factorial) ^ j := Nat.mul_le_mul (le_refl _) hp1
          _ = ((a + 1).factorial) ^ j * (a + 1).factorial := Nat.mul_comm _ _
          _ = ((a + 1).factorial) ^ k := by rw [hj, pow_succ]
      have hp3 : 120 * (a + 1) * 2 ^ j ≤ (a + 1).factorial * 2 ^ j :=
        Nat.mul_le_mul hfact (le_refl _)
      have hp4 : j + 2 ≤ 2 ^ (j + 1) := by
        have h10 := two_pow_gt (j + 1)
        omega
      have hp5 : 60 * ((a + 1) * (k + 1)) ≤ 120 * (a + 1) * 2 ^ j := by
        have e1 : 120 * (a + 1) * 2 ^ j = 60 * ((a + 1) * (2 * 2 ^ j)) := by ring
        have e2 : (2:ℕ) * 2 ^ j = 2 ^ (j + 1) := by ring
        have e3 : (a + 1) * (k + 1) ≤ (a + 1) * 2 ^ (j + 1) :=
          Nat.mul_le_mul (le_refl (a + 1)) (by omega)
        rw [e1, e2]
        omega
      have hbig : 6 * 2 ≤ (a + 1) * (k + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    · interval_cases a
      · have hf : ((1 + 1).factorial) ^ k = 2 ^ k := by norm_num [Nat.factorial]
        have hk10 : k ≤ 10 := by
          by_contra hc
          push_neg at hc
          obtain ⟨m, hm⟩ : ∃ m, k = m + 11 := ⟨k - 11, by omega⟩
          have e1 : (2:ℕ) ^ k = 2048 * 2 ^ m := by rw [hm]; ring
          have h1 : m + 1 ≤ 2 ^ m := pow_ge 2 m (le_refl 2)
          have h2 : 2048 * (m + 1) ≤ 2048 * 2 ^ m := Nat.mul_le_mul (le_refl _) h1
          omega
        have hyb : y ≤ 20 := by omega
        clear hdvd1 hdvd2 hdvd3 hle hle2 hf hk1 hk4 hy_le e0
        interval_cases y <;> revert key <;> norm_num [Nat.factorial]
      · have hf : ((2 + 1).factorial) ^ k = 6 ^ k := by norm_num [Nat.factorial]
        have hk10 : k ≤ 3 := by
          by_contra hc
          push_neg at hc
          obtain ⟨m, hm⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
          have e1 : (6:ℕ) ^ k = 1296 * 6 ^ m := by rw [hm]; ring
          have h1 : m + 1 ≤ 6 ^ m := pow_ge 6 m (by norm_num)
          have h2 : 1296 * (m + 1) ≤ 1296 * 6 ^ m := Nat.mul_le_mul (le_refl _) h1
          omega
        have hyb : y ≤ 9 := by omega
        clear hdvd1 hdvd2 hdvd3 hle hle2 hf hk1 hk4 hy_le e0
        interval_cases y <;> revert key <;> norm_num [Nat.factorial]
      · have hf : ((3 + 1).factorial) ^ k = 24 ^ k := by norm_num [Nat.factorial]
        have hk10 : k ≤ 2 := by
          by_contra hc
          push_neg at hc
          obtain ⟨m, hm⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
          have e1 : (24:ℕ) ^ k = 13824 * 24 ^ m := by rw [hm]; ring
          have h1 : m + 1 ≤ 24 ^ m := pow_ge 24 m (by norm_num)
          have h2 : 13824 * (m + 1) ≤ 13824 * 24 ^ m := Nat.mul_le_mul (le_refl _) h1
          omega
        have hyb : y ≤ 8 := by omega
        clear hdvd1 hdvd2 hdvd3 hle hle2 hf hk1 hk4 hy_le e0
        interval_cases y <;> revert key <;> norm_num [Nat.factorial]
      · have hf : ((4 + 1).factorial) ^ k = 120 ^ k := by norm_num [Nat.factorial]
        have hk10 : k ≤ 1 := by
          by_contra hc
          push_neg at hc
          obtain ⟨m, hm⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
          have e1 : (120:ℕ) ^ k = 14400 * 120 ^ m := by rw [hm]; ring
          have h1 : m + 1 ≤ 120 ^ m := pow_ge 120 m (by norm_num)
          have h2 : 14400 * (m + 1) ≤ 14400 * 120 ^ m := Nat.mul_le_mul (le_refl _) h1
          omega
        have hyb : y ≤ 5 := by omega
        clear hdvd1 hdvd2 hdvd3 hle hle2 hf hk1 hk4 hy_le e0
        interval_cases y <;> revert key <;> norm_num [Nat.factorial]
  · rintro ⟨rfl, rfl⟩
    norm_num [Nat.factorial]
```
