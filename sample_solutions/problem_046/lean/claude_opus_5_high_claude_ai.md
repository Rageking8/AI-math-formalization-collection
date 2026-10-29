# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `8 August 2026`\
Line count: `194`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem digit_sum_xyz_bounds (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h_prod : ∃ k : ℕ, 1 ≤ k ∧ x * y * z = 10 ^ k)
      (h_not_pow : (¬ ∃ a : ℕ, x = 10 ^ a) ∨ (¬ ∃ b : ℕ, y = 10 ^ b) ∨ (¬ ∃ c : ℕ, z = 10 ^ c)) :
      (Nat.digits 10 x).sum + (Nat.digits 10 y).sum + (Nat.digits 10 z).sum ≥ 8 := by
  obtain ⟨k, hk1, hxyz⟩ := h_prod
  -- digit sums of positive numbers are positive
  have D1' : ∀ N n : ℕ, n ≤ N → 0 < n → 0 < (Nat.digits 10 n).sum := by
    intro N
    induction N with
    | zero => intro n h1 h2; exfalso; omega
    | succ N ih =>
      intro n hle hn
      rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hn, List.sum_cons]
      by_cases h : n % 10 = 0
      · have h1 : 0 < n / 10 := by omega
        have h2 : n / 10 ≤ N := by omega
        have h3 := ih (n / 10) h2 h1
        omega
      · omega
  have D1 : ∀ n : ℕ, 0 < n → 0 < (Nat.digits 10 n).sum := fun n hn => D1' n n le_rfl hn
  -- digit sum dominates the last digit
  have D3 : ∀ n : ℕ, 0 < n → n % 10 ≤ (Nat.digits 10 n).sum := by
    intro n hn
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hn, List.sum_cons]
    omega
  -- multiplying by a power of ten does not change the digit sum
  have D2 : ∀ c n : ℕ, 0 < n → (Nat.digits 10 (10 ^ c * n)).sum = (Nat.digits 10 n).sum := by
    intro c
    induction c with
    | zero => intro n _; norm_num
    | succ c ih =>
      intro n hn
      have hp1 : 0 < (10:ℕ) ^ c * n := mul_pos (pow_pos (by norm_num) c) hn
      have hrw : (10:ℕ) ^ (c + 1) * n = 10 * (10 ^ c * n) := by ring
      obtain ⟨M, hM⟩ : ∃ M, (10:ℕ) ^ c * n = M := ⟨_, rfl⟩
      rw [hM] at hp1
      rw [hrw, hM, Nat.digits_def' (by norm_num : (1:ℕ) < 10) (by omega : 0 < 10 * M),
        List.sum_cons]
      have e1 : 10 * M % 10 = 0 := by omega
      have e2 : 10 * M / 10 = M := by omega
      rw [e1, e2, Nat.zero_add, ← hM]
      exact ih n hn
  have step2 : ∀ m : ℕ, 0 < m → m % 10 ≠ 0 → 2 ∣ m → 2 ≤ (Nat.digits 10 m).sum := by
    intro m hm h1 h2
    have h3 := D3 m hm
    obtain ⟨t, ht⟩ := h2
    omega
  have step5 : ∀ m : ℕ, 0 < m → m % 10 ≠ 0 → 5 ∣ m → 5 ≤ (Nat.digits 10 m).sum := by
    intro m hm h1 h2
    have h3 := D3 m hm
    obtain ⟨t, ht⟩ := h2
    omega
  have bnd2 : ∀ A B : ℕ, B < A → 2 ≤ (Nat.digits 10 (2 ^ A * 5 ^ B)).sum := by
    intro A B hBA
    obtain ⟨d, hd⟩ : ∃ d, A = B + d + 1 := ⟨A - B - 1, by omega⟩
    subst hd
    have hpos : 0 < (2:ℕ) ^ (d + 1) := pow_pos (by norm_num) _
    have heq : (2:ℕ) ^ (B + d + 1) * 5 ^ B = 10 ^ B * 2 ^ (d + 1) := by
      rw [show (10:ℕ) = 2 * 5 from by norm_num, mul_pow]
      ring
    rw [heq, D2 B (2 ^ (d + 1)) hpos]
    refine step2 _ hpos ?_ (dvd_pow_self 2 (by omega))
    intro hc
    have h10 : (10:ℕ) ∣ 2 ^ (d + 1) := Nat.dvd_of_mod_eq_zero hc
    have h5 : (5:ℕ) ∣ 2 ^ (d + 1) := dvd_trans (by norm_num) h10
    have h5' := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5
    norm_num at h5'
  have bnd5 : ∀ A B : ℕ, A < B → 5 ≤ (Nat.digits 10 (2 ^ A * 5 ^ B)).sum := by
    intro A B hAB
    obtain ⟨d, hd⟩ : ∃ d, B = A + d + 1 := ⟨B - A - 1, by omega⟩
    subst hd
    have hpos : 0 < (5:ℕ) ^ (d + 1) := pow_pos (by norm_num) _
    have heq : (2:ℕ) ^ A * 5 ^ (A + d + 1) = 10 ^ A * 5 ^ (d + 1) := by
      rw [show (10:ℕ) = 2 * 5 from by norm_num, mul_pow]
      ring
    rw [heq, D2 A (5 ^ (d + 1)) hpos]
    refine step5 _ hpos ?_ (dvd_pow_self 5 (by omega))
    intro hc
    have h10 : (10:ℕ) ∣ 5 ^ (d + 1) := Nat.dvd_of_mod_eq_zero hc
    have h2 : (2:ℕ) ∣ 5 ^ (d + 1) := dvd_trans (by norm_num) h10
    have h2' := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    norm_num at h2'
  -- divisors of powers of ten are of the form 2^a * 5^b
  have dec : ∀ N n : ℕ, n ≤ N → 0 < n → n ∣ 10 ^ k → ∃ a b : ℕ, n = 2 ^ a * 5 ^ b := by
    intro N
    induction N with
    | zero => intro n h1 h2 _; exfalso; omega
    | succ N ih =>
      intro n hle hn hdvd
      by_cases h1 : n = 1
      · exact ⟨0, 0, by simp [h1]⟩
      · obtain ⟨p, pp, hp⟩ := Nat.exists_prime_and_dvd h1
        have hp10 : p ∣ 10 := pp.dvd_of_dvd_pow (hp.trans hdvd)
        have hp25 : p = 2 ∨ p = 5 := by
          have h5 : p ∣ 2 * 5 := by simpa using hp10
          rcases (Nat.Prime.dvd_mul pp).mp h5 with h | h
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp Nat.prime_two).mp h)
          · exact Or.inr ((Nat.prime_dvd_prime_iff_eq pp (by norm_num)).mp h)
        obtain ⟨m, hm⟩ := hp
        have hm0 : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · rw [h, Nat.mul_zero] at hm; omega
          · exact h
        have hmlt : m < n := by
          have hle2 : 2 * m ≤ p * m := Nat.mul_le_mul pp.two_le (le_refl m)
          have hlt2 : m < 2 * m := by omega
          calc m < 2 * m := hlt2
            _ ≤ p * m := hle2
            _ = n := hm.symm
        have hmdvd : m ∣ 10 ^ k := dvd_trans ⟨p, by rw [hm]; ring⟩ hdvd
        obtain ⟨a, b, hab⟩ := ih m (by omega) hm0 hmdvd
        rcases hp25 with rfl | rfl
        · exact ⟨a + 1, b, by rw [hm, hab]; ring⟩
        · exact ⟨a, b + 1, by rw [hm, hab]; ring⟩
  have hxd : x ∣ 10 ^ k := ⟨y * z, by rw [← hxyz]; ring⟩
  have hyd : y ∣ 10 ^ k := ⟨x * z, by rw [← hxyz]; ring⟩
  have hzd : z ∣ 10 ^ k := ⟨x * y, by rw [← hxyz]; ring⟩
  obtain ⟨a1, b1, hx'⟩ := dec x x le_rfl hx hxd
  obtain ⟨a2, b2, hy'⟩ := dec y y le_rfl hy hyd
  obtain ⟨a3, b3, hz'⟩ := dec z z le_rfl hz hzd
  have exp_eq : ∀ A B K : ℕ, 2 ^ A * 5 ^ B = 2 ^ K * 5 ^ K → A = K ∧ B = K := by
    intro A B K h
    have hA : A = K := by
      by_contra hne
      rcases Nat.lt_or_ge A K with hlt | hge
      · obtain ⟨d, hd⟩ : ∃ d, K = A + d + 1 := ⟨K - A - 1, by omega⟩
        subst hd
        have h' : (2:ℕ) ^ A * 5 ^ B = 2 ^ A * (2 ^ (d + 1) * 5 ^ (A + d + 1)) := by
          rw [h]; ring
        have h5 : (5:ℕ) ^ B = 2 ^ (d + 1) * 5 ^ (A + d + 1) :=
          Nat.eq_of_mul_eq_mul_left (by positivity) h'
        have hd2 : (2:ℕ) ∣ 5 ^ B := by
          rw [h5]
          exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
        have hcon := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd2
        norm_num at hcon
      · obtain ⟨d, hd⟩ : ∃ d, A = K + d + 1 := ⟨A - K - 1, by omega⟩
        subst hd
        have h' : (2:ℕ) ^ K * (2 ^ (d + 1) * 5 ^ B) = 2 ^ K * 5 ^ K := by
          rw [← h]; ring
        have h5 : (2:ℕ) ^ (d + 1) * 5 ^ B = 5 ^ K :=
          Nat.eq_of_mul_eq_mul_left (by positivity) h'
        have hd2 : (2:ℕ) ∣ 5 ^ K := by
          rw [← h5]
          exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
        have hcon := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd2
        norm_num at hcon
    refine ⟨hA, ?_⟩
    rw [hA] at h
    have h5 : (5:ℕ) ^ B = 5 ^ K := Nat.eq_of_mul_eq_mul_left (by positivity) h
    exact Nat.pow_right_injective (by norm_num) h5
  have key : (2:ℕ) ^ (a1 + a2 + a3) * 5 ^ (b1 + b2 + b3) = 2 ^ k * 5 ^ k := by
    have h1 : (2:ℕ) ^ (a1 + a2 + a3) * 5 ^ (b1 + b2 + b3) = x * y * z := by
      rw [hx', hy', hz']; ring
    rw [h1, hxyz, show (10:ℕ) = 2 * 5 from by norm_num, mul_pow]
  obtain ⟨hs1, hs2⟩ := exp_eq _ _ _ key
  have hnp : a1 ≠ b1 ∨ a2 ≠ b2 ∨ a3 ≠ b3 := by
    rcases h_not_pow with h | h | h
    · refine Or.inl ?_
      intro hc
      exact h ⟨a1, by rw [hx', hc, show (10:ℕ) = 2 * 5 from by norm_num, mul_pow]⟩
    · refine Or.inr (Or.inl ?_)
      intro hc
      exact h ⟨a2, by rw [hy', hc, show (10:ℕ) = 2 * 5 from by norm_num, mul_pow]⟩
    · refine Or.inr (Or.inr ?_)
      intro hc
      exact h ⟨a3, by rw [hz', hc, show (10:ℕ) = 2 * 5 from by norm_num, mul_pow]⟩
  have hcase : (b1 < a1 ∧ a2 < b2) ∨ (b1 < a1 ∧ a3 < b3) ∨ (b2 < a2 ∧ a1 < b1) ∨
      (b2 < a2 ∧ a3 < b3) ∨ (b3 < a3 ∧ a1 < b1) ∨ (b3 < a3 ∧ a2 < b2) := by
    omega
  have Sx1 := D1 x hx
  have Sy1 := D1 y hy
  have Sz1 := D1 z hz
  have Bx2 : b1 < a1 → 2 ≤ (Nat.digits 10 x).sum := by
    intro h; rw [hx']; exact bnd2 a1 b1 h
  have Bx5 : a1 < b1 → 5 ≤ (Nat.digits 10 x).sum := by
    intro h; rw [hx']; exact bnd5 a1 b1 h
  have By2 : b2 < a2 → 2 ≤ (Nat.digits 10 y).sum := by
    intro h; rw [hy']; exact bnd2 a2 b2 h
  have By5 : a2 < b2 → 5 ≤ (Nat.digits 10 y).sum := by
    intro h; rw [hy']; exact bnd5 a2 b2 h
  have Bz2 : b3 < a3 → 2 ≤ (Nat.digits 10 z).sum := by
    intro h; rw [hz']; exact bnd2 a3 b3 h
  have Bz5 : a3 < b3 → 5 ≤ (Nat.digits 10 z).sum := by
    intro h; rw [hz']; exact bnd5 a3 b3 h
  rcases hcase with ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩ | ⟨p1, p2⟩
  · have e1 := Bx2 p1; have e2 := By5 p2; omega
  · have e1 := Bx2 p1; have e2 := Bz5 p2; omega
  · have e1 := By2 p1; have e2 := Bx5 p2; omega
  · have e1 := By2 p1; have e2 := Bz5 p2; omega
  · have e1 := Bz2 p1; have e2 := Bx5 p2; omega
  · have e1 := Bz2 p1; have e2 := By5 p2; omega
```
