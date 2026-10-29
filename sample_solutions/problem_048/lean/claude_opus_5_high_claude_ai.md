# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `8 August 2026`\
Line count: `94`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem odd_of_prime_quadratic_and_quintic (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h1 : Nat.Prime (x ^ 2 + 3 * y ^ 2 - 17))
      (h2 : Nat.Prime ((x ^ 5 + y ^ 5) / (x + y))) :
      Odd x ∧ Odd y := by
  -- x^5 + y^5 is always divisible by x + y, with an explicit natural cofactor
  have key : ∀ u v : ℕ, ∃ Q, u ^ 5 + v ^ 5 = (u + v) * Q := by
    intro u v
    rcases le_total v u with hle | hle
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
      exact ⟨k * ((v + k) ^ 3 + (v + k) * v ^ 2) + v ^ 4, by ring⟩
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
      exact ⟨k * ((u + k) ^ 3 + (u + k) * u ^ 2) + u ^ 4, by ring⟩
  -- the only positive solution of u^2 + 3 v^2 = 19
  have quad : ∀ u v : ℕ, 0 < u → 0 < v → u ^ 2 + 3 * v ^ 2 = 19 → u = 4 ∧ v = 1 := by
    intro u v hu hv h
    obtain ⟨A, hA⟩ : ∃ A, u ^ 2 = A := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, v ^ 2 = B := ⟨_, rfl⟩
    have hAB : A + 3 * B = 19 := by rw [← hA, ← hB]; exact h
    have hub : u ≤ 4 := by
      by_contra hc
      have h5 : 5 ≤ u := by omega
      have hp : 25 ≤ A := by
        rw [← hA]
        calc (25 : ℕ) = 5 ^ 2 := by norm_num
          _ ≤ u ^ 2 := Nat.pow_le_pow_left h5 2
      omega
    have hvb : v ≤ 2 := by
      by_contra hc
      have h3 : 3 ≤ v := by omega
      have hp : 9 ≤ B := by
        rw [← hB]
        calc (9 : ℕ) = 3 ^ 2 := by norm_num
          _ ≤ v ^ 2 := Nat.pow_le_pow_left h3 2
      omega
    clear hAB hA hB
    interval_cases u <;> interval_cases v <;> simp_all
  obtain ⟨D, hD⟩ := key x y
  have hpos : 0 < x + y := by omega
  have hcancel : (x + y) * D / (x + y) = D := by
    first
      | exact Nat.mul_div_cancel_left D hpos
      | exact Nat.mul_div_cancel_left _ hpos
      | exact Nat.mul_div_cancel_left D (by omega)
      | exact Nat.mul_div_cancel_left _ (by omega)
      | exact Nat.div_eq_of_eq_mul_left hpos (by ring)
      | (rw [Nat.mul_comm]; exact Nat.mul_div_cancel hpos)
      | simp [Nat.mul_div_cancel_left, hpos]
  rw [hD, hcancel] at h2
  -- mixed parity is impossible
  have mixed : ∀ t : ℕ, x ^ 2 + 3 * y ^ 2 = 2 * t + 1 → False := by
    intro t hpar
    obtain ⟨A, hA⟩ : ∃ A, x ^ 2 = A := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, y ^ 2 = B := ⟨_, rfl⟩
    rw [hA, hB] at hpar h1
    have h2le : 2 ≤ A + 3 * B - 17 := h1.two_le
    have hdvd : (2 : ℕ) ∣ (A + 3 * B - 17) := ⟨(A + 3 * B - 17) / 2, by omega⟩
    have hN : A + 3 * B = 19 := by
      rcases h1.eq_one_or_self_of_dvd 2 hdvd with hh | hh
      · omega
      · omega
    have hN2 : x ^ 2 + 3 * y ^ 2 = 19 := by rw [hA, hB]; exact hN
    obtain ⟨rfl, rfl⟩ := quad x y hx hy hN2
    norm_num at hD
    have hD5 : D = 205 := by omega
    rw [hD5] at h2
    exact absurd h2 (by norm_num)
  rcases Nat.even_or_odd x with hex | hox
  · exfalso
    obtain ⟨a, ha⟩ := hex
    rcases Nat.even_or_odd y with hey | hoy
    · -- both even: the quintic quotient is 16 * E, hence not prime
      obtain ⟨b, hb⟩ := hey
      obtain ⟨E, hE⟩ := key a b
      have hcalc : 2 * (a + b) * (16 * E) = 2 * (a + b) * D := by
        calc 2 * (a + b) * (16 * E) = 32 * ((a + b) * E) := by ring
          _ = 32 * (a ^ 5 + b ^ 5) := by rw [← hE]
          _ = (a + a) ^ 5 + (b + b) ^ 5 := by ring
          _ = ((a + a) + (b + b)) * D := by rw [← ha, ← hb]; exact hD
          _ = 2 * (a + b) * D := by ring
      have hab : 0 < 2 * (a + b) := by omega
      have hDE : 16 * E = D := Nat.eq_of_mul_eq_mul_left hab hcalc
      rcases h2.eq_one_or_self_of_dvd 2 ⟨8 * E, by omega⟩ with hh | hh
      · omega
      · omega
    · obtain ⟨c, hc⟩ := hoy
      exact mixed (2 * a ^ 2 + 6 * c ^ 2 + 6 * c + 1) (by rw [ha, hc]; ring)
  · rcases Nat.even_or_odd y with hey | hoy
    · exfalso
      obtain ⟨b, hb⟩ := hey
      obtain ⟨c, hc⟩ := hox
      exact mixed (2 * c ^ 2 + 2 * c + 6 * b ^ 2) (by rw [hc, hb]; ring)
    · exact ⟨hox, hoy⟩
```
