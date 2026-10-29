# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `29 July 2026`\
Line count: `67`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem no_x_sq_plus_two_x_dvd_y_sq_plus_one (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    ¬ (x^2 + 2*x ∣ y^2 + 1) := by
  -- A prime `p ≡ 3 [MOD 4]` never divides `z^2 + 1`.
  have prime_case : ∀ p : ℕ, p.Prime → p % 4 = 3 → ∀ z : ℕ, ¬ (p ∣ z ^ 2 + 1) := by
    intro p hp hp4 z hdvd
    haveI : Fact p.Prime := ⟨hp⟩
    have h0 : ((z ^ 2 + 1 : ℕ) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hdvd
    push_cast at h0
    have hsq : IsSquare (-1 : ZMod p) := ⟨(z : ZMod p), by linear_combination -h0⟩
    exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp4
  -- Hence no `m ≡ 3 [MOD 4]` divides `z^2 + 1` (strong induction, bounded by `N`).
  have key : ∀ N m : ℕ, m ≤ N → m % 4 = 3 → ∀ z : ℕ, ¬ (m ∣ z ^ 2 + 1) := by
    intro N
    induction N with
    | zero => intro m hm h3 z _; omega
    | succ N ih =>
      intro m hm h3 z hdvd
      have hm1 : m ≠ 1 := by omega
      obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
      obtain ⟨c, hc⟩ := hpm
      have hp2 : p ≠ 2 := by
        intro h
        rw [h] at hc
        omega
      have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
      have hmod : m % 4 = p % 4 * (c % 4) % 4 := by rw [hc]; exact Nat.mul_mod p c 4
      have hcase : p % 4 = 3 ∨ c % 4 = 3 := by
        have h1 : p % 4 = 1 ∨ p % 4 = 3 := by omega
        have h2 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
        rcases h1 with h | h <;> rcases h2 with h' | h' | h' | h' <;>
          rw [h, h'] at hmod <;> omega
      rcases hcase with h | h
      · have hpd : p ∣ m := ⟨c, hc⟩
        exact prime_case p hp h z (hpd.trans hdvd)
      · have hc0 : 0 < c := by omega
        have hclt : c < m := by
          have h2 := hp.two_le
          have hle : 2 * c ≤ p * c := Nat.mul_le_mul h2 (le_refl c)
          have hlt : c < 2 * c := by omega
          rw [hc]
          exact lt_of_lt_of_le hlt hle
        have hcd : c ∣ m := ⟨p, by rw [hc]; ring⟩
        exact ih c (by omega) h z (hcd.trans hdvd)
  -- `4` never divides `z^2 + 1`.
  have key4 : ∀ z : ℕ, ¬ ((4 : ℕ) ∣ z ^ 2 + 1) := by
    intro z hz
    obtain ⟨q, hq⟩ := hz
    rcases Nat.even_or_odd z with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk] at hq
      have h : 4 * (k * k) + 1 = 4 * q := by rw [← hq]; ring
      omega
    · rw [hk] at hq
      have h : 4 * (k * k + k) + 2 = 4 * q := by rw [← hq]; ring
      omega
  intro hdvd
  rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `x` even: `4 ∣ x^2 + 2x`
    have h4 : (4 : ℕ) ∣ x ^ 2 + 2 * x := ⟨k * k + k, by rw [hk]; ring⟩
    exact key4 y (h4.trans hdvd)
  · -- `x` odd: `x^2 + 2x ≡ 3 [MOD 4]`
    have h3 : (x ^ 2 + 2 * x) % 4 = 3 := by
      have h : x ^ 2 + 2 * x = 4 * (k * k + 2 * k) + 3 := by rw [hk]; ring
      rw [h]; omega
    exact key _ _ (le_refl _) h3 y hdvd
```
