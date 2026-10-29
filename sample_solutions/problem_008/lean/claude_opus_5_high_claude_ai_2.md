# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `11 August 2026`\
Line count: `34`\
Turn count: `2`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem no_x_sq_plus_two_x_dvd_y_sq_plus_one (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    ¬ (x^2 + 2*x ∣ y^2 + 1) := by
  have key : ∀ N n : ℕ, n ≤ N → n % 4 = 3 → ∀ z : ℕ, ¬ n ∣ z^2 + 1 := by
    intro N; induction N with
    | zero => intro n h h3 z hd; omega
    | succ N ih =>
      intro n hN h3 z hd
      obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      haveI := Fact.mk hp
      have h2 := hp.two_le
      have hm : m ≠ 0 := by rintro rfl; simp at h3
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by rintro rfl; omega)
      rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h1 | h1
      · have h5 := Nat.mul_mod p m 4
        rw [h1, one_mul, h3] at h5
        have h6 : 2 * m ≤ p * m := Nat.mul_le_mul h2 le_rfl
        have h7 : 2 * m ≤ N + 1 := h6.trans hN
        exact ih m (by omega) (by omega) z ((dvd_mul_left m p).trans hd)
      · have h0 := (CharP.cast_eq_zero_iff (ZMod p) p (z^2+1)).2 ((dvd_mul_right p m).trans hd)
        push_cast at h0
        exact ZMod.exists_sq_eq_neg_one_iff.mp ⟨(z : ZMod p), by linear_combination -h0⟩ h1
  rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · intro hd
    have h4 : (4:ℕ) ∣ y^2 + 1 := dvd_trans ⟨k*k + k, by ring⟩ hd
    rcases Nat.even_or_odd y with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [show (a+a)^2 + 1 = 4*(a*a) + 1 by ring] at h4; omega
    · rw [show (2*a+1)^2 + 1 = 4*(a*a+a) + 2 by ring] at h4; omega
  · rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact fun hd => key (2*(j+j)+3) (2*(j+j)+3) le_rfl (by omega) y
        (dvd_trans ⟨2*(j+j)+1, by ring⟩ hd)
    · exact fun hd => key (2*(2*j+1)+1) (2*(2*j+1)+1) le_rfl (by omega) y
        (dvd_trans ⟨2*(2*j+1)+3, by ring⟩ hd)
```
