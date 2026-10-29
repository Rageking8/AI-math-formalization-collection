# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `1 September 2026`\
Line count: `60`\
Turn count: `1`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem neither_x_nor_y_prime (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : 2 * (x : ℤ) ^ 2 + (x : ℤ) * (y : ℤ) + (y : ℤ) ^ 2 = 7 * ((x : ℤ) - (y : ℤ)) ^ 4) :
      ¬ Nat.Prime x ∧ ¬ Nat.Prime y := by
  have hx1 : (1:ℤ) ≤ (x:ℤ) := by exact_mod_cast hx
  have hy1 : (1:ℤ) ≤ (y:ℤ) := by exact_mod_cast hy
  have hne : (x:ℤ) ≠ (y:ℤ) := fun h0 => by
    rw [h0] at h; nlinarith [sq_nonneg ((y:ℤ) - 1)]
  have gen : ∀ D : ℤ, 4 ≤ D * D → 7 * ((D * D) * (D * D)) ≤ 11 * (D * D) → False :=
    fun D h1 h2 => by nlinarith
  have key : ((x:ℤ) - (y:ℤ)) ∣ 4 → x = 6 ∧ y = 4 := by
    intro hd
    have h1 : (x:ℤ) - (y:ℤ) ≤ 4 := Int.le_of_dvd (by norm_num) hd
    have h2 : -(4:ℤ) ≤ (x:ℤ) - (y:ℤ) := by
      have := Int.le_of_dvd (show (0:ℤ) < 4 by norm_num) (neg_dvd.mpr hd); linarith
    have core : ∀ Y D : ℤ, 1 ≤ Y → -4 ≤ D → D ≤ 4 →
        4 * (Y * Y) + 5 * (D * Y) + 2 * (D * D) = 7 * ((D * D) * (D * D)) → Y = 4 ∧ D = 2 := by
      intro Y D hY hD1 hD2 he
      have e1 : D * D ≤ 16 := by nlinarith
      have e2 : (D * D) * (D * D) ≤ 256 := by nlinarith [mul_self_nonneg D]
      have e3 : Y ≤ 24 := by
        nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ D + 4) (by linarith : (0:ℤ) ≤ Y),
          mul_self_nonneg D]
      interval_cases D <;> interval_cases Y <;> omega
    obtain ⟨c1, c2⟩ := core (y:ℤ) ((x:ℤ) - (y:ℤ)) hy1 h2 h1 (by linear_combination h)
    omega
  have main : ∀ p : ℕ, p.Prime → ((x:ℤ) - (y:ℤ)) ∣ 4 * (p:ℤ) ^ 2 →
      ((x:ℤ) - (y:ℤ)).natAbs < p → ((x:ℤ) - (y:ℤ)) ∣ 4 := by
    intro p hp hdvd hlt
    have h1 : ((x:ℤ) - (y:ℤ)).natAbs ∣ 4 * p ^ 2 := by
      have := Int.natAbs_dvd.mpr hdvd; exact_mod_cast this
    have h2 : ¬ p ∣ ((x:ℤ) - (y:ℤ)).natAbs := fun hc => by
      have := Nat.le_of_dvd (by omega) hc; omega
    have h3 : ((x:ℤ) - (y:ℤ)).natAbs ∣ 4 :=
      (((hp.coprime_iff_not_dvd).mpr h2).symm.pow_right 2).dvd_of_dvd_mul_right h1
    exact Int.natAbs_dvd.mp (by exact_mod_cast h3)
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · have hx2 : (2:ℤ) ≤ (x:ℤ) := by exact_mod_cast hp.two_le
    have hlt : -(x:ℤ) < (x:ℤ) - (y:ℤ) := by
      by_contra hcon
      push_neg at hcon
      refine gen ((x:ℤ) - (y:ℤ)) (by nlinarith [sq_nonneg ((x:ℤ) - (y:ℤ) + 2)]) ?_
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ (y:ℤ) - 2*(x:ℤ)) (by linarith : (0:ℤ) ≤ (y:ℤ)),
        mul_nonneg (by linarith : (0:ℤ) ≤ (y:ℤ) - 2*(x:ℤ)) (by linarith : (0:ℤ) ≤ (y:ℤ) - (x:ℤ)),
        sq_nonneg (x:ℤ), sq_nonneg (y:ℤ)]
    obtain ⟨e1, e2⟩ := key (main x hp
      ⟨7 * ((x:ℤ) - (y:ℤ)) ^ 3 + 3 * (x:ℤ) - ((x:ℤ) - (y:ℤ)), by linear_combination h⟩ (by omega))
    rw [e1] at hp; norm_num at hp
  · have hy2 : (2:ℤ) ≤ (y:ℤ) := by exact_mod_cast hp.two_le
    have hlt : (x:ℤ) - (y:ℤ) < (y:ℤ) := by
      by_contra hcon
      push_neg at hcon
      refine gen ((x:ℤ) - (y:ℤ)) (by nlinarith [sq_nonneg ((x:ℤ) - (y:ℤ) - 2)]) ?_
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ (x:ℤ) - 2*(y:ℤ)) (by linarith : (0:ℤ) ≤ (x:ℤ)),
        mul_nonneg (by linarith : (0:ℤ) ≤ (x:ℤ) - 2*(y:ℤ)) (by linarith : (0:ℤ) ≤ (x:ℤ) - (y:ℤ)),
        sq_nonneg (x:ℤ), sq_nonneg (y:ℤ)]
    obtain ⟨e1, e2⟩ := key (main y hp
      ⟨7 * ((x:ℤ) - (y:ℤ)) ^ 3 - 5 * (y:ℤ) - 2 * ((x:ℤ) - (y:ℤ)), by linear_combination h⟩ (by omega))
    rw [e2] at hp; norm_num at hp
```
