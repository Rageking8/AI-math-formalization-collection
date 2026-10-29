# Gemini 3.6 Flash High (AI Studio)

Model: `Gemini 3.6 Flash High` (via AI Studio)\
Date: `8 August 2026`\
Line count: `42`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem abs_mod_mod_sub_mod_le (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    |((x % y % z : ℤ) - (x % z : ℤ))| ≤ (z : ℤ) - Nat.gcd y z := by
  set g := Nat.gcd y z
  obtain ⟨y', hy_eq⟩ := Nat.gcd_dvd_left y z
  obtain ⟨z', hz_eq⟩ := Nat.gcd_dvd_right y z
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right y hz
  have hu_lt : x % y % z < z := Nat.mod_lt _ hz
  have hv_lt : x % z < z := Nat.mod_lt _ hz
  have hu_lt' : (x % y % z : ℤ) < (z : ℤ) := by exact_mod_cast hu_lt
  have hv_lt' : (x % z : ℤ) < (z : ℤ) := by exact_mod_cast hv_lt
  have hu_ge : 0 ≤ (x % y % z : ℤ) := Nat.cast_nonneg _
  have hv_ge : 0 ≤ (x % z : ℤ) := Nat.cast_nonneg _
  have h_abs_bound : |((x % y % z : ℤ) - (x % z : ℤ))| ≤ (z : ℤ) - 1 := by
    rw [abs_le]
    constructor <;> omega
  have h1 : (x : ℤ) = (y : ℤ) * (x / y : ℤ) + (x % y : ℤ) := by exact_mod_cast (Nat.div_add_mod x y).symm
  have h2 : (x % y : ℤ) = (z : ℤ) * ((x % y) / z : ℤ) + (x % y % z : ℤ) := by exact_mod_cast (Nat.div_add_mod (x % y) z).symm
  have h3 : (x : ℤ) = (z : ℤ) * (x / z : ℤ) + (x % z : ℤ) := by exact_mod_cast (Nat.div_add_mod x z).symm
  have h4 : (y : ℤ) = (g : ℤ) * (y' : ℤ) := by exact_mod_cast hy_eq
  have h5 : (z : ℤ) = (g : ℤ) * (z' : ℤ) := by exact_mod_cast hz_eq
  set K : ℤ := (z' : ℤ) * ((x / z : ℤ) - ((x % y) / z : ℤ)) - (y' : ℤ) * (x / y : ℤ)
  have hK : (x % y % z : ℤ) - (x % z : ℤ) = (g : ℤ) * K := by
    linear_combination -h2 - h1 + h3 - (x / y : ℤ) * h4 + ((x / z : ℤ) - ((x % y) / z : ℤ)) * h5
  have hg_nonneg : 0 ≤ (g : ℤ) := Nat.cast_nonneg _
  have h_abs_K : |((x % y % z : ℤ) - (x % z : ℤ))| = (g : ℤ) * |K| := by
    rw [hK, abs_mul, abs_of_nonneg hg_nonneg]
  have h_gk_bound : (g : ℤ) * |K| ≤ (z : ℤ) - 1 := by
    rw [← h_abs_K]
    exact h_abs_bound
  have h_strict : (g : ℤ) * |K| < (g : ℤ) * (z' : ℤ) := by linarith [h_gk_bound, h5]
  have h_K_lt : |K| < (z' : ℤ) := by
    by_contra h
    push_neg at h
    have : (g : ℤ) * (z' : ℤ) ≤ (g : ℤ) * |K| := by nlinarith
    linarith
  have h_K_le : |K| ≤ (z' : ℤ) - 1 := by omega
  calc
    |((x % y % z : ℤ) - (x % z : ℤ))| = (g : ℤ) * |K| := h_abs_K
    _ ≤ (g : ℤ) * ((z' : ℤ) - 1) := mul_le_mul_of_nonneg_left h_K_le hg_nonneg
    _ = (z : ℤ) - Nat.gcd y z := by linarith [h5]
```
