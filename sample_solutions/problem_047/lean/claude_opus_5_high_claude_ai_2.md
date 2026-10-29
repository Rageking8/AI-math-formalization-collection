# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `1 September 2026`\
Line count: `56`\
Turn count: `3`

## Note

The model was explicitly told to golf the proof.

## Solution

```lean4
import Mathlib

theorem sum_floor_div_eq_implies_dvd (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : ∑' (n : ℕ), ((n : ℝ) / (2 : ℝ) ^ n) * (Int.floor ((n : ℝ) * (y : ℝ) / (x : ℝ)) : ℝ) = 6 * (y : ℝ) / (x : ℝ)) :
      x ∣ y := by
  have hxne : (x:ℝ) ≠ 0 := Nat.cast_ne_zero.2 hx.ne'
  have hr : ‖(1/2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; norm_num
  have hg0 : HasSum (fun n : ℕ => (1/2:ℝ)^n) 2 := by
    have h0 := hasSum_geometric_of_norm_lt_one hr
    rwa [show (1 - (1/2:ℝ))⁻¹ = 2 by norm_num] at h0
  have hg1 : HasSum (fun n : ℕ => (n:ℝ) * (1/2:ℝ)^n) 2 := by
    have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hr
    rwa [show (1/2:ℝ) / (1 - 1/2)^2 = 2 by norm_num] at h1
  obtain ⟨T, hT⟩ := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
  have hT6 : T = 6 := by
    have h4 : HasSum (fun n : ℕ => (1/2:ℝ) * ((n:ℝ)^2 * (1/2:ℝ)^n)
        + (n:ℝ) * (1/2:ℝ)^n + (1/2:ℝ) * (1/2:ℝ)^n) (1/2*T + 2 + 1/2*2) :=
      ((hT.mul_left (1/2)).add hg1).add (hg0.mul_left (1/2))
    have h5 : HasSum (fun n : ℕ => (n:ℝ)^2 * (1/2:ℝ)^n)
        (T + ∑ i ∈ Finset.range 1, ((i:ℝ)^2 * (1/2:ℝ)^i)) := by simpa using hT
    have h6 := (hasSum_nat_add_iff 1).2 h5
    have h7 : (fun n : ℕ => (1/2:ℝ) * ((n:ℝ)^2 * (1/2:ℝ)^n)
          + (n:ℝ) * (1/2:ℝ)^n + (1/2:ℝ) * (1/2:ℝ)^n)
        = fun n : ℕ => (((n + 1 : ℕ)):ℝ)^2 * (1/2:ℝ)^(n+1) := by
      funext n; push_cast; rw [pow_succ]; ring
    rw [h7] at h4
    have h8 := h6.unique h4
    linarith
  subst hT6
  have hG : HasSum (fun n : ℕ => ((n:ℝ)/2^n) * ((n:ℝ) * (y:ℝ) / (x:ℝ))) (6 * (y:ℝ) / (x:ℝ)) := by
    have h3 := hT.mul_left ((y:ℝ)/(x:ℝ))
    rw [show (fun n : ℕ => ((y:ℝ)/(x:ℝ)) * ((n:ℝ)^2 * (1/2:ℝ)^n))
        = fun n : ℕ => ((n:ℝ)/2^n) * ((n:ℝ) * (y:ℝ) / (x:ℝ)) by
      funext n; rw [div_pow, one_pow]; ring] at h3
    rwa [show (6:ℝ) * (y:ℝ) / (x:ℝ) = (y:ℝ)/(x:ℝ) * 6 by ring]
  have hle : ∀ n : ℕ, ((n:ℝ)/2^n) * ((⌊(n:ℝ)*(y:ℝ)/(x:ℝ)⌋ : ℤ):ℝ)
      ≤ ((n:ℝ)/2^n) * ((n:ℝ) * (y:ℝ) / (x:ℝ)) :=
    fun n => mul_le_mul_of_nonneg_left (Int.floor_le _) (by positivity)
  have hnn : ∀ n : ℕ, 0 ≤ ((n:ℝ)/2^n) * ((⌊(n:ℝ)*(y:ℝ)/(x:ℝ)⌋ : ℤ):ℝ) := fun n =>
    mul_nonneg (by positivity)
      (by exact_mod_cast Int.floor_nonneg.2 (by positivity : (0:ℝ) ≤ (n:ℝ)*(y:ℝ)/(x:ℝ)))
  have hF : HasSum (fun n : ℕ => ((n:ℝ)/2^n) * ((⌊(n:ℝ)*(y:ℝ)/(x:ℝ)⌋ : ℤ):ℝ))
      (6 * (y:ℝ) / (x:ℝ)) := by
    rw [← h]; exact (Summable.of_nonneg_of_le hnn hle hG.summable).hasSum
  have hD := hG.sub hF
  rw [sub_self] at hD
  have h1 := le_hasSum hD 1 (fun j _ => sub_nonneg.2 (hle j))
  simp only [Nat.cast_one, pow_one, one_mul] at h1
  have hfl := Int.floor_le ((y:ℝ)/(x:ℝ))
  have heq : ((⌊(y:ℝ)/(x:ℝ)⌋ : ℤ):ℝ) = (y:ℝ)/(x:ℝ) := by linarith
  have hy2 : (y:ℤ) = ⌊(y:ℝ)/(x:ℝ)⌋ * (x:ℤ) := by
    have : (y:ℝ) = ((⌊(y:ℝ)/(x:ℝ)⌋ : ℤ):ℝ) * (x:ℝ) := by rw [heq]; field_simp
    exact_mod_cast this
  have hdvd : (x:ℤ) ∣ (y:ℤ) := ⟨⌊(y:ℝ)/(x:ℝ)⌋, by rw [hy2]; ring⟩
  exact_mod_cast hdvd
```
