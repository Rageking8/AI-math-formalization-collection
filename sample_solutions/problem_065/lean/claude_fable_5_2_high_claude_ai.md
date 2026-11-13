# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `13 November 2026`\
Line count: `160`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem transcendental_sum_ceil_pi :
    Transcendental ℚ (∑' (n : ℕ+), (⌈3 * Real.pi * (n : ℝ)⌉ : ℝ) / ((5 : ℝ) ^ (n : ℕ).factorial - 1)) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, ∀ n : ℕ,
      f n = (⌈3 * Real.pi * (n : ℝ)⌉ : ℝ) / ((5 : ℝ) ^ n.factorial - 1) := ⟨_, fun _ => rfl⟩
  have hre : (∑' (n : ℕ+), (⌈3 * Real.pi * (n : ℝ)⌉ : ℝ) / ((5 : ℝ) ^ (n : ℕ).factorial - 1))
      = ∑' n : ℕ, f (n + 1) := by
    rw [← tsum_pnat_eq_tsum_succ (f := f)]
    exact tsum_congr (fun n => (hf _).symm)
  rw [hre]
  -- elementary power bounds
  have hpowN : ∀ k : ℕ, 4 * k + 1 ≤ 5 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  have hpow : ∀ k : ℕ, (4 : ℝ) * k + 1 ≤ 5 ^ k := by
    intro k; exact_mod_cast hpowN k
  have hP : ∀ k : ℕ, (5 : ℝ) ≤ 5 ^ k.factorial := by
    intro k
    have h1 := hpow k.factorial
    have h2 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
    linarith
  -- positivity of the terms
  have fpos : ∀ k : ℕ, 1 ≤ k → 0 < f k := by
    intro k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have h1 : (0 : ℝ) < 3 * Real.pi * k := mul_pos (mul_pos (by norm_num) Real.pi_pos) hk'
    have h2 : (0 : ℝ) < ⌈3 * Real.pi * (k : ℝ)⌉ := by exact_mod_cast Int.ceil_pos.mpr h1
    have h3 := hP k
    rw [hf]
    exact div_pos h2 (by linarith)
  -- upper bound for the terms
  have fle : ∀ k : ℕ, f k ≤ 5 ^ (k + 2) / 5 ^ k.factorial := by
    intro k
    have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : (⌈3 * Real.pi * (k : ℝ)⌉ : ℝ) ≤ 12 * k := by
      have : ⌈3 * Real.pi * (k : ℝ)⌉ ≤ (12 * k : ℤ) := by
        rw [Int.ceil_le]; push_cast; nlinarith [Real.pi_le_four]
      exact_mod_cast this
    have h3 := hP k
    have h4 := hpow k
    have hPpos : (0 : ℝ) < 5 ^ k.factorial := by positivity
    have e : (5 : ℝ) ^ (k + 2) = 25 * 5 ^ k := by rw [pow_add]; ring
    calc f k ≤ (12 * k) / (5 ^ k.factorial / 2) := by
          rw [hf]; gcongr; linarith
      _ = (24 * k) / 5 ^ k.factorial := by field_simp; ring
      _ ≤ 5 ^ (k + 2) / 5 ^ k.factorial := by
          gcongr
          rw [e]; linarith
  -- growth of the factorial
  have hfact : ∀ N : ℕ, 1 ≤ N → ∀ j : ℕ,
      (N + 1).factorial + 2 * j ≤ (j + N + 1).factorial := by
    intro N hN j
    induction j with
    | zero => simp
    | succ j ih =>
      have h2 : 2 ≤ (N + 1).factorial := le_trans (by omega) (Nat.self_le_factorial (N + 1))
      have e : (j + 1 + N + 1) = (j + N + 1) + 1 := by ring
      rw [e, Nat.factorial_succ (j + N + 1)]
      nlinarith [Nat.zero_le ((j + N) * (j + N + 1).factorial)]
  -- geometric bound for the shifted terms
  have hterm : ∀ N : ℕ, 1 ≤ N → ∀ j : ℕ,
      f (j + N + 1) ≤ (5 : ℝ) ^ (N + 3) / 5 ^ (N + 1).factorial * (1 / 5) ^ j := by
    intro N hN j
    have h5 : (1 : ℝ) ≤ 5 := by norm_num
    calc f (j + N + 1) ≤ 5 ^ (j + N + 1 + 2) / 5 ^ (j + N + 1).factorial := fle _
      _ ≤ 5 ^ (j + N + 1 + 2) / 5 ^ ((N + 1).factorial + 2 * j) := by
          gcongr <;> first | exact h5 | exact hfact N hN j
      _ = (5 : ℝ) ^ (N + 3) / 5 ^ (N + 1).factorial * (1 / 5) ^ j := by
          have e : j + N + 1 + 2 = (N + 3) + j := by ring
          rw [e, pow_add 5 (N + 3) j, pow_add 5 (N + 1).factorial (2 * j), pow_mul', one_div_pow]
          field_simp
  -- summability
  have hsum1 : Summable (fun j : ℕ => f (j + 1 + 1)) := by
    refine Summable.of_nonneg_of_le (fun j => (fpos _ (by omega)).le)
      (fun j => hterm 1 le_rfl j) ?_
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsum : Summable (fun n : ℕ => f (n + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ => f (n + 1)) 1).mp hsum1
  -- the sum is a Liouville number
  have hL : Liouville (∑' n : ℕ, f (n + 1)) := by
    have hxs := hsum.hasSum
    generalize (∑' n : ℕ, f (n + 1)) = x at hxs ⊢
    intro m
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = m + 2 := ⟨_, rfl⟩
    have htail : HasSum (fun n : ℕ => f (n + N + 1))
        (x - Finset.sum (Finset.range N) (fun i => f (i + 1))) :=
      (hasSum_nat_add_iff' (f := fun n : ℕ => f (n + 1)) N).mpr hxs
    have hC : (0 : ℝ) < 5 ^ (N + 3) / 5 ^ (N + 1).factorial := by positivity
    have hgeom : HasSum (fun j : ℕ => (5 : ℝ) ^ (N + 3) / 5 ^ (N + 1).factorial * (1 / 5) ^ j)
        ((5 : ℝ) ^ (N + 3) / 5 ^ (N + 1).factorial * (1 - 1 / 5)⁻¹) :=
      (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have hT_le := hasSum_le (fun j => hterm N (by omega) j) htail hgeom
    have hT_pos : 0 < x - Finset.sum (Finset.range N) (fun i => f (i + 1)) := by
      have h0 := le_hasSum htail 0 (fun j _ => (fpos _ (by omega)).le)
      exact lt_of_lt_of_le (fpos _ (by omega)) h0
    -- the partial sum is a rational number with denominator `5 ^ N! - 1`
    have hb : ((5 ^ N.factorial - 1 : ℤ) : ℝ) = 5 ^ N.factorial - 1 := by push_cast; ring
    have hPN := hP N
    have hterm_int : ∀ i : ℕ, i < N →
        ∃ z : ℤ, f (i + 1) = z / ((5 ^ N.factorial - 1 : ℤ) : ℝ) := by
      intro i hi
      obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial (show i + 1 ≤ N by omega)
      have hdvd : ((5 : ℤ) ^ (i + 1).factorial - 1) ∣ (5 ^ N.factorial - 1) := by
        have := sub_dvd_pow_sub_pow ((5 : ℤ) ^ (i + 1).factorial) 1 c
        rwa [one_pow, ← pow_mul, ← hc] at this
      obtain ⟨q, hq⟩ := hdvd
      refine ⟨⌈3 * Real.pi * ((i + 1 : ℕ) : ℝ)⌉ * q, ?_⟩
      have hqR : (5 : ℝ) ^ N.factorial - 1 = (5 ^ (i + 1).factorial - 1) * q := by
        exact_mod_cast hq
      have hd : (5 : ℝ) ^ (i + 1).factorial - 1 ≠ 0 := by
        have := hP (i + 1); linarith
      have hq0 : (q : ℝ) ≠ 0 := by
        intro h; rw [h, mul_zero] at hqR; linarith
      rw [hf, hb, hqR, Int.cast_mul, mul_div_mul_right _ _ hq0]
    have hS : ∀ M : ℕ, M ≤ N → ∃ a : ℤ,
        Finset.sum (Finset.range M) (fun i => f (i + 1)) = a / ((5 ^ N.factorial - 1 : ℤ) : ℝ) := by
      intro M
      induction M with
      | zero => intro _; exact ⟨0, by simp⟩
      | succ M ih =>
        intro hM
        obtain ⟨a, ha⟩ := ih (by omega)
        obtain ⟨z, hz⟩ := hterm_int M (by omega)
        exact ⟨a + z, by rw [Finset.sum_range_succ, ha, hz]; push_cast; ring⟩
    obtain ⟨a, ha⟩ := hS N le_rfl
    refine ⟨a, 5 ^ N.factorial - 1, ?_, ?_, ?_⟩
    · have : (5 : ℤ) ≤ 5 ^ N.factorial := by exact_mod_cast hPN
      linarith
    · rw [← ha]
      exact (sub_pos.mp hT_pos).ne'
    · rw [← ha, abs_of_pos hT_pos, hb]
      have hexp : N + 4 + N.factorial * m ≤ (N + 1).factorial := by
        rw [Nat.factorial_succ]
        have h1 := Nat.self_le_factorial N
        have h2 : (N + 1) * N.factorial = N.factorial * m + 3 * N.factorial := by
          rw [hN]; ring
        omega
      have hB : (0 : ℝ) < 5 ^ N.factorial - 1 := by linarith
      have e1 : (5 : ℝ) ^ (N + 4) / 5 ^ (N + 1).factorial
          = 5 ^ (N + 3) / 5 ^ (N + 1).factorial * 5 := by
        rw [pow_succ]; ring
      have e2 : ((1 : ℝ) - 1 / 5)⁻¹ = 5 / 4 := by norm_num
      calc x - Finset.sum (Finset.range N) (fun i => f (i + 1))
          ≤ (5 : ℝ) ^ (N + 3) / 5 ^ (N + 1).factorial * (1 - 1 / 5)⁻¹ := hT_le
        _ < 5 ^ (N + 4) / 5 ^ (N + 1).factorial := by
            rw [e1, e2]; linarith
        _ ≤ 5 ^ (N + 4) / 5 ^ (N + 4 + N.factorial * m) := by
            gcongr <;> first | exact hexp | norm_num
        _ = 1 / ((5 : ℝ) ^ N.factorial) ^ m := by
            rw [pow_add 5 (N + 4) (N.factorial * m), pow_mul]; field_simp
        _ ≤ 1 / ((5 : ℝ) ^ N.factorial - 1) ^ m := by
            apply one_div_le_one_div_of_le (pow_pos hB m)
            gcongr
            linarith
  -- conclude
  intro h
  exact hL.transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr h)
```
