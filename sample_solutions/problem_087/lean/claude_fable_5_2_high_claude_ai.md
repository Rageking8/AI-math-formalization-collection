# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `13 November 2026`\
Line count: `249`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem double_infinite_sum_sgn_factorial_eq :
    (∑' (m : ℕ+) (n : ℕ+),
      ((Int.sign (2 * (m : ℤ) - (n : ℤ) - 5) : ℝ) + (-1 : ℝ) ^ ((min (m : ℕ) (n : ℕ)) + 3)) /
      (Nat.factorial ((max (m : ℕ) (n : ℕ)) + 1) : ℝ)) =
      (1249 : ℝ) / 120 - 4 * Real.exp 1 := by
  classical
  -- Step 0: move from `ℕ+` to `ℕ`.
  have key : ∀ G : ℕ → ℕ → ℝ,
      ∑' (m : ℕ+) (n : ℕ+), G m n = ∑' (a : ℕ) (b : ℕ), G (a + 1) (b + 1) := by
    intro G
    rw [tsum_pnat_eq_tsum_succ (f := fun m => ∑' n : ℕ+, G m n)]
    refine tsum_congr fun a => ?_
    exact tsum_pnat_eq_tsum_succ (f := fun n => G (a + 1) n)
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ → ℝ, ∀ a b, F a b =
      ((Int.sign (2 * ((a + 1 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ) - 5) : ℝ) +
        (-1 : ℝ) ^ ((min (a + 1) (b + 1)) + 3)) /
      (Nat.factorial ((max (a + 1) (b + 1)) + 1) : ℝ) := ⟨_, fun _ _ => rfl⟩
  have hgoal : (∑' (m : ℕ+) (n : ℕ+),
      ((Int.sign (2 * (m : ℤ) - (n : ℤ) - 5) : ℝ) + (-1 : ℝ) ^ ((min (m : ℕ) (n : ℕ)) + 3)) /
      (Nat.factorial ((max (m : ℕ) (n : ℕ)) + 1) : ℝ)) = ∑' (a : ℕ) (b : ℕ), F a b := by
    rw [key (fun m n => ((Int.sign (2 * (m : ℤ) - (n : ℤ) - 5) : ℝ) +
      (-1 : ℝ) ^ ((min m n) + 3)) / (Nat.factorial ((max m n) + 1) : ℝ))]
    refine tsum_congr fun a => tsum_congr fun b => ?_
    rw [hF]
  rw [hgoal]
  -- Step 1: summability on `ℕ × ℕ`.
  have hfact : ∀ k : ℕ, 4 ^ k ≤ (k + 2).factorial := by
    intro k
    cases k with
    | zero => decide
    | succ n =>
      have h := @Nat.factorial_mul_pow_le_factorial 3 n
      have h3 : Nat.factorial 3 = 6 := rfl
      rw [h3] at h
      have e : n + 1 + 2 = 3 + n := by omega
      rw [e]
      have h4 : 4 ^ (n + 1) ≤ 6 * (3 + 1) ^ n := by
        rw [pow_succ]
        have : 0 < 4 ^ n := Nat.pos_of_ne_zero (by positivity)
        norm_num
        omega
      exact le_trans h4 h
  have hD : ∀ a b : ℕ, 2 ^ a * 2 ^ b ≤ (max (a + 1) (b + 1) + 1).factorial := by
    intro a b
    have hk : ∃ k, max (a + 1) (b + 1) = k + 1 ∧ a ≤ k ∧ b ≤ k := by
      refine ⟨max a b, ?_, le_max_left _ _, le_max_right _ _⟩
      rcases le_total a b with h | h
      · rw [max_eq_right h, max_eq_right (by omega)]
      · rw [max_eq_left h, max_eq_left (by omega)]
    obtain ⟨k, hk, hak, hbk⟩ := hk
    rw [hk]
    calc 2 ^ a * 2 ^ b ≤ 2 ^ k * 2 ^ k :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hak)
            (Nat.pow_le_pow_right (by norm_num) hbk)
      _ = 4 ^ k := by rw [← mul_pow]; norm_num
      _ ≤ (k + 2).factorial := hfact k
  have hsign : ∀ x : ℤ, -1 ≤ ((Int.sign x : ℤ) : ℝ) ∧ ((Int.sign x : ℤ) : ℝ) ≤ 1 := by
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
    · rw [h]; norm_num
    · rw [Int.sign_eq_one_of_pos h]; norm_num
  have hs : Summable (fun p : ℕ × ℕ => F p.1 p.2) := by
    have hg : Summable (fun p : ℕ × ℕ => 2 * (((1 : ℝ) / 2) ^ p.1 * ((1 : ℝ) / 2) ^ p.2)) :=
      (Summable.mul_of_nonneg summable_geometric_two summable_geometric_two
        (fun _ => by positivity) (fun _ => by positivity)).mul_left 2
    refine Summable.of_abs (Summable.of_nonneg_of_le (fun _ => abs_nonneg _) ?_ hg)
    rintro ⟨a, b⟩
    simp only
    rw [hF]
    have hDpos : (0 : ℝ) < ((max (a + 1) (b + 1) + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hDle : ((2 : ℝ) ^ a * 2 ^ b) ≤ ((max (a + 1) (b + 1) + 1).factorial : ℝ) := by
      exact_mod_cast hD a b
    have hP : (0 : ℝ) < 2 ^ a * 2 ^ b := by positivity
    have hnum : |((Int.sign (2 * ((a + 1 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ) - 5) : ℤ) : ℝ) +
        (-1 : ℝ) ^ ((min (a + 1) (b + 1)) + 3)| ≤ 2 := by
      have h1 := hsign (2 * ((a + 1 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ) - 5)
      rw [abs_le]
      rcases neg_one_pow_eq_or ℝ ((min (a + 1) (b + 1)) + 3) with h2 | h2 <;> rw [h2] <;>
        constructor <;> linarith [h1.1, h1.2]
    rw [abs_div, abs_of_pos hDpos]
    calc _ ≤ 2 / ((max (a + 1) (b + 1) + 1).factorial : ℝ) := by gcongr
      _ ≤ 2 / ((2 : ℝ) ^ a * 2 ^ b) := by gcongr
      _ = 2 * (((1 : ℝ) / 2) ^ a * ((1 : ℝ) / 2) ^ b) := by
          rw [one_div_pow, one_div_pow]; field_simp
  -- Step 2: the iterated sum is the limit of the sums over squares.
  have hprod : ∑' (a : ℕ) (b : ℕ), F a b = ∑' p : ℕ × ℕ, F p.1 p.2 := by
    symm
    first
      | exact Summable.tsum_prod' hs hs.prod_factor
      | exact tsum_prod' hs hs.prod_factor
  rw [hprod]
  have hsq : Filter.Tendsto
      (fun N : ℕ => ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, F a b)
      Filter.atTop (nhds (∑' p : ℕ × ℕ, F p.1 p.2)) := by
    have h1 : Filter.Tendsto (fun s : Finset (ℕ × ℕ) => ∑ p ∈ s, F p.1 p.2)
        Filter.atTop (nhds (∑' p : ℕ × ℕ, F p.1 p.2)) := hs.hasSum
    have hmono : Monotone (fun N : ℕ => Finset.range N ×ˢ Finset.range N) := by
      intro M N hMN
      exact Finset.product_subset_product (Finset.range_mono hMN) (Finset.range_mono hMN)
    have hcov : ∀ p : ℕ × ℕ, ∃ N : ℕ, p ∈ Finset.range N ×ˢ Finset.range N := by
      rintro ⟨a, b⟩
      refine ⟨a + b + 1, ?_⟩
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      constructor <;> simp only <;> omega
    have h2 := h1.comp (Filter.tendsto_atTop_finset_of_monotone hmono hcov)
    refine h2.congr fun N => ?_
    simp only [Function.comp]
    rw [Finset.sum_product]
  -- Step 3: finite identities.
  have hpar : ∀ N : ℕ, ∑ a ∈ Finset.range N, (-1 : ℝ) ^ (a + 4) = (1 - (-1) ^ N) / 2 := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_add, pow_succ]
      norm_num
      ring
  have hsgn : ∀ N : ℕ, 5 ≤ N →
      ∑ a ∈ Finset.range N, Int.sign (2 * ((a + 1 : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ) - 5) = -5 := by
    intro N hN
    obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, ∀ a, f a =
      Int.sign (2 * ((a + 1 : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ) - 5) := ⟨_, fun _ => rfl⟩
    have hrefl : ∀ j ∈ Finset.range (N + 5), f (N + 5 - 1 - j) = - f j := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      rw [hf, hf, ← Int.sign_neg]
      congr 1
      have e : ((N + 5 - 1 - j + 1 : ℕ) : ℤ) = (N : ℤ) + 5 - j := by omega
      rw [e]
      push_cast
      ring
    have h0 : ∑ j ∈ Finset.range (N + 5), f j = 0 := by
      have h := Finset.sum_range_reflect f (N + 5)
      rw [Finset.sum_congr rfl hrefl, Finset.sum_neg_distrib] at h
      linarith
    have hpos : ∀ i : ℕ, f (N + i) = 1 := by
      intro i
      rw [hf]
      apply Int.sign_eq_one_of_pos
      push_cast
      omega
    have h5 : ∑ j ∈ Finset.range (N + 5), f j = ∑ j ∈ Finset.range N, f j + 5 := by
      rw [Finset.sum_range_add]
      simp [hpos]
    have h6 : ∑ a ∈ Finset.range N, f a = -5 := by linarith
    rw [← h6]
    exact Finset.sum_congr rfl fun a _ => (hf a).symm
  have hrow : ∀ N : ℕ, 5 ≤ N → ∀ b ∈ Finset.range (N + 1),
      F N b = (1 + (-1 : ℝ) ^ (b + 4)) / ((N + 2).factorial : ℝ) := by
    intro N hN b hb
    have hb' := Finset.mem_range.1 hb
    rw [hF, max_eq_left (by omega), min_eq_right (by omega),
      Int.sign_eq_one_of_pos (by push_cast; omega)]
    norm_num
  have hcol : ∀ N : ℕ, ∀ a ∈ Finset.range N,
      F a N = ((Int.sign (2 * ((a + 1 : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ) - 5) : ℝ) +
        (-1 : ℝ) ^ (a + 4)) / ((N + 2).factorial : ℝ) := by
    intro N a ha
    have ha' := Finset.mem_range.1 ha
    rw [hF, max_eq_right (by omega), min_eq_left (by omega)]
  have hT : ∀ N : ℕ, 5 ≤ N →
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, F a b =
        169 / 120 + ∑ k ∈ Finset.range N,
          (1 / ((k + 1).factorial : ℝ) - 5 / ((k + 2).factorial : ℝ)) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hF]
      norm_num [Nat.factorial, Int.sign_eq_one_of_pos, Int.sign_eq_neg_one_of_neg,
        show Int.sign 1 = 1 from rfl, show Int.sign 2 = 1 from rfl, show Int.sign 3 = 1 from rfl,
        show Int.sign 4 = 1 from rfl, show Int.sign 5 = 1 from rfl, show Int.sign 6 = 1 from rfl,
        show Int.sign 7 = 1 from rfl, show Int.sign 8 = 1 from rfl]
    | succ N hN ih =>
      have hstep : ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), F a b =
          ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, F a b +
            ∑ a ∈ Finset.range N, F a N + ∑ b ∈ Finset.range (N + 1), F N b := by
        rw [Finset.sum_range_succ, ← Finset.sum_add_distrib]
        congr 1
        exact Finset.sum_congr rfl fun a _ => Finset.sum_range_succ _ _
      rw [hstep, ih, Finset.sum_congr rfl (hcol N), Finset.sum_congr rfl (hrow N hN),
        ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Int.cast_sum, hsgn N hN, hpar N, hpar (N + 1),
        Finset.sum_range_succ (fun k => 1 / ((k + 1).factorial : ℝ) - 5 / ((k + 2).factorial : ℝ))]
      have e : ((N + 2).factorial : ℝ) = (N + 2) * ((N + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ (N + 1)]
        push_cast
        ring
      have hpos : (0 : ℝ) < ((N + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      rw [e, pow_succ]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      have hN2 : (N : ℝ) + 2 ≠ 0 := by positivity
      have h1 : 1 / ((N + 1).factorial : ℝ) =
          ((N : ℝ) + 2) / (((N : ℝ) + 2) * ((N + 1).factorial : ℝ)) := by
        field_simp
      rw [h1]
      ring
  -- Step 4: partial sums of `∑ 1 / n!` converge to `e`.
  have hE : Filter.Tendsto (fun n : ℕ => ∑ m ∈ Finset.range n, 1 / (m.factorial : ℝ))
      Filter.atTop (nhds (Real.exp 1)) := by
    have hz : Filter.Tendsto
        (fun n : ℕ => ∑ m ∈ Finset.range n, 1 / (m.factorial : ℝ) - Real.exp 1)
        Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat 2)
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hb := Real.exp_bound (x := 1) (by norm_num) hn
      simp only [one_pow, abs_one, one_mul] at hb
      rw [Real.norm_eq_abs, abs_sub_comm]
      refine le_trans hb ?_
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hf1 : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hf2 : (n : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial n
      have hkey : 0 ≤ (2 * (n.factorial : ℝ) - n - 1) * n := mul_nonneg (by linarith) hn'.le
      have hden : (0 : ℝ) < (n.factorial : ℝ) * n := by positivity
      first
        | rw [div_le_div_iff₀ hden hn']
        | rw [div_le_div_iff hden hn']
      push_cast
      nlinarith [hkey]
    have := hz.add_const (Real.exp 1)
    simpa using this
  have hlim : Filter.Tendsto
      (fun N : ℕ => 169 / 120 + ∑ k ∈ Finset.range N,
          (1 / ((k + 1).factorial : ℝ) - 5 / ((k + 2).factorial : ℝ)))
      Filter.atTop (nhds ((1249 : ℝ) / 120 - 4 * Real.exp 1)) := by
    have h1 := hE.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 := hE.comp (Filter.tendsto_add_atTop_nat 2)
    have h3 := ((h1.sub_const 1).sub ((h2.sub_const 2).const_mul 5)).const_add (169 / 120)
    have e : (169 : ℝ) / 120 + (Real.exp 1 - 1 - 5 * (Real.exp 1 - 2)) =
        1249 / 120 - 4 * Real.exp 1 := by ring
    rw [e] at h3
    refine h3.congr fun N => ?_
    simp only [Function.comp]
    rw [Finset.sum_range_succ' _ N, Finset.sum_range_succ' _ (N + 1), Finset.sum_range_succ' _ N,
      Finset.sum_sub_distrib]
    have h5 : ∀ x : ℕ, (5 : ℝ) / ((x + 2).factorial : ℝ) = 5 * (1 / ((x + 1 + 1).factorial : ℝ)) :=
      fun x => by ring_nf
    rw [Finset.sum_congr rfl fun x _ => h5 x, ← Finset.mul_sum]
    norm_num [Nat.factorial]
    ring
  -- Step 5: conclude by uniqueness of limits.
  refine tendsto_nhds_unique hsq (hlim.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop 5] with N hN
  exact (hT N hN).symm
```
