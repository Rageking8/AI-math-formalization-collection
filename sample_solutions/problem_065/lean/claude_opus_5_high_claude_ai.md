# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `19 August 2026`\
Line count: `306`\
Turn count: `3`

## Solution

```lean4
import Mathlib

open Finset

namespace CeilPiLiouville

/-! ## Hand-rolled helpers (no fragile division/power lemma names) -/

lemma div_le_div_cross {a b c d : ℝ} (hc : 0 < c) (hd : 0 < d) (h : a * c ≤ b * d) :
    a / d ≤ b / c := by
  have key : b / c - a / d = (b * d - c * a) / (c * d) :=
    div_sub_div b a (ne_of_gt hc) (ne_of_gt hd)
  have h1 : 0 ≤ (b * d - c * a) / (c * d) :=
    div_nonneg (by nlinarith) (by positivity)
  linarith

lemma div_lt_div_cross {a b c d : ℝ} (hc : 0 < c) (hd : 0 < d) (h : a * c < b * d) :
    a / d < b / c := by
  have key : b / c - a / d = (b * d - c * a) / (c * d) :=
    div_sub_div b a (ne_of_gt hc) (ne_of_gt hd)
  have h1 : 0 < (b * d - c * a) / (c * d) :=
    div_pos (by nlinarith) (by positivity)
  linarith

lemma pow_le_pow_aux {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n := by
  have hb : 0 ≤ b := le_trans ha hab
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : a ^ n * a ≤ b ^ n * a := mul_le_mul_of_nonneg_right ih ha
      have h2 : b ^ n * a ≤ b ^ n * b := mul_le_mul_of_nonneg_left hab (pow_nonneg hb n)
      calc a ^ (n + 1) = a ^ n * a := pow_succ a n
        _ ≤ b ^ n * b := le_trans h1 h2
        _ = b ^ (n + 1) := (pow_succ b n).symm

lemma one_le_fact (m : ℕ) : 1 ≤ Nat.factorial m := Nat.factorial_pos m

lemma five_le_pow {m : ℕ} (hm : 1 ≤ m) : (5 : ℝ) ≤ (5 : ℝ) ^ m := by
  calc (5 : ℝ) = 5 ^ 1 := (pow_one 5).symm
    _ ≤ 5 ^ m := pow_le_pow_right₀ (by norm_num) hm

lemma succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
      have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      omega

lemma add_le_mul_two_pow (M j : ℕ) (hM : 1 ≤ M) : M + j ≤ M * 2 ^ j := by
  have h1 : M * (j + 1) ≤ M * 2 ^ j := Nat.mul_le_mul le_rfl (succ_le_two_pow j)
  have h2 : j ≤ M * j := Nat.le_mul_of_pos_left j hM
  have h3 : M * (j + 1) = M * j + M := by ring
  omega

/-- **Needs `1 ≤ M`**: at `M = 0, j = 1` the statement reads `2 ≤ 1`, which is false.
That is exactly the counterexample `omega` was reporting. -/
lemma fact_add_le (M j : ℕ) (hM : 1 ≤ M) :
    Nat.factorial M + j ≤ Nat.factorial (M + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep : Nat.factorial (M + j) + 1 ≤ Nat.factorial (M + j + 1) := by
        rw [Nat.factorial_succ]
        have hpos : 1 ≤ Nat.factorial (M + j) := Nat.factorial_pos _
        have h2 : 2 * Nat.factorial (M + j) ≤ (M + j + 1) * Nat.factorial (M + j) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have he : M + (j + 1) = M + j + 1 := by omega
      rw [he]
      omega

/-! ## The series -/

noncomputable def cc (n : ℕ) : ℤ := ⌈3 * Real.pi * ((n : ℝ) + 1)⌉

noncomputable def T (n : ℕ) : ℝ := (cc n : ℝ) / ((5 : ℝ) ^ Nat.factorial (n + 1) - 1)

lemma denom_pos (n : ℕ) : (0 : ℝ) < (5 : ℝ) ^ Nat.factorial (n + 1) - 1 := by
  have := five_le_pow (one_le_fact (n + 1)); linarith

lemma cc_pos (n : ℕ) : 0 < cc n := by
  have hpi := Real.pi_pos
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact Int.ceil_pos.2 (by nlinarith)

lemma cc_le (n : ℕ) : (cc n : ℝ) ≤ 13 * ((n : ℝ) + 1) := by
  have h1 : (cc n : ℝ) < 3 * Real.pi * ((n : ℝ) + 1) + 1 := Int.ceil_lt_add_one _
  have h2 : Real.pi < 4 := Real.pi_lt_four
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 4 - Real.pi)
    (by linarith : (0:ℝ) ≤ (n:ℝ) + 1)]

lemma T_pos (n : ℕ) : 0 < T n :=
  div_pos (by exact_mod_cast cc_pos n) (denom_pos n)

lemma T_le (n : ℕ) : T n ≤ 17 * ((n : ℝ) + 1) / (5 : ℝ) ^ Nat.factorial (n + 1) := by
  have hp : (0 : ℝ) < (5 : ℝ) ^ Nat.factorial (n + 1) := by positivity
  have h5 : (5 : ℝ) ≤ (5 : ℝ) ^ Nat.factorial (n + 1) := five_le_pow (one_le_fact (n + 1))
  have hd : (0 : ℝ) < (5 : ℝ) ^ Nat.factorial (n + 1) - 1 := denom_pos n
  have hc : (cc n : ℝ) ≤ 13 * ((n : ℝ) + 1) := cc_le n
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  refine div_le_div_cross hp hd ?_
  nlinarith [mul_le_mul_of_nonneg_right hc hp.le,
    mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ) + 1)
      (by linarith : (0:ℝ) ≤ (5:ℝ) ^ Nat.factorial (n + 1) - 5)]

/-! ## Tail estimate -/

lemma tail_term_bound (N j : ℕ) :
    T (j + N) ≤ 17 * ((N : ℝ) + 1) / (5 : ℝ) ^ Nat.factorial (N + 1) * (2 / 5 : ℝ) ^ j := by
  have hnumN : j + N + 1 ≤ (N + 1) * 2 ^ j := by
    have h := add_le_mul_two_pow (N + 1) j (by omega)
    omega
  have hnum : (((j + N : ℕ) : ℝ)) + 1 ≤ ((N : ℝ) + 1) * 2 ^ j := by
    have : ((j + N + 1 : ℕ) : ℝ) ≤ (((N + 1) * 2 ^ j : ℕ) : ℝ) := by exact_mod_cast hnumN
    push_cast at this ⊢
    linarith
  have hexp : Nat.factorial (N + 1) + j ≤ Nat.factorial (j + N + 1) := by
    have h := fact_add_le (N + 1) j (by omega)
    have he : N + 1 + j = j + N + 1 := by omega
    rwa [he] at h
  have hpow : (5 : ℝ) ^ (Nat.factorial (N + 1) + j) ≤ (5 : ℝ) ^ Nat.factorial (j + N + 1) :=
    pow_le_pow_right₀ (by norm_num) hexp
  have hstep : 17 * (((j + N : ℕ) : ℝ) + 1) / (5 : ℝ) ^ Nat.factorial (j + N + 1)
      ≤ 17 * (((N : ℝ) + 1) * 2 ^ j) / (5 : ℝ) ^ (Nat.factorial (N + 1) + j) := by
    refine div_le_div_cross (by positivity) (by positivity) ?_
    have hmul : (((j + N : ℕ) : ℝ) + 1) * (5 : ℝ) ^ (Nat.factorial (N + 1) + j)
        ≤ ((N : ℝ) + 1) * 2 ^ j * (5 : ℝ) ^ Nat.factorial (j + N + 1) :=
      mul_le_mul hnum hpow (by positivity) (by positivity)
    nlinarith [hmul]
  have heq : 17 * (((N : ℝ) + 1) * 2 ^ j) / (5 : ℝ) ^ (Nat.factorial (N + 1) + j)
      = 17 * ((N : ℝ) + 1) / (5 : ℝ) ^ Nat.factorial (N + 1) * (2 / 5 : ℝ) ^ j := by
    rw [pow_add, div_pow]
    ring
  exact (T_le (j + N)).trans (hstep.trans (le_of_eq heq))

lemma T_summable : Summable T := by
  have hgeo : Summable (fun j : ℕ => (2 / 5 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hmaj : Summable (fun j : ℕ =>
      17 * (((0 : ℕ) : ℝ) + 1) / (5 : ℝ) ^ Nat.factorial (0 + 1) * (2 / 5 : ℝ) ^ j) :=
    hgeo.mul_left _
  refine Summable.of_nonneg_of_le (fun j => (T_pos j).le) (fun j => ?_) hmaj
  simpa using tail_term_bound 0 j

lemma tail_bound (N : ℕ) :
    ∑' j : ℕ, T (j + N) ≤ 29 * ((N : ℝ) + 1) / (5 : ℝ) ^ Nat.factorial (N + 1) := by
  have hs : Summable (fun j : ℕ => T (j + N)) := (summable_nat_add_iff N).2 T_summable
  have hgeo : Summable (fun j : ℕ => (2 / 5 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hmaj := hgeo.mul_left (17 * ((N : ℝ) + 1) / (5 : ℝ) ^ Nat.factorial (N + 1))
  have h1 := Summable.tsum_le_tsum (fun j => tail_term_bound N j) hs hmaj
  have h2 : ∑' j : ℕ, 17 * ((N : ℝ) + 1) / (5 : ℝ) ^ Nat.factorial (N + 1) * (2 / 5 : ℝ) ^ j
      = 17 * ((N : ℝ) + 1) / (5 : ℝ) ^ Nat.factorial (N + 1) * (5 / 3) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [h2] at h1
  refine h1.trans ?_
  have hX : (0 : ℝ) < (5 : ℝ) ^ Nat.factorial (N + 1) := by positivity
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hrw : 17 * ((N : ℝ) + 1) / (5 : ℝ) ^ Nat.factorial (N + 1) * (5 / 3)
      = 17 * ((N : ℝ) + 1) * (5 / 3) / (5 : ℝ) ^ Nat.factorial (N + 1) := by ring
  rw [hrw]
  refine div_le_div_cross hX hX ?_
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (N : ℝ) + 1) hX.le]

/-! ## Common denominator -/

lemma pow_sub_one_dvd {a b : ℕ} (h : a ∣ b) : (5 : ℤ) ^ a - 1 ∣ (5 : ℤ) ^ b - 1 := by
  obtain ⟨k, rfl⟩ := h
  have h1 : ((5 : ℤ) ^ a - 1) ∣ ((5 : ℤ) ^ a) ^ k - 1 ^ k := sub_dvd_pow_sub_pow _ _ _
  simpa [← pow_mul] using h1

lemma partial_sum_eq (N : ℕ) :
    ∃ P : ℤ, ∑ n ∈ range N, T n = (P : ℝ) / ((5 : ℝ) ^ Nat.factorial N - 1) := by
  classical
  have h5N : (5 : ℝ) ≤ (5 : ℝ) ^ Nat.factorial N := five_le_pow (one_le_fact N)
  have hNR : ((5 : ℝ) ^ Nat.factorial N - 1) ≠ 0 := by intro h; linarith
  refine ⟨∑ n ∈ range N, cc n *
    (((5 : ℤ) ^ Nat.factorial N - 1) / ((5 : ℤ) ^ Nat.factorial (n + 1) - 1)), ?_⟩
  rw [Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hlt : n < N := Finset.mem_range.mp hn
  have hdvd : ((5 : ℤ) ^ Nat.factorial (n + 1) - 1) ∣ ((5 : ℤ) ^ Nat.factorial N - 1) :=
    pow_sub_one_dvd (Nat.factorial_dvd_factorial hlt)
  obtain ⟨e, he⟩ := hdvd
  have h5Z : (5 : ℤ) ≤ (5 : ℤ) ^ Nat.factorial (n + 1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 5) (one_le_fact (n + 1))
    simpa using h
  have hd0 : ((5 : ℤ) ^ Nat.factorial (n + 1) - 1) ≠ 0 := by
    have : (0 : ℤ) < (5 : ℤ) ^ Nat.factorial (n + 1) - 1 := by linarith
    exact this.ne'
  have hquot : ((5 : ℤ) ^ Nat.factorial N - 1) / ((5 : ℤ) ^ Nat.factorial (n + 1) - 1) = e := by
    rw [he, Int.mul_ediv_cancel_left _ hd0]
  rw [hquot]
  have heR : ((5 : ℝ) ^ Nat.factorial N - 1)
      = ((5 : ℝ) ^ Nat.factorial (n + 1) - 1) * (e : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) he
  have he0 : (e : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at heR; exact hNR heR
  have hdR : ((5 : ℝ) ^ Nat.factorial (n + 1) - 1) ≠ 0 := ne_of_gt (denom_pos n)
  rw [T, heR, Int.cast_mul, div_eq_div_iff hdR (mul_ne_zero hdR he0)]
  ring

/-! ## The arithmetic inequality -/

lemma key_ineq (N : ℕ) (hN : 4 ≤ N) : 29 * (N + 1) < 5 ^ (5 * Nat.factorial N) := by
  have h1 : N + 1 ≤ 2 ^ N := succ_le_two_pow N
  have h2 : (2 : ℕ) ^ N ≤ 5 ^ N := Nat.pow_le_pow_left (by norm_num) N
  have h4 : 29 * (N + 1) ≤ 29 * 5 ^ N := Nat.mul_le_mul le_rfl (h1.trans h2)
  have h5 : (125 : ℕ) * 5 ^ N = 5 ^ (N + 3) := by ring
  have h7 : N ≤ Nat.factorial N := Nat.self_le_factorial N
  have h6 : N + 3 < 5 * Nat.factorial N := by omega
  calc 29 * (N + 1) ≤ 5 ^ (N + 3) := by omega
    _ < 5 ^ (5 * Nat.factorial N) := Nat.pow_lt_pow_right (by norm_num) h6

/-! ## Liouville -/

theorem liouville_T : Liouville (∑' n : ℕ, T n) := by
  intro k
  set x : ℝ := ∑' n : ℕ, T n with hxdef
  obtain ⟨N, hN⟩ : ∃ N, N = k + 4 := ⟨k + 4, rfl⟩
  obtain ⟨P, hP⟩ := partial_sum_eq N
  have hfN : (5 : ℝ) ≤ (5 : ℝ) ^ Nat.factorial N := five_le_pow (one_le_fact N)
  have h5Z : (5 : ℤ) ≤ (5 : ℤ) ^ Nat.factorial N := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 5) (one_le_fact N)
    simpa using h
  have hQZ : (1 : ℤ) < (5 : ℤ) ^ Nat.factorial N - 1 := by linarith
  have hQR : (((5 : ℤ) ^ Nat.factorial N - 1 : ℤ) : ℝ) = (5 : ℝ) ^ Nat.factorial N - 1 := by
    push_cast; ring
  have hsplit : (∑ n ∈ range N, T n) + (∑' j : ℕ, T (j + N)) = x :=
    T_summable.sum_add_tsum_nat_add N
  have hs : Summable (fun j : ℕ => T (j + N)) := (summable_nat_add_iff N).2 T_summable
  have hspos : 0 < ∑' j : ℕ, T (j + N) := by
    have hle : T (0 + N) ≤ ∑' j : ℕ, T (j + N) :=
      hs.le_tsum 0 (fun j _ => (T_pos _).le)
    exact lt_of_lt_of_le (T_pos (0 + N)) hle
  have hdiff : x - (P : ℝ) / ((5 : ℝ) ^ Nat.factorial N - 1) = ∑' j : ℕ, T (j + N) := by
    rw [← hsplit, ← hP]; ring
  refine ⟨P, (5 : ℤ) ^ Nat.factorial N - 1, hQZ, ?_, ?_⟩
  · rw [hQR]
    intro hcon
    rw [hcon, sub_self] at hdiff
    linarith
  · rw [hQR, hdiff, abs_of_pos hspos]
    have hfe : Nat.factorial (N + 1) = k * Nat.factorial N + 5 * Nat.factorial N := by
      rw [Nat.factorial_succ, hN]; ring
    have hA : (0 : ℝ) < (5 : ℝ) ^ (k * Nat.factorial N) := by positivity
    have hQk : (0 : ℝ) < ((5 : ℝ) ^ Nat.factorial N - 1) ^ k := pow_pos (by linarith) k
    have hQpow : ((5 : ℝ) ^ Nat.factorial N - 1) ^ k ≤ (5 : ℝ) ^ (k * Nat.factorial N) := by
      rw [mul_comm, pow_mul]
      exact pow_le_pow_aux (by linarith) (by linarith) k
    have hkey : (29 : ℝ) * ((N : ℝ) + 1) < (5 : ℝ) ^ (5 * Nat.factorial N) := by
      exact_mod_cast key_ineq N (by omega)
    have step1 : ∑' j : ℕ, T (j + N)
        ≤ 29 * ((N : ℝ) + 1) /
            ((5 : ℝ) ^ (k * Nat.factorial N) * (5 : ℝ) ^ (5 * Nat.factorial N)) := by
      rw [← pow_add, ← hfe]; exact tail_bound N
    have step2 : 29 * ((N : ℝ) + 1) /
        ((5 : ℝ) ^ (k * Nat.factorial N) * (5 : ℝ) ^ (5 * Nat.factorial N))
        < 1 / (5 : ℝ) ^ (k * Nat.factorial N) := by
      refine div_lt_div_cross hA (by positivity) ?_
      nlinarith [mul_lt_mul_of_pos_right hkey hA]
    have step3 : 1 / (5 : ℝ) ^ (k * Nat.factorial N)
        ≤ 1 / ((5 : ℝ) ^ Nat.factorial N - 1) ^ k := by
      refine div_le_div_cross hQk hA ?_
      nlinarith [hQpow]
    linarith

/-! ## Reindexing -/

def eNatPNat : ℕ ≃ ℕ+ where
  toFun n := ⟨n + 1, Nat.succ_pos n⟩
  invFun p := (p : ℕ) - 1
  left_inv n := by simp
  right_inv p := by
    apply PNat.coe_injective
    have hp : 1 ≤ (p : ℕ) := p.property
    show (p : ℕ) - 1 + 1 = (p : ℕ)
    omega

end CeilPiLiouville

theorem transcendental_sum_ceil_pi :
    Transcendental ℚ (∑' (n : ℕ+), (⌈3 * Real.pi * (n : ℝ)⌉ : ℝ) / ((5 : ℝ) ^ (n : ℕ).factorial - 1)) := by
  have hterm : ∀ n : ℕ,
      (⌈3 * Real.pi * ((CeilPiLiouville.eNatPNat n : ℕ+) : ℝ)⌉ : ℝ) /
        ((5 : ℝ) ^ ((CeilPiLiouville.eNatPNat n : ℕ+) : ℕ).factorial - 1)
        = CeilPiLiouville.T n := by
    intro n
    have h1 : ((CeilPiLiouville.eNatPNat n : ℕ+) : ℕ) = n + 1 := rfl
    have h2 : ((CeilPiLiouville.eNatPNat n : ℕ+) : ℝ) = (n : ℝ) + 1 := by
      have := congrArg (fun m : ℕ => (m : ℝ)) h1
      push_cast at this ⊢
      exact this
    rw [h2, h1, CeilPiLiouville.T, CeilPiLiouville.cc]
  have hre : (∑' (n : ℕ+), (⌈3 * Real.pi * (n : ℝ)⌉ : ℝ) / ((5 : ℝ) ^ (n : ℕ).factorial - 1))
      = ∑' n : ℕ, CeilPiLiouville.T n := by
    rw [← Equiv.tsum_eq CeilPiLiouville.eNatPNat
      (fun p : ℕ+ => (⌈3 * Real.pi * (p : ℝ)⌉ : ℝ) / ((5 : ℝ) ^ (p : ℕ).factorial - 1))]
    exact tsum_congr hterm
  rw [hre]
  intro halg
  exact CeilPiLiouville.liouville_T.transcendental
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr halg)
```
