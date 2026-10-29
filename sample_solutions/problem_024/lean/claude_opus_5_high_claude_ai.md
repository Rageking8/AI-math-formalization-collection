# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `31 July 2026`\
Line count: `265`\
Turn count: `2`

## Solution

```lean4
import Mathlib

private lemma sum_digits_le : ∀ (k m : ℕ), m < 10 ^ k → (Nat.digits 10 m).sum ≤ 9 * k := by
  intro k
  induction k with
  | zero =>
      intro m hm
      have hm0 : m = 0 := by simpa using hm
      subst hm0
      simp
  | succ k ih =>
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp
      · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hpos, List.sum_cons]
        have h1 : (10:ℕ) ^ (k + 1) = 10 ^ k * 10 := by ring
        have hlt : m / 10 < 10 ^ k := by omega
        have h2 := ih (m / 10) hlt
        omega

private lemma digits_sum_special (m : ℕ) :
    (Nat.digits 10 (100 * m + 11)).sum = 2 + (Nat.digits 10 m).sum := by
  have e1 : (100 * m + 11) % 10 = 1 := by omega
  have e2 : (100 * m + 11) / 10 = 10 * m + 1 := by omega
  have e3 : (10 * m + 1) % 10 = 1 := by omega
  have e4 : (10 * m + 1) / 10 = m := by omega
  rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) (by omega : 0 < 100 * m + 11), e1, e2,
      Nat.digits_def' (by norm_num : (1:ℕ) < 10) (by omega : 0 < 10 * m + 1), e3, e4,
      List.sum_cons, List.sum_cons]
  omega

/-- Helper replacing `sum_le_tsum` (removed/renamed in current Mathlib). -/
private lemma finset_sum_le_tsum {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (hs : Summable g)
    (s : Finset ℕ) : ∑ i ∈ s, g i ≤ ∑' i, g i := by
  obtain ⟨N, hN⟩ : ∃ N, s ⊆ Finset.range N := by
    first
    | exact s.exists_nat_subset_range
    | exact ⟨s.sup id + 1, fun x hx =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hx))⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hN (fun i _ _ => hg i)) ?_
  have hmono : Monotone (fun n => ∑ j ∈ Finset.range n, g j) :=
    monotone_nat_of_le_succ (fun n => by rw [Finset.sum_range_succ]; linarith [hg n])
  exact hmono.ge_of_tendsto hs.hasSum.tendsto_sum_nat N

private noncomputable def f (n : ℕ) : ℝ :=
  if n ≥ 3 ∧ (Nat.digits 10 n).sum ≥ 2 then
    1 / ((n : ℝ) * ((Nat.digits 10 n).sum : ℝ) * Real.log ((Nat.digits 10 n).sum : ℝ))
  else
    0

private lemma f_nonneg (n : ℕ) : 0 ≤ f n := by
  unfold f
  by_cases h : n ≥ 3 ∧ (Nat.digits 10 n).sum ≥ 2
  · rw [if_pos h]
    have h2 : (2:ℝ) ≤ ((Nat.digits 10 n).sum : ℝ) := by exact_mod_cast h.2
    have hlog : 0 ≤ Real.log ((Nat.digits 10 n).sum : ℝ) := Real.log_nonneg (by linarith)
    exact div_nonneg zero_le_one
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _)) hlog)
  · simp [h]

private lemma term_bound (j m : ℕ) (hm : m < 10 ^ (j + 1)) :
    1 / ((10:ℝ) ^ (j + 3) * (9 * ((j:ℝ) + 3)) * Real.log (9 * ((j:ℝ) + 3)))
      ≤ f (100 * m + 11) := by
  have hS2 : (Nat.digits 10 (100 * m + 11)).sum ≥ 2 := by
    rw [digits_sum_special]; omega
  have hn3 : 100 * m + 11 ≥ 3 := by omega
  have hnlt : 100 * m + 11 < 10 ^ (j + 3) := by
    have h3 : (10:ℕ) ^ (j + 3) = 100 * 10 ^ (j + 1) := by ring
    omega
  have hSle : (Nat.digits 10 (100 * m + 11)).sum ≤ 9 * (j + 3) :=
    sum_digits_le (j + 3) _ hnlt
  have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  have hcast2 : (2:ℝ) ≤ (((Nat.digits 10 (100 * m + 11)).sum : ℝ)) := by exact_mod_cast hS2
  have hcastle : (((Nat.digits 10 (100 * m + 11)).sum : ℝ)) ≤ 9 * ((j:ℝ) + 3) := by
    calc (((Nat.digits 10 (100 * m + 11)).sum : ℝ))
        ≤ ((9 * (j + 3) : ℕ) : ℝ) := by exact_mod_cast hSle
      _ = 9 * ((j:ℝ) + 3) := by push_cast; ring
  have hcastn : ((100 * m + 11 : ℕ) : ℝ) ≤ (10:ℝ) ^ (j + 3) := by
    calc ((100 * m + 11 : ℕ) : ℝ)
        ≤ ((10 ^ (j + 3) : ℕ) : ℝ) := by exact_mod_cast hnlt.le
      _ = (10:ℝ) ^ (j + 3) := by push_cast; ring
  have hnpos : (0:ℝ) < ((100 * m + 11 : ℕ) : ℝ) := by push_cast; positivity
  have hlogpos : 0 < Real.log (((Nat.digits 10 (100 * m + 11)).sum : ℝ)) :=
    Real.log_pos (by linarith)
  have hlogle : Real.log (((Nat.digits 10 (100 * m + 11)).sum : ℝ))
      ≤ Real.log (9 * ((j:ℝ) + 3)) := by
    first
    | exact Real.log_le_log (by linarith) hcastle
    | exact Real.log_le_log_of_le hcastle
    | (gcongr <;> linarith)
  unfold f
  rw [if_pos (show 100 * m + 11 ≥ 3 ∧ (Nat.digits 10 (100 * m + 11)).sum ≥ 2 from ⟨hn3, hS2⟩)]
  apply one_div_le_one_div_of_le
  · exact mul_pos (mul_pos hnpos (by linarith)) hlogpos
  · exact mul_le_mul (mul_le_mul hcastn hcastle (by linarith) (by positivity)) hlogle
      hlogpos.le (by positivity)

private noncomputable def v (j : ℕ) : ℝ :=
  1 / (1000 * ((j:ℝ) + 3) * Real.log (9 * ((j:ℝ) + 3)))

private lemma v_log_pos (j : ℕ) : 0 < Real.log (9 * ((j:ℝ) + 3)) := by
  have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  exact Real.log_pos (by linarith)

private lemma v_nonneg (j : ℕ) : 0 ≤ v j := by
  have h := v_log_pos j
  have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  unfold v
  exact div_nonneg zero_le_one (mul_nonneg (by linarith) h.le)

private lemma block_bound (j : ℕ) :
    v j ≤ ∑ m ∈ Finset.Ico (10 ^ j) (10 ^ (j + 1)), f (100 * m + 11) := by
  have hle : ∀ m ∈ Finset.Ico (10 ^ j) (10 ^ (j + 1)),
      1 / ((10:ℝ) ^ (j + 3) * (9 * ((j:ℝ) + 3)) * Real.log (9 * ((j:ℝ) + 3)))
        ≤ f (100 * m + 11) := fun m hm => term_bound j m (Finset.mem_Ico.mp hm).2
  have hsum := Finset.card_nsmul_le_sum (Finset.Ico (10 ^ j) (10 ^ (j + 1)))
      (fun m => f (100 * m + 11)) _ hle
  have hcard : (Finset.Ico (10 ^ j) (10 ^ (j + 1))).card = 9 * 10 ^ j := by
    rw [Nat.card_Ico]
    have h1 : (10:ℕ) ^ (j + 1) = 10 * 10 ^ j := by ring
    omega
  rw [hcard, nsmul_eq_mul] at hsum
  refine le_trans (le_of_eq ?_) hsum
  have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  have hL : 0 < Real.log (9 * ((j:ℝ) + 3)) := v_log_pos j
  have hLne : Real.log (9 * ((j:ℝ) + 3)) ≠ 0 := ne_of_gt hL
  have hjne : ((j:ℝ) + 3) ≠ 0 := by linarith
  have h10jne : (10:ℝ) ^ j ≠ 0 := by positivity
  have h10 : (10:ℝ) ^ (j + 3) = 10 ^ j * 1000 := by ring
  unfold v
  rw [h10]
  push_cast
  field_simp
  try ring

private lemma partial_sum_v (J : ℕ) :
    ∑ j ∈ Finset.range J, v j ≤ ∑ m ∈ Finset.Ico 1 (10 ^ J), f (100 * m + 11) := by
  induction J with
  | zero => simp
  | succ J ih =>
      have h1 : (1:ℕ) ≤ 10 ^ J := Nat.one_le_pow _ _ (by norm_num)
      have h2 : (10:ℕ) ^ J ≤ 10 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Finset.sum_range_succ, ← Finset.sum_Ico_consecutive (fun m => f (100 * m + 11)) h1 h2]
      exact add_le_add ih (block_bound J)

private noncomputable def w (i : ℕ) : ℝ := 1 / (8000 * ((i:ℝ) + 7))

private lemma v_lower (i j : ℕ) (hj : j < 2 ^ (i + 1)) :
    1 / (1000 * (2:ℝ) ^ (i + 3) * ((i:ℝ) + 7)) ≤ v j := by
  have hjnat : j + 3 ≤ 2 ^ (i + 3) := by
    have e1 : (2:ℕ) ^ (i + 3) = 8 * 2 ^ i := by ring
    have e2 : (2:ℕ) ^ (i + 1) = 2 * 2 ^ i := by ring
    have e3 : 1 ≤ (2:ℕ) ^ i := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hjR : ((j:ℝ) + 3) ≤ (2:ℝ) ^ (i + 3) := by
    have h : ((j + 3 : ℕ) : ℝ) ≤ ((2 ^ (i + 3) : ℕ) : ℝ) := by exact_mod_cast hjnat
    push_cast at h
    linarith
  have hjR0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  have hiR0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hstep : Real.log (9 * ((j:ℝ) + 3)) ≤ (i:ℝ) + 7 := by
    have hpow : (0:ℝ) ≤ (2:ℝ) ^ (i + 3) := by positivity
    have h1 : 9 * ((j:ℝ) + 3) ≤ (2:ℝ) ^ (i + 7) := by
      have e : (2:ℝ) ^ (i + 7) = 2 ^ (i + 3) * 16 := by ring
      rw [e]; linarith
    have h3 : Real.log (9 * ((j:ℝ) + 3)) ≤ Real.log ((2:ℝ) ^ (i + 7)) := by
      first
      | exact Real.log_le_log (by linarith) h1
      | exact Real.log_le_log_of_le h1
      | (gcongr <;> linarith)
    have h4 : Real.log ((2:ℝ) ^ (i + 7)) = ((i:ℝ) + 7) * Real.log 2 := by
      rw [Real.log_pow]; push_cast; ring
    rw [h4] at h3
    linarith [mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ) ≤ (i:ℝ) + 7 by linarith)]
  have hL : 0 < Real.log (9 * ((j:ℝ) + 3)) := v_log_pos j
  have hden : 1000 * ((j:ℝ) + 3) * Real.log (9 * ((j:ℝ) + 3))
      ≤ 1000 * (2:ℝ) ^ (i + 3) * ((i:ℝ) + 7) := by
    apply mul_le_mul _ hstep hL.le (by positivity)
    linarith
  have hpos : 0 < 1000 * ((j:ℝ) + 3) * Real.log (9 * ((j:ℝ) + 3)) :=
    mul_pos (by linarith) hL
  unfold v
  exact one_div_le_one_div_of_le hpos hden

private lemma v_block (i : ℕ) : w i ≤ ∑ j ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)), v j := by
  have hle : ∀ j ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)),
      1 / (1000 * (2:ℝ) ^ (i + 3) * ((i:ℝ) + 7)) ≤ v j :=
    fun j hj => v_lower i j (Finset.mem_Ico.mp hj).2
  have hsum := Finset.card_nsmul_le_sum (Finset.Ico (2 ^ i) (2 ^ (i + 1))) v _ hle
  have hcard : (Finset.Ico (2 ^ i) (2 ^ (i + 1))).card = 2 ^ i := by
    rw [Nat.card_Ico]
    have h1 : (2:ℕ) ^ (i + 1) = 2 * 2 ^ i := by ring
    omega
  rw [hcard, nsmul_eq_mul] at hsum
  refine le_trans (le_of_eq ?_) hsum
  have hiR : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
  have hine : ((i:ℝ) + 7) ≠ 0 := by linarith
  have h2ne : (2:ℝ) ^ i ≠ 0 := by positivity
  have h2 : (2:ℝ) ^ (i + 3) = 2 ^ i * 8 := by ring
  unfold w
  rw [h2]
  push_cast
  field_simp
  try ring

private lemma partial_sum_w (I : ℕ) :
    ∑ i ∈ Finset.range I, w i ≤ ∑ j ∈ Finset.Ico 1 (2 ^ I), v j := by
  induction I with
  | zero => simp
  | succ I ih =>
      have h1 : (1:ℕ) ≤ 2 ^ I := Nat.one_le_pow _ _ (by norm_num)
      have h2 : (2:ℕ) ^ I ≤ 2 ^ (I + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Finset.sum_range_succ, ← Finset.sum_Ico_consecutive v h1 h2]
      exact add_le_add ih (v_block I)

private lemma f_not_summable : ¬ Summable f := by
  intro hf
  have hinj : Function.Injective (fun m : ℕ => 100 * m + 11) := by
    intro a b hab
    have h : 100 * a + 11 = 100 * b + 11 := hab
    omega
  have hcomp : Summable (fun m : ℕ => f (100 * m + 11)) := by
    first
    | exact hf.comp_injective hinj
    | simpa [Function.comp] using hf.comp_injective hinj
  have hTv : ∀ J : ℕ, ∑ j ∈ Finset.range J, v j ≤ ∑' m : ℕ, f (100 * m + 11) := fun J =>
    le_trans (partial_sum_v J) (finset_sum_le_tsum (fun n => f_nonneg (100 * n + 11)) hcomp _)
  have hvsum : Summable v := summable_of_sum_range_le v_nonneg hTv
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    have hi : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    unfold w
    positivity
  have hTw : ∀ I : ℕ, ∑ i ∈ Finset.range I, w i ≤ ∑' j : ℕ, v j := fun I =>
    le_trans (partial_sum_w I) (finset_sum_le_tsum v_nonneg hvsum _)
  have hwsum : Summable w := summable_of_sum_range_le hw0 hTw
  have h2 : Summable (fun i : ℕ => 1 / (((i + 7 : ℕ)) : ℝ)) := by
    have hm := hwsum.mul_left 8000
    apply hm.congr
    intro i
    have hi : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    have hne : ((i:ℝ) + 7) ≠ 0 := by linarith
    unfold w
    push_cast
    field_simp
  have h3 : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 7).mp h2
  have hns : ¬ Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    first
    | exact Real.not_summable_one_div_natCast
    | exact Real.not_summable_one_div_nat_cast
    | simpa [one_div] using Real.not_summable_natCast_inv
    | simpa [one_div] using Real.not_summable_nat_cast_inv
  exact hns h3

theorem digit_sum_series_diverges :
    ¬ Summable (fun n : ℕ =>
      if n ≥ 3 ∧ (Nat.digits 10 n).sum ≥ 2 then
      1 / ((n : ℝ) * ((Nat.digits 10 n).sum : ℝ) * Real.log ((Nat.digits 10 n).sum : ℝ))
      else 0) := by
  intro h
  exact f_not_summable h
```
