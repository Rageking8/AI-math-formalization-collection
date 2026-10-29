# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `24 August 2026`\
Line count: `341`\
Turn count: `4`

## Note

The conversation contained 1 "Continue" message not included in the turn count.

## Solution

```lean4
import Mathlib

def sumValidIntegers (l s : ℕ) : ℕ :=
  ∑ n ∈ (Finset.Ico 1 (10 ^ l)).filter (fun n => (Nat.digits 10 n).sum ≤ s), n

namespace TLB

def A (l s : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (10 ^ l), if (Nat.digits 10 n).sum ≤ s then n else 0

def Bn (l s : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (10 ^ l), if (Nat.digits 10 n).sum ≤ s then 1 else 0

/-! ### Splitting a range sum into blocks of ten -/

lemma sum_range_add' (f : ℕ → ℕ) (m n : ℕ) :
    ∑ i ∈ Finset.range (m + n), f i
      = (∑ i ∈ Finset.range m, f i) + ∑ i ∈ Finset.range n, f (m + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    show ∑ i ∈ Finset.range (m + n + 1), f i = _
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun i => f (m + i)) n]
    ring

lemma split10 (f : ℕ → ℕ) (m : ℕ) :
    ∑ n ∈ Finset.range (10 * m), f n
      = ∑ q ∈ Finset.range m, ∑ r ∈ Finset.range 10, f (10 * q + r) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : 10 * (m + 1) = 10 * m + 10 := by ring
    rw [h, sum_range_add' f (10 * m) 10, ih,
      Finset.sum_range_succ (fun q => ∑ r ∈ Finset.range 10, f (10 * q + r)) m]

lemma ds_add (q r : ℕ) (hr : r < 10) :
    (Nat.digits 10 (10 * q + r)).sum = r + (Nat.digits 10 q).sum := by
  rcases Nat.eq_zero_or_pos (10 * q + r) with h | h
  · have hq : q = 0 := by omega
    have hr0 : r = 0 := by omega
    subst hq; subst hr0; simp
  · have h1 : (10 * q + r) % 10 = r := by omega
    have h2 : (10 * q + r) / 10 = q := by omega
    rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 10) h, h1, h2, List.sum_cons]

/-! ### Base cases and the digit recursions -/

lemma A_zero (s : ℕ) : A 0 s = 0 := by simp [A]

lemma Bn_zero (s : ℕ) : Bn 0 s = 1 := by
  unfold Bn
  rw [pow_zero, Finset.sum_range_one]
  simp

lemma A_succ (l s : ℕ) :
    A (l + 1) s
      = ∑ r ∈ Finset.range 10, (if r ≤ s then 10 * A l (s - r) + r * Bn l (s - r) else 0) := by
  have hp : (10 : ℕ) ^ (l + 1) = 10 * 10 ^ l := by ring
  unfold A Bn
  rw [hp, split10, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Finset.mem_range] at hr
  by_cases h : r ≤ s
  · rw [if_pos h, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [ds_add q r hr]
    by_cases h2 : (Nat.digits 10 q).sum ≤ s - r
    · rw [if_pos (show r + (Nat.digits 10 q).sum ≤ s by omega), if_pos h2, if_pos h2]; ring
    · rw [if_neg (show ¬ r + (Nat.digits 10 q).sum ≤ s by omega), if_neg h2, if_neg h2]; simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero ?_
    intro q _
    rw [ds_add q r hr]
    exact if_neg (by omega)

lemma Bn_succ (l s : ℕ) :
    Bn (l + 1) s = ∑ r ∈ Finset.range 10, (if r ≤ s then Bn l (s - r) else 0) := by
  have hp : (10 : ℕ) ^ (l + 1) = 10 * 10 ^ l := by ring
  unfold Bn
  rw [hp, split10, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Finset.mem_range] at hr
  by_cases h : r ≤ s
  · rw [if_pos h]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [ds_add q r hr]
    by_cases h2 : (Nat.digits 10 q).sum ≤ s - r
    · rw [if_pos (show r + (Nat.digits 10 q).sum ≤ s by omega), if_pos h2]
    · rw [if_neg (show ¬ r + (Nat.digits 10 q).sum ≤ s by omega), if_neg h2]
  · rw [if_neg h]
    refine Finset.sum_eq_zero ?_
    intro q _
    rw [ds_add q r hr]
    exact if_neg (by omega)

/-! ### A 14-field row carrying `A l s` and `Bn l s` for `s ≤ 6` -/

structure Row where
  a0 : ℕ
  a1 : ℕ
  a2 : ℕ
  a3 : ℕ
  a4 : ℕ
  a5 : ℕ
  a6 : ℕ
  b0 : ℕ
  b1 : ℕ
  b2 : ℕ
  b3 : ℕ
  b4 : ℕ
  b5 : ℕ
  b6 : ℕ

def step (v : Row) : Row :=
  ⟨ 10 * v.a0,
    10 * (v.a0 + v.a1) + v.b0,
    10 * (v.a0 + v.a1 + v.a2) + 2 * v.b0 + v.b1,
    10 * (v.a0 + v.a1 + v.a2 + v.a3) + 3 * v.b0 + 2 * v.b1 + v.b2,
    10 * (v.a0 + v.a1 + v.a2 + v.a3 + v.a4) + 4 * v.b0 + 3 * v.b1 + 2 * v.b2 + v.b3,
    10 * (v.a0 + v.a1 + v.a2 + v.a3 + v.a4 + v.a5)
      + 5 * v.b0 + 4 * v.b1 + 3 * v.b2 + 2 * v.b3 + v.b4,
    10 * (v.a0 + v.a1 + v.a2 + v.a3 + v.a4 + v.a5 + v.a6)
      + 6 * v.b0 + 5 * v.b1 + 4 * v.b2 + 3 * v.b3 + 2 * v.b4 + v.b5,
    v.b0,
    v.b0 + v.b1,
    v.b0 + v.b1 + v.b2,
    v.b0 + v.b1 + v.b2 + v.b3,
    v.b0 + v.b1 + v.b2 + v.b3 + v.b4,
    v.b0 + v.b1 + v.b2 + v.b3 + v.b4 + v.b5,
    v.b0 + v.b1 + v.b2 + v.b3 + v.b4 + v.b5 + v.b6 ⟩

def row (l : ℕ) : Row :=
  ⟨A l 0, A l 1, A l 2, A l 3, A l 4, A l 5, A l 6,
   Bn l 0, Bn l 1, Bn l 2, Bn l 3, Bn l 4, Bn l 5, Bn l 6⟩

lemma a0_eq (l : ℕ) : (row l).a0 = A l 0 := rfl
lemma a1_eq (l : ℕ) : (row l).a1 = A l 1 := rfl
lemma a2_eq (l : ℕ) : (row l).a2 = A l 2 := rfl
lemma a3_eq (l : ℕ) : (row l).a3 = A l 3 := rfl
lemma a4_eq (l : ℕ) : (row l).a4 = A l 4 := rfl
lemma a5_eq (l : ℕ) : (row l).a5 = A l 5 := rfl
lemma a6_eq (l : ℕ) : (row l).a6 = A l 6 := rfl

lemma rowsucc (l : ℕ) : row (l + 1) = step (row l) := by
  have e0 : A (l+1) 0 = 10 * A l 0 := by
    rw [A_succ]; norm_num [Finset.sum_range_succ]
  have e1 : A (l+1) 1 = 10 * A l 0 + 10 * A l 1 + Bn l 0 := by
    rw [A_succ]; norm_num [Finset.sum_range_succ]; try omega
  have e2 : A (l+1) 2 = 10 * A l 0 + 10 * A l 1 + 10 * A l 2 + 2 * Bn l 0 + Bn l 1 := by
    rw [A_succ]; norm_num [Finset.sum_range_succ]; try omega
  have e3 : A (l+1) 3 = 10 * A l 0 + 10 * A l 1 + 10 * A l 2 + 10 * A l 3
      + 3 * Bn l 0 + 2 * Bn l 1 + Bn l 2 := by
    rw [A_succ]; norm_num [Finset.sum_range_succ]; try omega
  have e4 : A (l+1) 4 = 10 * A l 0 + 10 * A l 1 + 10 * A l 2 + 10 * A l 3 + 10 * A l 4
      + 4 * Bn l 0 + 3 * Bn l 1 + 2 * Bn l 2 + Bn l 3 := by
    rw [A_succ]; norm_num [Finset.sum_range_succ]; try omega
  have e5 : A (l+1) 5 = 10 * A l 0 + 10 * A l 1 + 10 * A l 2 + 10 * A l 3 + 10 * A l 4
      + 10 * A l 5 + 5 * Bn l 0 + 4 * Bn l 1 + 3 * Bn l 2 + 2 * Bn l 3 + Bn l 4 := by
    rw [A_succ]; norm_num [Finset.sum_range_succ]; try omega
  have e6 : A (l+1) 6 = 10 * A l 0 + 10 * A l 1 + 10 * A l 2 + 10 * A l 3 + 10 * A l 4
      + 10 * A l 5 + 10 * A l 6
      + 6 * Bn l 0 + 5 * Bn l 1 + 4 * Bn l 2 + 3 * Bn l 3 + 2 * Bn l 4 + Bn l 5 := by
    rw [A_succ]; norm_num [Finset.sum_range_succ]; try omega
  have f0 : Bn (l+1) 0 = Bn l 0 := by
    rw [Bn_succ]; norm_num [Finset.sum_range_succ]
  have f1 : Bn (l+1) 1 = Bn l 0 + Bn l 1 := by
    rw [Bn_succ]; norm_num [Finset.sum_range_succ]; try omega
  have f2 : Bn (l+1) 2 = Bn l 0 + Bn l 1 + Bn l 2 := by
    rw [Bn_succ]; norm_num [Finset.sum_range_succ]; try omega
  have f3 : Bn (l+1) 3 = Bn l 0 + Bn l 1 + Bn l 2 + Bn l 3 := by
    rw [Bn_succ]; norm_num [Finset.sum_range_succ]; try omega
  have f4 : Bn (l+1) 4 = Bn l 0 + Bn l 1 + Bn l 2 + Bn l 3 + Bn l 4 := by
    rw [Bn_succ]; norm_num [Finset.sum_range_succ]; try omega
  have f5 : Bn (l+1) 5 = Bn l 0 + Bn l 1 + Bn l 2 + Bn l 3 + Bn l 4 + Bn l 5 := by
    rw [Bn_succ]; norm_num [Finset.sum_range_succ]; try omega
  have f6 : Bn (l+1) 6 = Bn l 0 + Bn l 1 + Bn l 2 + Bn l 3 + Bn l 4 + Bn l 5 + Bn l 6 := by
    rw [Bn_succ]; norm_num [Finset.sum_range_succ]; try omega
  simp only [row, step, Row.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ### The rows, as explicit numerals -/

lemma row0 : row 0 = ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1⟩ := by
  simp [row, A_zero, Bn_zero]

lemma row1 : row 1 = ⟨0, 1, 3, 6, 10, 15, 21, 1, 2, 3, 4, 5, 6, 7⟩ := by
  have h : row 1 = step (row 0) := rowsucc 0
  rw [h, row0]; norm_num [step]

lemma row2 : row 2 = ⟨0, 11, 44, 110, 220, 385, 616, 1, 3, 6, 10, 15, 21, 28⟩ := by
  have h : row 2 = step (row 1) := rowsucc 1
  rw [h, row1]; norm_num [step]

lemma row3 : row 3 = ⟨0, 111, 555, 1665, 3885, 7770, 13986, 1, 4, 10, 20, 35, 56, 84⟩ := by
  have h : row 3 = step (row 2) := rowsucc 2
  rw [h, row2]; norm_num [step]

lemma row4 : row 4 = ⟨0, 1111, 6666, 23331, 62216, 139986, 279972,
    1, 5, 15, 35, 70, 126, 210⟩ := by
  have h : row 4 = step (row 3) := rowsucc 3
  rw [h, row3]; norm_num [step]

lemma row5 : row 5 = ⟨0, 11111, 77777, 311108, 933324, 2333310, 5133282,
    1, 6, 21, 56, 126, 252, 462⟩ := by
  have h : row 5 = step (row 4) := rowsucc 4
  rw [h, row4]; norm_num [step]

lemma row6 : row 6 = ⟨0, 111111, 888888, 3999996, 13333320, 36666630, 87999912,
    1, 7, 28, 84, 210, 462, 924⟩ := by
  have h : row 6 = step (row 5) := rowsucc 5
  rw [h, row5]; norm_num [step]

lemma row7 : row 7 = ⟨0, 1111111, 9999999, 49999995, 183333315, 549999945, 1429999857,
    1, 8, 36, 120, 330, 792, 1716⟩ := by
  have h : row 7 = step (row 6) := rowsucc 6
  rw [h, row6]; norm_num [step]

lemma row8 : row 8 = ⟨0, 11111111, 111111110, 611111105, 2444444420, 7944444365, 22244444222,
    1, 9, 45, 165, 495, 1287, 3003⟩ := by
  have h : row 8 = step (row 7) := rowsucc 7
  rw [h, row7]; norm_num [step]

lemma row9 : row 9 = ⟨0, 111111111, 1222222221, 7333333326, 31777777746, 111222222111,
    333666666333, 1, 10, 55, 220, 715, 2002, 5005⟩ := by
  have h : row 9 = step (row 8) := rowsucc 8
  rw [h, row8]; norm_num [step]

lemma row10 : row 10 = ⟨0, 1111111111, 13333333332, 86666666658, 404444444404,
    1516666666515, 4853333332848, 1, 11, 66, 286, 1001, 3003, 8008⟩ := by
  have h : row 10 = step (row 9) := rowsucc 9
  rw [h, row9]; norm_num [step]

lemma row11 : row 11 = ⟨0, 11111111111, 144444444443, 1011111111101, 5055555555505,
    20222222222020, 68755555554868, 1, 12, 78, 364, 1365, 4368, 12376⟩ := by
  have h : row 11 = step (row 10) := rowsucc 10
  rw [h, row10]; norm_num [step]

lemma row12 : row 12 = ⟨0, 111111111111, 1555555555554, 11666666666655, 62222222222160,
    264444444444180, 951999999999048, 1, 13, 91, 455, 1820, 6188, 18564⟩ := by
  have h : row 12 = step (row 11) := rowsucc 11
  rw [h, row11]; norm_num [step]

lemma row13 : row 13 = ⟨0, 1111111111111, 16666666666665, 133333333333320, 755555555555480,
    3399999999999660, 12919999999998708, 1, 14, 105, 560, 2380, 8568, 27132⟩ := by
  have h : row 13 = step (row 12) := rowsucc 12
  rw [h, row12]; norm_num [step]

/-! ### The seven bounds, plus the witness -/

lemma val7 : A 7 6 ≤ 10 ^ 12 := by
  rw [← a6_eq 7, row7]; norm_num

lemma val8 : A 8 5 ≤ 10 ^ 12 := by
  rw [← a5_eq 8, row8]; norm_num

lemma val9 : A 9 4 ≤ 10 ^ 12 := by
  rw [← a4_eq 9, row9]; norm_num

lemma val10 : A 10 3 ≤ 10 ^ 12 := by
  rw [← a3_eq 10, row10]; norm_num

lemma val11 : A 11 2 ≤ 10 ^ 12 := by
  rw [← a2_eq 11, row11]; norm_num

lemma val12 : A 12 1 ≤ 10 ^ 12 := by
  rw [← a1_eq 12, row12]; norm_num

lemma val13 : A 13 0 ≤ 10 ^ 12 := by
  rw [← a0_eq 13, row13]; norm_num

lemma witness : 10 ^ 12 < A 13 1 := by
  rw [← a1_eq 13, row13]; norm_num

/-! ### Glue -/

lemma svi_eq (l s : ℕ) : sumValidIntegers l s = A l s := by
  unfold sumValidIntegers A
  rw [Finset.sum_filter, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by positivity : (0:ℕ) < 10 ^ l)]
  simp

lemma A_mono_s (l : ℕ) {s t : ℕ} (h : s ≤ t) : A l s ≤ A l t := by
  unfold A
  refine Finset.sum_le_sum ?_
  intro n _
  by_cases h1 : (Nat.digits 10 n).sum ≤ s
  · have h2 : (Nat.digits 10 n).sum ≤ t := h1.trans h
    simp [h1, h2]
  · simp [h1]

lemma A_le_gauss (l s : ℕ) : A l s ≤ ∑ n ∈ Finset.range (10 ^ l), n := by
  unfold A
  refine Finset.sum_le_sum ?_
  intro n _
  by_cases h1 : (Nat.digits 10 n).sum ≤ s <;> simp [h1]

lemma gauss_le (l : ℕ) (hl : l ≤ 6) :
    ∑ n ∈ Finset.range (10 ^ l), n ≤ 499999500000 := by
  have hle : (10 : ℕ) ^ l ≤ 1000000 := by
    calc (10 : ℕ) ^ l ≤ 10 ^ 6 := Nat.pow_le_pow_right (by norm_num) hl
      _ = 1000000 := by norm_num
  have hsub : Finset.range (10 ^ l) ⊆ Finset.range 1000000 := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have h1 : ∑ n ∈ Finset.range (10 ^ l), n ≤ ∑ n ∈ Finset.range 1000000, n :=
    Finset.sum_le_sum_of_subset hsub
  have h2 : (∑ n ∈ Finset.range 1000000, n) * 2 = 1000000 * (1000000 - 1) :=
    Finset.sum_range_id_mul_two 1000000
  omega

lemma key (l s : ℕ) (hsl : s + l ≤ 13) : A l s ≤ 10 ^ 12 := by
  rcases Nat.lt_or_ge l 7 with hl | hl
  · have hl6 : l ≤ 6 := by omega
    calc A l s ≤ ∑ n ∈ Finset.range (10 ^ l), n := A_le_gauss l s
      _ ≤ 499999500000 := gauss_le l hl6
      _ ≤ 10 ^ 12 := by norm_num
  · have hs : s ≤ 13 - l := by omega
    have hl13 : l ≤ 13 := by omega
    refine le_trans (A_mono_s l hs) ?_
    interval_cases l
    exacts [val7, val8, val9, val10, val11, val12, val13]

end TLB

theorem tight_lower_bound_s_add_l :
    (∀ l s : ℕ, sumValidIntegers l s > 10 ^ 12 → s + l ≥ 14) ∧
      (∃ l s : ℕ, sumValidIntegers l s > 10 ^ 12 ∧ s + l = 14) := by
  constructor
  · intro l s hgt
    rw [TLB.svi_eq] at hgt
    by_contra hcon
    push_neg at hcon
    exact absurd hgt (not_lt.2 (TLB.key l s (by omega)))
  · refine ⟨13, 1, ?_, by norm_num⟩
    rw [TLB.svi_eq]
    exact TLB.witness
```
