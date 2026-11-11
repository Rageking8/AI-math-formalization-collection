# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `11 November 2026`\
Line count: `157`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def sumValidIntegers (l s : ℕ) : ℕ :=
  ∑ n ∈ (Finset.Ico 1 (10 ^ l)).filter (fun n => (Nat.digits 10 n).sum ≤ s), n

/-- number of `n < 10 ^ l` with digit sum `≤ s` -/
def sumValidCnt : ℕ → ℕ → ℕ
  | 0, _ => 1
  | l + 1, s => ∑ d ∈ Finset.range 10, if d ≤ s then sumValidCnt l (s - d) else 0

/-- sum of the `n < 10 ^ l` with digit sum `≤ s` -/
def sumValidTot : ℕ → ℕ → ℕ
  | 0, _ => 0
  | l + 1, s => ∑ d ∈ Finset.range 10,
      if d ≤ s then 10 * sumValidTot l (s - d) + d * sumValidCnt l (s - d) else 0

lemma sumValid_digits_step (n : ℕ) :
    (Nat.digits 10 n).sum = n % 10 + (Nat.digits 10 (n / 10)).sum := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · conv_lhs => rw [Nat.digits_def' (by norm_num) h]
    rw [List.sum_cons]

lemma sumValid_digits_step' (m d : ℕ) (hd : d < 10) :
    (Nat.digits 10 (m * 10 + d)).sum = d + (Nat.digits 10 m).sum := by
  rw [sumValid_digits_step]
  have h1 : (m * 10 + d) % 10 = d := by omega
  have h2 : (m * 10 + d) / 10 = m := by omega
  rw [h1, h2]

lemma sumValid_range_mul (f : ℕ → ℕ) (a b : ℕ) :
    ∑ n ∈ Finset.range (a * b), f n
      = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f (i * b + j) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : (a + 1) * b = a * b + b := by ring
    rw [e, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma sumValid_cnt_eq (l : ℕ) : ∀ s : ℕ,
    ∑ n ∈ Finset.range (10 ^ l), (if (Nat.digits 10 n).sum ≤ s then 1 else 0)
      = sumValidCnt l s := by
  induction l with
  | zero =>
    intro s
    rw [pow_zero, Finset.sum_range_one]
    rw [Nat.digits_zero, List.sum_nil, if_pos (Nat.zero_le s)]
    rfl
  | succ l ih =>
    intro s
    rw [pow_succ, sumValid_range_mul, Finset.sum_comm, sumValidCnt]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd' : d < 10 := Finset.mem_range.1 hd
    by_cases h : d ≤ s
    · rw [if_pos h, ← ih (s - d)]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [sumValid_digits_step' m d hd']
      have e : d + (Nat.digits 10 m).sum ≤ s ↔ (Nat.digits 10 m).sum ≤ s - d := by omega
      by_cases h2 : (Nat.digits 10 m).sum ≤ s - d
      · rw [if_pos h2, if_pos (e.2 h2)]
      · rw [if_neg h2, if_neg (fun h3 => h2 (e.1 h3))]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [sumValid_digits_step' m d hd']
      exact if_neg (by omega)

lemma sumValid_tot_eq (l : ℕ) : ∀ s : ℕ,
    ∑ n ∈ Finset.range (10 ^ l), (if (Nat.digits 10 n).sum ≤ s then n else 0)
      = sumValidTot l s := by
  induction l with
  | zero =>
    intro s
    rw [pow_zero, Finset.sum_range_one]
    rw [Nat.digits_zero, List.sum_nil, if_pos (Nat.zero_le s)]
    rfl
  | succ l ih =>
    intro s
    rw [pow_succ, sumValid_range_mul, Finset.sum_comm, sumValidTot]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd' : d < 10 := Finset.mem_range.1 hd
    by_cases h : d ≤ s
    · rw [if_pos h, ← ih (s - d), ← sumValid_cnt_eq l (s - d), Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [sumValid_digits_step' m d hd']
      have e : d + (Nat.digits 10 m).sum ≤ s ↔ (Nat.digits 10 m).sum ≤ s - d := by omega
      by_cases h2 : (Nat.digits 10 m).sum ≤ s - d
      · rw [if_pos h2, if_pos h2, if_pos (e.2 h2)]; ring
      · rw [if_neg h2, if_neg h2, if_neg (fun h3 => h2 (e.1 h3))]; ring
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [sumValid_digits_step' m d hd']
      exact if_neg (by omega)

lemma sumValidIntegers_eq (l s : ℕ) : sumValidIntegers l s = sumValidTot l s := by
  rw [← sumValid_tot_eq l s, sumValidIntegers, Finset.sum_filter,
    Finset.sum_range_eq_add_Ico _ (pow_pos (by norm_num) l)]
  have h0 : (if (Nat.digits 10 0).sum ≤ s then 0 else 0) = 0 := by
    split_ifs <;> rfl
  rw [h0, zero_add]

theorem tight_lower_bound_s_add_l :
    (∀ l s : ℕ, sumValidIntegers l s > 10 ^ 12 → s + l ≥ 14) ∧
      (∃ l s : ℕ, sumValidIntegers l s > 10 ^ 12 ∧ s + l = 14) := by
  have hmono : ∀ l s t : ℕ, s ≤ t → sumValidIntegers l s ≤ sumValidIntegers l t := by
    intro l s t hst
    unfold sumValidIntegers
    apply Finset.sum_le_sum_of_subset
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.trans hst⟩
  have hsmall : ∀ l s : ℕ, l ≤ 6 → sumValidIntegers l s ≤ 10 ^ 12 := by
    intro l s hl
    unfold sumValidIntegers
    have h10 : 10 ^ l ≤ 10 ^ 6 := Nat.pow_le_pow_right (by norm_num) hl
    calc ∑ n ∈ (Finset.Ico 1 (10 ^ l)).filter (fun n => (Nat.digits 10 n).sum ≤ s), n
        ≤ ∑ n ∈ Finset.range (10 ^ l), n := by
          apply Finset.sum_le_sum_of_subset
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Ico] at hn
          exact Finset.mem_range.2 hn.1.2
      _ ≤ ∑ _n ∈ Finset.range (10 ^ l), 10 ^ 6 := by
          apply Finset.sum_le_sum
          intro n hn
          exact le_of_lt (lt_of_lt_of_le (Finset.mem_range.1 hn) h10)
      _ = 10 ^ l * 10 ^ 6 := by
          rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_range]
      _ ≤ 10 ^ 6 * 10 ^ 6 := Nat.mul_le_mul_right _ h10
      _ = 10 ^ 12 := by norm_num
  have h7 : sumValidTot 7 6 ≤ 10 ^ 12 := by decide +kernel
  have h8 : sumValidTot 8 5 ≤ 10 ^ 12 := by decide +kernel
  have h9 : sumValidTot 9 4 ≤ 10 ^ 12 := by decide +kernel
  have h10 : sumValidTot 10 3 ≤ 10 ^ 12 := by decide +kernel
  have h11 : sumValidTot 11 2 ≤ 10 ^ 12 := by decide +kernel
  have h12 : sumValidTot 12 1 ≤ 10 ^ 12 := by decide +kernel
  have h13 : sumValidTot 13 0 ≤ 10 ^ 12 := by decide +kernel
  have hbig : sumValidTot 13 1 > 10 ^ 12 := by decide +kernel
  rw [← sumValidIntegers_eq] at h7 h8 h9 h10 h11 h12 h13 hbig
  constructor
  · intro l s h
    by_contra hc
    have hls : s + l ≤ 13 := by omega
    have hle : sumValidIntegers l s ≤ 10 ^ 12 := by
      rcases Nat.lt_or_ge l 7 with hl | hl
      · exact hsmall l s (by omega)
      · have hl13 : l ≤ 13 := by omega
        interval_cases l
        · exact (hmono 7 s 6 (by omega)).trans h7
        · exact (hmono 8 s 5 (by omega)).trans h8
        · exact (hmono 9 s 4 (by omega)).trans h9
        · exact (hmono 10 s 3 (by omega)).trans h10
        · exact (hmono 11 s 2 (by omega)).trans h11
        · exact (hmono 12 s 1 (by omega)).trans h12
        · exact (hmono 13 s 0 (by omega)).trans h13
    omega
  · exact ⟨13, 1, hbig, rfl⟩
```
