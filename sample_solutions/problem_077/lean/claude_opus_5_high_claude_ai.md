# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `23 August 2026`\
Line count: `368`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def sumValidIntegers (l s : ℕ) : ℕ :=
  ∑ n ∈ (Finset.Ico 1 (10 ^ l)).filter (fun n => (Nat.digits 10 n).sum ≤ s), n

namespace TightBoundAux

def ds (n : ℕ) : ℕ := (Nat.digits 10 n).sum

def Tc (l s : ℕ) : ℕ := ∑ n ∈ Finset.range (10 ^ l), (if ds n ≤ s then 1 else 0)

def Ts (l s : ℕ) : ℕ := ∑ n ∈ Finset.range (10 ^ l), (if ds n ≤ s then n else 0)

def R (l : ℕ) : ℕ := ∑ i ∈ Finset.range l, 10 ^ i

lemma R_succ (l : ℕ) : R (l + 1) = 10 * R l + 1 := by
  unfold R
  rw [Finset.sum_range_succ']
  simp only [pow_succ, pow_zero]
  rw [← Finset.sum_mul]
  ring

/-! ### binomial coefficient facts -/

lemma pascal (n k : ℕ) : (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) :=
  Nat.choose_succ_succ n k

lemma choose_le_succ (n k : ℕ) : n.choose k ≤ (n + 1).choose k := by
  cases k with
  | zero => simp
  | succ j =>
    have h := pascal n j
    omega

lemma choose_le_of_le (k : ℕ) : ∀ m n : ℕ, n ≤ m → n.choose k ≤ m.choose k := by
  intro m
  induction m with
  | zero =>
    intro n h
    have hn : n = 0 := Nat.le_zero.mp h
    subst hn
    exact le_refl _
  | succ m ih =>
    intro n h
    rcases Nat.lt_or_ge n (m + 1) with h1 | h1
    · exact le_trans (ih n (by omega)) (choose_le_succ m k)
    · have hn : n = m + 1 := by omega
      subst hn
      exact le_refl _

lemma hockey1 (l : ℕ) : ∀ s : ℕ,
    ∑ j ∈ Finset.range (s + 1), (l + j).choose l = (l + s + 1).choose (l + 1) := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih]
    have h := pascal (l + s + 1) l
    simp only [← Nat.add_assoc]
    omega

lemma hockey2 (l : ℕ) : ∀ s : ℕ,
    ∑ j ∈ Finset.range (s + 1), (l + j).choose (l + 1) = (l + s + 1).choose (l + 2) := by
  intro s
  induction s with
  | zero =>
    have h1 : l.choose (l + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (l + 1).choose (l + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h2]
  | succ s ih =>
    rw [Finset.sum_range_succ, ih]
    have h := pascal (l + s + 1) (l + 1)
    have e : l + 1 + 1 = l + 2 := by omega
    rw [e] at h
    simp only [← Nat.add_assoc]
    omega

lemma hockey3 (l : ℕ) : ∀ s : ℕ,
    ∑ j ∈ Finset.range (s + 1), (s - j) * (l + j).choose l = (l + s + 1).choose (l + 2) := by
  intro s
  induction s with
  | zero =>
    have h2 : (l + 1).choose (l + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h2]
  | succ s ih =>
    have expand : ∑ j ∈ Finset.range (s + 1 + 1), (s + 1 - j) * (l + j).choose l
        = (∑ j ∈ Finset.range (s + 1), (s - j) * (l + j).choose l)
          + ∑ j ∈ Finset.range (s + 1), (l + j).choose l := by
      rw [Finset.sum_range_succ]
      have hz : s + 1 - (s + 1) = 0 := by omega
      rw [hz, zero_mul, add_zero, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp only [Finset.mem_range] at hj
      have h1 : s + 1 - j = (s - j) + 1 := by omega
      rw [h1]
      ring
    rw [expand, ih, hockey1 l s]
    have h := pascal (l + s + 1) (l + 1)
    have e : l + 1 + 1 = l + 2 := by omega
    rw [e] at h
    simp only [← Nat.add_assoc]
    omega

/-! ### reindexing helpers -/

lemma reflect_sum (n : ℕ) (f : ℕ → ℕ) :
    ∑ j ∈ Finset.range (n + 1), f (n - j) = ∑ j ∈ Finset.range (n + 1), f j := by
  simpa using Finset.sum_range_reflect f (n + 1)

lemma filter_sub (s : ℕ) :
    (Finset.range 10).filter (fun d => d ≤ s) ⊆ Finset.range (s + 1) := by
  intro d hd
  simp only [Finset.mem_filter, Finset.mem_range] at hd ⊢
  omega

lemma key_shift (s : ℕ) (g : ℕ → ℕ) :
    ∑ d ∈ Finset.range 10, (if d ≤ s then g (s - d) else 0)
      ≤ ∑ j ∈ Finset.range (s + 1), g j := by
  calc ∑ d ∈ Finset.range 10, (if d ≤ s then g (s - d) else 0)
      = ∑ d ∈ (Finset.range 10).filter (fun d => d ≤ s), g (s - d) := by
        rw [Finset.sum_filter]
    _ ≤ ∑ d ∈ Finset.range (s + 1), g (s - d) := Finset.sum_le_sum_of_subset (filter_sub s)
    _ = ∑ j ∈ Finset.range (s + 1), g j := reflect_sum s g

lemma key_shift2 (s : ℕ) (g : ℕ → ℕ) :
    ∑ d ∈ Finset.range 10, (if d ≤ s then d * g (s - d) else 0)
      ≤ ∑ j ∈ Finset.range (s + 1), (s - j) * g j := by
  calc ∑ d ∈ Finset.range 10, (if d ≤ s then d * g (s - d) else 0)
      = ∑ d ∈ (Finset.range 10).filter (fun d => d ≤ s), d * g (s - d) := by
        rw [Finset.sum_filter]
    _ ≤ ∑ d ∈ Finset.range (s + 1), d * g (s - d) := Finset.sum_le_sum_of_subset (filter_sub s)
    _ = ∑ j ∈ Finset.range (s + 1), (s - j) * g j := by
        rw [← reflect_sum s (fun d => d * g (s - d))]
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp only [Finset.mem_range] at hj
        show (s - j) * g (s - (s - j)) = (s - j) * g j
        have h2 : s - (s - j) = j := by omega
        rw [h2]

lemma sum_split (f : ℕ → ℕ) (k : ℕ) :
    ∑ n ∈ Finset.range (10 * k), f n
      = ∑ m ∈ Finset.range k, ∑ d ∈ Finset.range 10, f (10 * m + d) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ (fun m => ∑ d ∈ Finset.range 10, f (10 * m + d)) k, ← ih]
    have e2 : ∑ d ∈ Finset.range 10, f (10 * k + d)
        = ∑ i ∈ Finset.Ico (10 * k) (10 * k + 10), f i := by
      have hh : 10 * k + 10 - 10 * k = 10 := by omega
      rw [Finset.sum_Ico_eq_sum_range, hh]
    have e3 : ∑ n ∈ Finset.range (10 * k), f n = ∑ i ∈ Finset.Ico 0 (10 * k), f i := by
      rw [Finset.range_eq_Ico]
    have e4 : ∑ n ∈ Finset.range (10 * (k + 1)), f n
        = ∑ i ∈ Finset.Ico 0 (10 * (k + 1)), f i := by
      rw [Finset.range_eq_Ico]
    rw [e2, e3, e4]
    have e5 : (10 : ℕ) * (k + 1) = 10 * k + 10 := by ring
    rw [e5]
    exact (Finset.sum_Ico_consecutive f (Nat.zero_le _) (by omega)).symm

/-! ### the digit recursion -/

lemma ds_step (m d : ℕ) (hd : d < 10) : ds (10 * m + d) = d + ds m := by
  rcases Nat.eq_zero_or_pos (10 * m + d) with h | h
  · have hm : m = 0 := by omega
    have hd0 : d = 0 := by omega
    subst hm
    subst hd0
    simp [ds]
  · unfold ds
    rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 10) h]
    have h1 : (10 * m + d) % 10 = d := by omega
    have h2 : (10 * m + d) / 10 = m := by omega
    rw [h1, h2, List.sum_cons]

lemma Tc_succ (l s : ℕ) :
    Tc (l + 1) s = ∑ d ∈ Finset.range 10, (if d ≤ s then Tc l (s - d) else 0) := by
  unfold Tc
  have h10 : (10 : ℕ) ^ (l + 1) = 10 * 10 ^ l := by ring
  rw [h10, sum_split, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d hd
  simp only [Finset.mem_range] at hd
  by_cases hds : d ≤ s
  · rw [if_pos hds]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [ds_step m d hd]
    by_cases h : ds m ≤ s - d
    · rw [if_pos (show d + ds m ≤ s by omega), if_pos h]
    · rw [if_neg (show ¬ (d + ds m ≤ s) by omega), if_neg h]
  · rw [if_neg hds]
    refine Finset.sum_eq_zero ?_
    intro m _
    rw [ds_step m d hd, if_neg (show ¬ (d + ds m ≤ s) by omega)]

lemma Ts_succ (l s : ℕ) :
    Ts (l + 1) s
      = ∑ d ∈ Finset.range 10, (if d ≤ s then 10 * Ts l (s - d) + d * Tc l (s - d) else 0) := by
  unfold Ts Tc
  have h10 : (10 : ℕ) ^ (l + 1) = 10 * 10 ^ l := by ring
  rw [h10, sum_split, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d hd
  simp only [Finset.mem_range] at hd
  by_cases hds : d ≤ s
  · rw [if_pos hds, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [ds_step m d hd]
    by_cases h : ds m ≤ s - d
    · rw [if_pos (show d + ds m ≤ s by omega), if_pos h, if_pos h]
      ring
    · rw [if_neg (show ¬ (d + ds m ≤ s) by omega), if_neg h, if_neg h]
      ring
  · rw [if_neg hds]
    refine Finset.sum_eq_zero ?_
    intro m _
    rw [ds_step m d hd, if_neg (show ¬ (d + ds m ≤ s) by omega)]

/-! ### the main bound -/

lemma main_bound (l : ℕ) : ∀ s : ℕ,
    Tc l s ≤ (l + s).choose l ∧ Ts l s ≤ (l + s).choose (l + 1) * R l := by
  induction l with
  | zero =>
    intro s
    constructor
    · simp [Tc, ds]
    · simp [Ts]
  | succ l ih =>
    intro s
    constructor
    · rw [Tc_succ]
      calc ∑ d ∈ Finset.range 10, (if d ≤ s then Tc l (s - d) else 0)
          ≤ ∑ j ∈ Finset.range (s + 1), Tc l j := key_shift s (fun j => Tc l j)
        _ ≤ ∑ j ∈ Finset.range (s + 1), (l + j).choose l :=
            Finset.sum_le_sum (fun j _ => (ih j).1)
        _ = (l + s + 1).choose (l + 1) := hockey1 l s
        _ = (l + 1 + s).choose (l + 1) := by rw [show l + s + 1 = l + 1 + s from by omega]
    · rw [Ts_succ]
      have step1 : ∑ d ∈ Finset.range 10,
            (if d ≤ s then 10 * Ts l (s - d) + d * Tc l (s - d) else 0)
          = (∑ d ∈ Finset.range 10, (if d ≤ s then 10 * Ts l (s - d) else 0))
            + ∑ d ∈ Finset.range 10, (if d ≤ s then d * Tc l (s - d) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro d _
        by_cases h : d ≤ s
        · simp [h]
        · simp [h]
      have step2 : (∑ d ∈ Finset.range 10, (if d ≤ s then 10 * Ts l (s - d) else 0))
          ≤ ∑ j ∈ Finset.range (s + 1), 10 * Ts l j := key_shift s (fun j => 10 * Ts l j)
      have step3 : (∑ d ∈ Finset.range 10, (if d ≤ s then d * Tc l (s - d) else 0))
          ≤ ∑ j ∈ Finset.range (s + 1), (s - j) * Tc l j := key_shift2 s (fun j => Tc l j)
      have step4 : (∑ j ∈ Finset.range (s + 1), 10 * Ts l j)
          ≤ 10 * ((l + s + 1).choose (l + 2) * R l) := by
        have e1 : ∑ j ∈ Finset.range (s + 1), 10 * Ts l j
            ≤ ∑ j ∈ Finset.range (s + 1), 10 * ((l + j).choose (l + 1) * R l) :=
          Finset.sum_le_sum (fun j _ => Nat.mul_le_mul (le_refl 10) (ih j).2)
        have e2 : ∑ j ∈ Finset.range (s + 1), 10 * ((l + j).choose (l + 1) * R l)
            = 10 * ((∑ j ∈ Finset.range (s + 1), (l + j).choose (l + 1)) * R l) := by
          rw [Finset.sum_mul, Finset.mul_sum]
        rw [e2, hockey2 l s] at e1
        exact e1
      have step5 : (∑ j ∈ Finset.range (s + 1), (s - j) * Tc l j)
          ≤ (l + s + 1).choose (l + 2) := by
        have e1 : ∑ j ∈ Finset.range (s + 1), (s - j) * Tc l j
            ≤ ∑ j ∈ Finset.range (s + 1), (s - j) * (l + j).choose l :=
          Finset.sum_le_sum (fun j _ => Nat.mul_le_mul (le_refl _) (ih j).1)
        rw [hockey3 l s] at e1
        exact e1
      have final : 10 * ((l + s + 1).choose (l + 2) * R l) + (l + s + 1).choose (l + 2)
          = (l + 1 + s).choose (l + 1 + 1) * R (l + 1) := by
        rw [R_succ]
        have e1 : l + 1 + s = l + s + 1 := by omega
        have e2 : l + 1 + 1 = l + 2 := by omega
        rw [e1, e2]
        ring
      calc ∑ d ∈ Finset.range 10,
              (if d ≤ s then 10 * Ts l (s - d) + d * Tc l (s - d) else 0)
          = _ := step1
        _ ≤ (∑ j ∈ Finset.range (s + 1), 10 * Ts l j)
              + ∑ j ∈ Finset.range (s + 1), (s - j) * Tc l j := Nat.add_le_add step2 step3
        _ ≤ 10 * ((l + s + 1).choose (l + 2) * R l) + (l + s + 1).choose (l + 2) :=
            Nat.add_le_add step4 step5
        _ = (l + 1 + s).choose (l + 1 + 1) * R (l + 1) := final

set_option maxRecDepth 10000 in
lemma table (l : ℕ) (hl : l ≤ 13) : (13 : ℕ).choose (l + 1) * R l ≤ 10 ^ 12 := by
  interval_cases l <;>
    simp only [R, Finset.sum_range_succ, Finset.sum_range_zero] <;> decide

lemma bound_final (l s : ℕ) (h : l + s ≤ 13) : Ts l s ≤ 10 ^ 12 := by
  have h1 := (main_bound l s).2
  have h2 : (l + s).choose (l + 1) ≤ (13 : ℕ).choose (l + 1) :=
    choose_le_of_le (l + 1) 13 (l + s) h
  calc Ts l s ≤ (l + s).choose (l + 1) * R l := h1
    _ ≤ (13 : ℕ).choose (l + 1) * R l := Nat.mul_le_mul h2 (le_refl _)
    _ ≤ 10 ^ 12 := table l (by omega)

lemma sVI_eq (l s : ℕ) : sumValidIntegers l s = Ts l s := by
  unfold sumValidIntegers Ts ds
  rw [Finset.sum_filter]
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
    omega
  · intro x hx hnx
    simp only [Finset.mem_range] at hx
    have hx0 : x = 0 := by
      by_contra hne
      exact hnx (Finset.mem_Ico.mpr ⟨by omega, hx⟩)
    subst hx0
    simp

/-! ### the witness -/

lemma ds_pow (k : ℕ) : ds (10 ^ k) = 1 := by
  induction k with
  | zero =>
    have h1 : (10 : ℕ) ^ 0 = 1 := by norm_num
    rw [h1]
    unfold ds
    rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 10) (by norm_num : 0 < 1)]
    norm_num
  | succ k ih =>
    have h : (10 : ℕ) ^ (k + 1) = 10 * 10 ^ k + 0 := by ring
    rw [h, ds_step (10 ^ k) 0 (by norm_num)]
    omega

lemma exists_witness : sumValidIntegers 13 1 > 10 ^ 12 := by
  have h11 : ds (10 ^ 11) = 1 := ds_pow 11
  have h12 : ds (10 ^ 12) = 1 := ds_pow 12
  unfold ds at h11 h12
  have hsub : ({10 ^ 11, 10 ^ 12} : Finset ℕ)
      ⊆ (Finset.Ico 1 (10 ^ 13)).filter (fun n => (Nat.digits 10 n).sum ≤ 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp only [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
      omega
    · simp only [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
      omega
  have hle : ∑ x ∈ ({10 ^ 11, 10 ^ 12} : Finset ℕ), x ≤ sumValidIntegers 13 1 :=
    Finset.sum_le_sum_of_subset hsub
  have hval : ∑ x ∈ ({10 ^ 11, 10 ^ 12} : Finset ℕ), x = 10 ^ 11 + 10 ^ 12 :=
    Finset.sum_pair (by norm_num)
  have hpos : (10 : ℕ) ^ 12 < 10 ^ 11 + 10 ^ 12 := by norm_num
  omega

end TightBoundAux

theorem tight_lower_bound_s_add_l :
    (∀ l s : ℕ, sumValidIntegers l s > 10 ^ 12 → s + l ≥ 14) ∧
      (∃ l s : ℕ, sumValidIntegers l s > 10 ^ 12 ∧ s + l = 14) := by
  constructor
  · intro l s hgt
    by_contra hc
    have hls : l + s ≤ 13 := by omega
    have hb := TightBoundAux.bound_final l s hls
    rw [TightBoundAux.sVI_eq] at hgt
    omega
  · exact ⟨13, 1, TightBoundAux.exists_witness, by norm_num⟩
```
