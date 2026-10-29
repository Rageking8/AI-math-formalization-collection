# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `19 August 2026`\
Line count: `253`\
Turn count: `2`

## Solution

```lean4
import Mathlib

/-! ### Digit sum lemmas (needed already for termination) -/

private lemma dsum_step (j : ℕ) :
    (Nat.digits 10 j).sum = j % 10 + (Nat.digits 10 (j / 10)).sum := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp
  · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h]
    simp

private lemma dsum_le_self_aux : ∀ N j : ℕ, j ≤ N → (Nat.digits 10 j).sum ≤ j := by
  intro N
  induction N with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp
  | succ N ih =>
    intro j hj
    rw [dsum_step j]
    rcases Nat.lt_or_ge j 10 with h | h
    · have hd : j / 10 = 0 := Nat.div_eq_of_lt h
      rw [hd]
      simp [Nat.mod_eq_of_lt h]
    · have h1 : j / 10 ≤ N := by omega
      have h2 := ih (j / 10) h1
      omega

private lemma dsum_le_self (j : ℕ) : (Nat.digits 10 j).sum ≤ j :=
  dsum_le_self_aux j j le_rfl

private lemma sum_digits_lt (n : ℕ) (hn : 10 ≤ n) : (Nat.digits 10 n).sum < n := by
  rw [dsum_step n]
  have h1 : (Nat.digits 10 (n / 10)).sum ≤ n / 10 := dsum_le_self (n / 10)
  omega

/-! ### The definition -/

def additivePersistence (n : ℕ) : ℕ :=
  if n < 10 then 0
  else 1 + additivePersistence (Nat.digits 10 n).sum
termination_by n
decreasing_by
  rename_i h
  exact sum_digits_lt n (by omega)

/-! ### More digit sum lemmas -/

private lemma dsum_mul_add (r x : ℕ) (hr : r < 10) :
    (Nat.digits 10 (10 * x + r)).sum = r + (Nat.digits 10 x).sum := by
  have h1 : (10 * x + r) % 10 = r := by omega
  have h2 : (10 * x + r) / 10 = x := by omega
  rw [dsum_step (10 * x + r), h1, h2]

private lemma dsum_one : (Nat.digits 10 1).sum = 1 := by
  rw [dsum_step 1]
  norm_num

private lemma dsum_pos_aux : ∀ N j : ℕ, j ≤ N → 0 < j → 0 < (Nat.digits 10 j).sum := by
  intro N
  induction N with
  | zero => intro j h1 h2; omega
  | succ N ih =>
    intro j h1 h2
    rw [dsum_step j]
    rcases Nat.lt_or_ge j 10 with h | h
    · have hmod : j % 10 = j := Nat.mod_eq_of_lt h
      omega
    · have hb1 : 0 < j / 10 := by omega
      have hb2 : j / 10 ≤ N := by omega
      have hb3 := ih (j / 10) hb2 hb1
      omega

private lemma dsum_pos (j : ℕ) (hj : 0 < j) : 0 < (Nat.digits 10 j).sum :=
  dsum_pos_aux j j le_rfl hj

private lemma dsum_le : ∀ m j : ℕ, j < 10 ^ m → (Nat.digits 10 j).sum ≤ 9 * m := by
  intro m
  induction m with
  | zero =>
    intro j hj
    have h : (10:ℕ) ^ 0 = 1 := pow_zero 10
    have hj0 : j = 0 := by omega
    subst hj0
    simp
  | succ m ih =>
    intro j hj
    have hp : (10:ℕ) ^ (m + 1) = 10 ^ m * 10 := by ring
    have h1 : j / 10 < 10 ^ m := by omega
    have h2 := ih (j / 10) h1
    rw [dsum_step j]
    omega

private lemma dsum_lt : ∀ m j : ℕ, j + 1 < 10 ^ m → (Nat.digits 10 j).sum + 1 ≤ 9 * m := by
  intro m
  induction m with
  | zero =>
    intro j hj
    have h : (10:ℕ) ^ 0 = 1 := pow_zero 10
    omega
  | succ m ih =>
    intro j hj
    have hp : (10:ℕ) ^ (m + 1) = 10 ^ m * 10 := by ring
    have h1 : j / 10 < 10 ^ m := by omega
    rw [dsum_step j]
    by_cases hc : j / 10 + 1 < 10 ^ m
    · have h2 := ih (j / 10) hc
      omega
    · have h2 := dsum_le m (j / 10) h1
      omega

private lemma dsum_split : ∀ m A j : ℕ, 0 < A → j < 10 ^ m →
    (Nat.digits 10 (10 ^ m * A + j)).sum
      = (Nat.digits 10 A).sum + (Nat.digits 10 j).sum := by
  intro m
  induction m with
  | zero =>
    intro A j hA hj
    have h : (10:ℕ) ^ 0 = 1 := pow_zero 10
    have hj0 : j = 0 := by omega
    subst hj0
    simp
  | succ m ih =>
    intro A j hA hj
    have hp : (10:ℕ) ^ (m + 1) = 10 ^ m * 10 := by ring
    have h1 : j / 10 < 10 ^ m := by omega
    have hdm : 10 * (j / 10) + j % 10 = j := Nat.div_add_mod j 10
    have key : 10 ^ (m + 1) * A + j = 10 * (10 ^ m * A + j / 10) + j % 10 := by
      calc 10 ^ (m + 1) * A + j
          = 10 ^ m * 10 * A + (10 * (j / 10) + j % 10) := by rw [hdm, hp]
        _ = 10 * (10 ^ m * A + j / 10) + j % 10 := by ring
    rw [key, dsum_mul_add (j % 10) (10 ^ m * A + j / 10) (by omega),
      ih A (j / 10) hA h1, dsum_step j]
    omega

private lemma exists_dsum : ∀ a : ℕ, ∃ A : ℕ, (Nat.digits 10 A).sum = a := by
  intro a
  induction a with
  | zero => exact ⟨0, by simp⟩
  | succ a ih =>
    obtain ⟨A, hA⟩ := ih
    refine ⟨10 * A + 1, ?_⟩
    rw [dsum_mul_add 1 A (by norm_num), hA]
    omega

/-! ### Unfolding `additivePersistence` -/

private lemma ap_def (n : ℕ) :
    additivePersistence n =
      if n < 10 then 0 else 1 + additivePersistence ((Nat.digits 10 n).sum) := by
  first
    | exact additivePersistence.eq_def n
    | rw [additivePersistence]
    | unfold additivePersistence

private lemma ap_small (n : ℕ) (h : n < 10) : additivePersistence n = 0 := by
  rw [ap_def n, if_pos h]

private lemma ap_big (n : ℕ) (h : 10 ≤ n) :
    additivePersistence n = 1 + additivePersistence ((Nat.digits 10 n).sum) := by
  have h' : ¬ n < 10 := by omega
  rw [ap_def n, if_neg h']

/-! ### The base run and the inductive step -/

private lemma base_run : ∀ i < 9, additivePersistence (10 + i) = 1 := by
  intro i hi
  have h1 : (Nat.digits 10 (10 + i)).sum = i + 1 := by
    have h : 10 + i = 10 * 1 + i := by ring
    rw [h, dsum_mul_add i 1 (by omega), dsum_one]
  have h2 := ap_big (10 + i) (by omega)
  rw [h1, ap_small (i + 1) (by omega)] at h2
  omega

private lemma pow_ge : ∀ t : ℕ, t + 1 ≤ 10 ^ t := by
  intro t
  induction t with
  | zero => norm_num
  | succ t ih =>
    have h : (10:ℕ) ^ (t + 1) = 10 ^ t * 10 := by ring
    omega

private lemma step (a p L m : ℕ) (ha : 2 ≤ a) (hm : 1 ≤ m) (hL : 9 * m ≤ L)
    (hrun : ∀ i < L, additivePersistence (a + i) = p) :
    ∃ N, 2 ≤ N ∧ ∀ i < 2 * 10 ^ m - 2, additivePersistence (N + i) = p + 1 := by
  obtain ⟨B, hB⟩ := exists_dsum (a - 2)
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ, A = 10 * B + 1 := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by omega
  have hSA : (Nat.digits 10 A).sum = a - 1 := by
    rw [hAdef, dsum_mul_add 1 B (by norm_num), hB]
    omega
  have hSA1 : (Nat.digits 10 (A + 1)).sum = a := by
    have h : A + 1 = 10 * B + 2 := by omega
    rw [h, dsum_mul_add 2 B (by norm_num), hB]
    omega
  have hpow10 : 10 ≤ 10 ^ m := by
    calc (10:ℕ) = 10 ^ 1 := (pow_one 10).symm
      _ ≤ 10 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hmul : 10 ^ m ≤ 10 ^ m * A := by
    have h := Nat.mul_le_mul (le_refl (10 ^ m)) hA1
    rwa [mul_one] at h
  refine ⟨10 ^ m * A + 1, by omega, ?_⟩
  intro i hi
  have hn10 : 10 ≤ 10 ^ m * A + 1 + i := by omega
  by_cases hc : 1 + i < 10 ^ m
  · have heq : 10 ^ m * A + 1 + i = 10 ^ m * A + (1 + i) := by ring
    have hS : (Nat.digits 10 (10 ^ m * A + 1 + i)).sum
        = a - 1 + (Nat.digits 10 (1 + i)).sum := by
      rw [heq, dsum_split m A (1 + i) (by omega) hc, hSA]
    have h1 : 1 ≤ (Nat.digits 10 (1 + i)).sum := dsum_pos (1 + i) (by omega)
    have h2 : (Nat.digits 10 (1 + i)).sum ≤ 9 * m := dsum_le m (1 + i) hc
    have h3 := hrun ((Nat.digits 10 (1 + i)).sum - 1) (by omega)
    rw [ap_big _ hn10, hS,
      (show a - 1 + (Nat.digits 10 (1 + i)).sum
          = a + ((Nat.digits 10 (1 + i)).sum - 1) by omega), h3]
    omega
  · push_neg at hc
    have hj : (1 + i - 10 ^ m) + 1 < 10 ^ m := by omega
    have heq : 10 ^ m * A + 1 + i = 10 ^ m * (A + 1) + (1 + i - 10 ^ m) := by
      have h : 10 ^ m * (A + 1) = 10 ^ m * A + 10 ^ m := by ring
      omega
    have hS : (Nat.digits 10 (10 ^ m * A + 1 + i)).sum
        = a + (Nat.digits 10 (1 + i - 10 ^ m)).sum := by
      rw [heq, dsum_split m (A + 1) (1 + i - 10 ^ m) (by omega) (by omega), hSA1]
    have h2 : (Nat.digits 10 (1 + i - 10 ^ m)).sum + 1 ≤ 9 * m := dsum_lt m _ hj
    have h3 := hrun ((Nat.digits 10 (1 + i - 10 ^ m)).sum) (by omega)
    rw [ap_big _ hn10, hS, h3]
    omega

private lemma runs : ∀ t : ℕ, ∃ a p L : ℕ,
    2 ≤ a ∧ 9 * (t + 1) ≤ L ∧ ∀ i < L, additivePersistence (a + i) = p := by
  intro t
  induction t with
  | zero => exact ⟨10, 1, 9, by norm_num, by norm_num, base_run⟩
  | succ t ih =>
    obtain ⟨a, p, L, ha, hL, hrun⟩ := ih
    obtain ⟨N, hN, hNrun⟩ := step a p L (t + 1) ha (by omega) hL hrun
    refine ⟨N, p + 1, 2 * 10 ^ (t + 1) - 2, hN, ?_, hNrun⟩
    have h1 : t + 1 ≤ 10 ^ t := pow_ge t
    have h2 : (10:ℕ) ^ (t + 1) = 10 ^ t * 10 := by ring
    omega

theorem arbitrary_consecutive_same_additive_persistence (k : ℕ) :
    ∃ n : ℕ, ∀ i < k, additivePersistence (n + i) = additivePersistence n := by
  obtain ⟨a, p, L, ha, hL, hrun⟩ := runs k
  refine ⟨a, ?_⟩
  intro i hi
  have h0 : additivePersistence a = p := by
    have h := hrun 0 (by omega)
    simpa using h
  rw [hrun i (by omega), h0]
```
