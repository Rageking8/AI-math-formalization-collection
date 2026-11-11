# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `11 November 2026`\
Line count: `206`\
Turn count: `1`

## Solution

```lean4
import Mathlib

lemma m7_key_rep (s : ℕ) : ∃ R : ℕ, s ≤ R ∧ ∀ (x y z : ℕ) (T : List ℕ),
    Nat.ofDigits 10 ((List.replicate s [x, y, z]).flatten ++ T) =
      (x + 10 * y + 100 * z) * R + (999 * R + 1) * Nat.ofDigits 10 T := by
  induction s with
  | zero =>
    refine ⟨0, le_refl _, ?_⟩
    intro x y z T
    simp only [List.replicate_zero, List.flatten_nil, List.nil_append]
    ring
  | succ s ih =>
    obtain ⟨R, hR, h⟩ := ih
    refine ⟨1000 * R + 1, by omega, ?_⟩
    intro x y z T
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc]
    simp only [List.cons_append, List.nil_append, Nat.ofDigits_cons]
    rw [h]
    ring

lemma m7_cnt_rep (d s : ℕ) (l : List ℕ) :
    List.count d (List.replicate s l).flatten = s * List.count d l := by
  induction s with
  | zero => simp only [List.replicate_zero, List.flatten_nil, List.count_nil, Nat.zero_mul]
  | succ s ih =>
    rw [List.replicate_succ, List.flatten_cons, List.count_append, ih]
    ring

lemma m7_lt_rep (s : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x < 10) :
    ∀ x ∈ (List.replicate s l).flatten, x < 10 := by
  intro x hx
  rw [List.mem_flatten] at hx
  obtain ⟨l', hl', hx'⟩ := hx
  rw [List.eq_of_mem_replicate hl'] at hx'
  exact hl x hx'

lemma m7_lt_app (A B : List ℕ) (hA : ∀ x ∈ A, x < 10) (hB : ∀ x ∈ B, x < 10) :
    ∀ x ∈ A ++ B, x < 10 := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hA x h
  · exact hB x h

lemma m7_mode7_of_list (N : ℕ) (P : List ℕ) (d : ℕ)
    (hN : N = Nat.ofDigits 10 (P ++ [d])) (hP : ∀ x ∈ P, x < 10) (hd0 : 0 < d) (hd : d < 10)
    (hc : ∀ e, e < 10 → e ≠ 7 → List.count e (P ++ [d]) < List.count 7 (P ++ [d])) :
    ∀ e : ℕ, e ≠ 7 → (Nat.digits 10 N).count e < (Nat.digits 10 N).count 7 := by
  have hall : ∀ x ∈ P ++ [d], x < 10 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hP x hx
    · rw [List.mem_singleton] at hx
      omega
  have hdig : Nat.digits 10 N = P ++ [d] := by
    rw [hN]
    apply Nat.digits_ofDigits 10 (by norm_num) _ hall
    intro hne
    rw [List.getLast_append_singleton]
    omega
  rw [hdig]
  intro e hne
  rcases Nat.lt_or_ge e 10 with he | he
  · exact hc e he hne
  · have h0 : List.count e (P ++ [d]) = 0 := by
      apply List.count_eq_zero_of_not_mem
      intro hmem
      have := hall e hmem
      omega
    have h7 := hc 0 (by norm_num) (by norm_num)
    omega

def m7_sqL (a : ℕ) : List ℕ :=
      [9, 8, 8, 8, 8, 8] ++
      ((List.replicate a [8, 8, 8]).flatten ++
      ([8, 8, 8, 2, 7, 6, 6, 6, 6] ++
      ((List.replicate a [6, 6, 6]).flatten ++
      ([6, 6, 6, 2, 4, 6, 5, 5, 5, 5, 5, 5] ++
      ((List.replicate a [5, 5, 5]).flatten ++
      ((List.replicate a [5, 5, 5]).flatten ++
      ([5, 5, 5, 5, 5, 5, 5, 5, 5, 1, 7, 6, 6, 6, 6] ++
      ((List.replicate a [6, 6, 6]).flatten ++
      ([6, 6, 6, 4, 1, 9, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] ++
      ((List.replicate a [7, 7, 7]).flatten ++
      ((List.replicate a [7, 7, 7]).flatten ++
      ((List.replicate a [7, 7, 7]).flatten ++
      ([7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 3])))))))))))))

set_option maxRecDepth 100000 in
lemma sqL_id (a R : ℕ) (h : ∀ (x y z : ℕ) (T : List ℕ),
    Nat.ofDigits 10 ((List.replicate a [x, y, z]).flatten ++ T) =
      (x + 10 * y + 100 * z) * R + (999 * R + 1) * Nat.ofDigits 10 T) :
    (7333333333333333333333333342666666667 + 29304000000000000000000000009324000000000 * R + 43912044000000000000000000000000000000000000 * R ^ 2 + 29245421304000000000000000000000000000000000000 * R ^ 3 + 7304043970674000000000000000000000000000000000000 * R ^ 4) ^ 2 = Nat.ofDigits 10 (m7_sqL a ++ [5]) := by
  simp only [m7_sqL, List.append_assoc, List.cons_append, List.nil_append, Nat.ofDigits_cons,
    Nat.ofDigits_nil, h]
  ring

lemma sqL_lt (a : ℕ) : ∀ x ∈ m7_sqL a, x < 10 :=
  (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (by decide))))))))))))))

lemma sqL_cnt (a : ℕ) : ∀ e, e < 10 → e ≠ 7 →
    List.count e (m7_sqL a ++ [5]) < List.count 7 (m7_sqL a ++ [5]) := by
  intro e he hne
  simp only [m7_sqL, List.count_append, m7_cnt_rep]
  interval_cases e
  all_goals first
    | exact absurd rfl hne
    | (simp only [List.count_cons, List.count_nil]; norm_num; done)
    | (simp only [List.count_cons, List.count_nil]; norm_num; omega)

def m7_cuL (a : ℕ) : List ℕ :=
      [3, 2, 7, 9, 2, 6] ++
      ((List.replicate a [9, 2, 6]).flatten ++
      ([9, 2, 6, 7, 7, 3, 2, 5, 8] ++
      ((List.replicate a [1, 5, 8]).flatten ++
      ([1, 5, 8, 9, 3, 5, 8, 0, 4] ++
      ((List.replicate a [7, 0, 4]).flatten ++
      ([7, 0, 4, 3, 8, 1, 1, 7, 3] ++
      ((List.replicate a [0, 7, 3]).flatten ++
      ([0, 7, 3, 2, 7, 6, 9, 5, 2] ++
      ((List.replicate a [9, 5, 2]).flatten ++
      ([9, 5, 2, 3, 8, 4, 5, 0, 7] ++
      ((List.replicate a [3, 0, 7]).flatten ++
      ([3, 0, 7, 5, 7, 1, 1, 6, 2, 9, 5, 2] ++
      ((List.replicate a [9, 5, 2]).flatten ++
      ((List.replicate a [9, 5, 2]).flatten ++
      ([9, 5, 2, 9, 5, 2, 9, 5, 2, 7, 4, 8, 8, 4, 1] ++
      ((List.replicate a [8, 4, 1]).flatten ++
      ([8, 4, 1, 6, 7, 8, 1, 7, 3, 0, 7, 3, 0, 7, 3, 0, 7, 3] ++
      ((List.replicate a [0, 7, 3]).flatten ++
      ((List.replicate a [0, 7, 3]).flatten ++
      ((List.replicate a [0, 7, 3]).flatten ++
      ([0, 7, 3, 0, 7, 3, 0, 7, 3, 0, 7, 3, 4, 9])))))))))))))))))))))

set_option maxRecDepth 100000 in
lemma cuL_id (a R : ℕ) (h : ∀ (x y z : ℕ) (T : List ℕ),
    Nat.ofDigits 10 ((List.replicate a [x, y, z]).flatten ++ T) =
      (x + 10 * y + 100 * z) * R + (999 * R + 1) * Nat.ofDigits 10 T) :
    (7333333333333333333333333342666666667 + 29304000000000000000000000009324000000000 * R + 43912044000000000000000000000000000000000000 * R ^ 2 + 29245421304000000000000000000000000000000000000 * R ^ 3 + 7304043970674000000000000000000000000000000000000 * R ^ 4 + 4) ^ 3 + 12 = Nat.ofDigits 10 (m7_cuL a ++ [3]) := by
  simp only [m7_cuL, List.append_assoc, List.cons_append, List.nil_append, Nat.ofDigits_cons,
    Nat.ofDigits_nil, h]
  ring

lemma cuL_lt (a : ℕ) : ∀ x ∈ m7_cuL a, x < 10 :=
  (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (by decide)
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (m7_lt_app _ _ (m7_lt_rep _ _ (by decide))
    (by decide))))))))))))))))))))))

lemma cuL_cnt (a : ℕ) : ∀ e, e < 10 → e ≠ 7 →
    List.count e (m7_cuL a ++ [3]) < List.count 7 (m7_cuL a ++ [3]) := by
  intro e he hne
  simp only [m7_cuL, List.count_append, m7_cnt_rep]
  interval_cases e
  all_goals first
    | exact absurd rfl hne
    | (simp only [List.count_cons, List.count_nil]; norm_num; done)
    | (simp only [List.count_cons, List.count_nil]; norm_num; omega)

theorem infinite_positive_integers_mode_digit_seven :
    Set.Infinite { n : ℕ | 0 < n ∧
      (∀ d : ℕ, d ≠ 7 → (Nat.digits 10 ((n - 4) ^ 2)).count d <
      (Nat.digits 10 ((n - 4) ^ 2)).count 7) ∧
      (∀ d : ℕ, d ≠ 7 → (Nat.digits 10 (n ^ 3 + 12)).count d <
      (Nat.digits 10 (n ^ 3 + 12)).count 7) } := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨R, hR, h⟩ := m7_key_rep a
  refine ⟨7333333333333333333333333342666666667 + 29304000000000000000000000009324000000000 * R + 43912044000000000000000000000000000000000000 * R ^ 2 + 29245421304000000000000000000000000000000000000 * R ^ 3 + 7304043970674000000000000000000000000000000000000 * R ^ 4 + 4, ⟨by omega, ?_, ?_⟩, ?_⟩
  · rw [Nat.add_sub_cancel]
    exact m7_mode7_of_list _ _ 5 (sqL_id a R h) (sqL_lt a) (by norm_num) (by norm_num) (sqL_cnt a)
  · exact m7_mode7_of_list _ _ 3 (cuL_id a R h) (cuL_lt a) (by norm_num) (by norm_num) (cuL_cnt a)
  · have h2 := Nat.zero_le (R ^ 2)
    have h3 := Nat.zero_le (R ^ 3)
    have h4 := Nat.zero_le (R ^ 4)
    omega
```
