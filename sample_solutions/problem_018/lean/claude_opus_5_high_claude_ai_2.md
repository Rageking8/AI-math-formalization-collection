# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `31 July 2026`\
Line count: `187`\
Turn count: `2`

## Note

The solution is more verbose as the model is explicitly told not to use `native_decide`.

## Solution

```lean4
import Mathlib

set_option maxRecDepth 100000

/-- Fuel-based computation of `∑ 32 ^ d` over the base-10 digits of `n`. -/
def dw : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n = 0 then 0 else 32 ^ (n % 10) + dw f (n / 10)

lemma dw_zero (n : ℕ) : dw 0 n = 0 := by simp [dw]

lemma dw_succ (f n : ℕ) :
    dw (f + 1) n = if n = 0 then 0 else 32 ^ (n % 10) + dw f (n / 10) := by
  simp [dw]

lemma dw_eq : ∀ (f n : ℕ), n < 10 ^ f →
    dw f n = ((Nat.digits 10 n).map (fun d => 32 ^ d)).sum := by
  intro f
  induction f with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by simpa using hn
    subst hn0
    simp [dw_zero]
  | succ f ih =>
    intro n hn
    rw [dw_succ]
    by_cases h : n = 0
    · subst h; simp
    · rw [if_neg h]
      have hlt : n / 10 < 10 ^ f := by
        apply Nat.div_lt_of_lt_mul
        calc n < 10 ^ (f + 1) := hn
          _ = 10 * 10 ^ f := by ring
      rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) (Nat.pos_of_ne_zero h), ih _ hlt]
      simp

lemma digits_len_le_of_lt_pow : ∀ (k m : ℕ), m < 10 ^ k → (Nat.digits 10 m).length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by simpa using hm
    subst hm0
    simp
  | succ k ih =>
    intro m hm
    by_cases h : m = 0
    · subst h; simp
    · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) (Nat.pos_of_ne_zero h)]
      have hlt : m / 10 < 10 ^ k := by
        apply Nat.div_lt_of_lt_mul
        calc m < 10 ^ (k + 1) := hm
          _ = 10 * 10 ^ k := by ring
      have h2 := ih _ hlt
      simp only [List.length_cons]
      omega

lemma lt_pow_of_digits_len_le : ∀ (k m : ℕ), (Nat.digits 10 m).length ≤ k → m < 10 ^ k := by
  intro k
  induction k with
  | zero =>
    intro m hm
    by_cases h : m = 0
    · subst h; norm_num
    · exfalso
      rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) (Nat.pos_of_ne_zero h)] at hm
      simp only [List.length_cons] at hm
      omega
  | succ k ih =>
    intro m hm
    by_cases h : m = 0
    · subst h; positivity
    · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) (Nat.pos_of_ne_zero h)] at hm
      simp only [List.length_cons] at hm
      have h1 : m / 10 < 10 ^ k := ih _ (by omega)
      have h3 : m / 10 + 1 ≤ 10 ^ k := h1
      have h4 : m < 10 * (m / 10 + 1) := by omega
      calc m < 10 * (m / 10 + 1) := h4
        _ ≤ 10 * 10 ^ k := Nat.mul_le_mul (le_refl 10) h3
        _ = 10 ^ (k + 1) := by ring

/-- Checks `k` consecutive candidates starting at `s`. -/
def rchk : ℕ → ℕ → Bool
  | _, 0 => true
  | s, k + 1 => (dw 12 ((s + k) ^ 2) + dw 12 ((s + k) ^ 3) != 72638703667264) && rchk s k

lemma rchk_succ (s k : ℕ) :
    rchk s (k + 1) =
      ((dw 12 ((s + k) ^ 2) + dw 12 ((s + k) ^ 3) != 72638703667264) && rchk s k) := by
  simp [rchk]

lemma rchk_spec : ∀ (s k : ℕ), rchk s k = true → ∀ j, j < k →
    dw 12 ((s + j) ^ 2) + dw 12 ((s + j) ^ 3) ≠ 72638703667264 := by
  intro s k
  induction k with
  | zero => intro _ j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    intro h j hj
    rw [rchk_succ, Bool.and_eq_true] at h
    rcases (Nat.lt_succ_iff.mp hj).lt_or_eq with hj' | rfl
    · exact ih h.2 j hj'
    · simpa using h.1

theorem no_nat_sq_cube_digits_one_through_nine_twice :
    ¬ ∃ (n : ℕ), List.Perm (Nat.digits 10 (n ^ 2) ++ Nat.digits 10 (n ^ 3))
      (List.range' 1 9 ++ List.range' 1 9) := by
  rintro ⟨n, hp⟩
  rw [show List.range' 1 9 = [1, 2, 3, 4, 5, 6, 7, 8, 9] from rfl] at hp
  have hlen : (Nat.digits 10 (n ^ 2)).length + (Nat.digits 10 (n ^ 3)).length = 18 := by
    have h := hp.length_eq
    simpa using h
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hlen
  have hn2 : 0 < n ^ 2 := pow_pos (Nat.pos_of_ne_zero hn0) 2
  have hn3 : 0 < n ^ 3 := pow_pos (Nat.pos_of_ne_zero hn0) 3
  have hA1 : 1 ≤ (Nat.digits 10 (n ^ 2)).length := by
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hn2]
    simp only [List.length_cons]
    omega
  have hB1 : 1 ≤ (Nat.digits 10 (n ^ 3)).length := by
    rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) hn3]
    simp only [List.length_cons]
    omega
  have l2 : (10:ℕ) ^ ((Nat.digits 10 (n ^ 2)).length - 1) ≤ n ^ 2 := by
    by_contra hc
    push_neg at hc
    have h := digits_len_le_of_lt_pow _ _ hc
    omega
  have l3 : (10:ℕ) ^ ((Nat.digits 10 (n ^ 3)).length - 1) ≤ n ^ 3 := by
    by_contra hc
    push_neg at hc
    have h := digits_len_le_of_lt_pow _ _ hc
    omega
  have hlow : 2155 ≤ n := by
    by_contra hc
    push_neg at hc
    have h1 : n ^ 3 < 10 ^ 10 :=
      lt_of_le_of_lt (Nat.pow_le_pow_left (by omega : n ≤ 2154) 3) (by norm_num)
    have hB : (Nat.digits 10 (n ^ 3)).length ≤ 10 := digits_len_le_of_lt_pow _ _ h1
    have h2 : (10:ℕ) ^ 7 ≤ n ^ 2 :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) l2
    have h3 : n ^ 2 ≤ 2154 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : (2154:ℕ) ^ 2 < 10 ^ 7 := by norm_num
    exact absurd h2 (not_le.mpr (lt_of_le_of_lt h3 h4))
  have hup : n ≤ 3162 := by
    by_contra hc
    push_neg at hc
    have h1 : (10:ℕ) ^ 7 ≤ n ^ 2 :=
      le_trans (by norm_num) (Nat.pow_le_pow_left (by omega : 3163 ≤ n) 2)
    have hA : 8 ≤ (Nat.digits 10 (n ^ 2)).length := by
      by_contra hc2
      push_neg at hc2
      exact absurd h1 (not_le.mpr (lt_pow_of_digits_len_le 7 (n ^ 2) (by omega)))
    have h2 : n ^ 3 < 10 ^ 10 := lt_pow_of_digits_len_le 10 (n ^ 3) (by omega)
    have h3 : (10:ℕ) ^ 10 ≤ 2155 ^ 3 := by norm_num
    have h4 : (2155:ℕ) ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left (by omega) 3
    exact absurd h2 (not_lt.mpr (le_trans h3 h4))
  have hkey : dw 12 (n ^ 2) + dw 12 (n ^ 3) = 72638703667264 := by
    have e2 : dw 12 (n ^ 2) = ((Nat.digits 10 (n ^ 2)).map (fun d => 32 ^ d)).sum := by
      apply dw_eq
      calc n ^ 2 ≤ 3162 ^ 2 := Nat.pow_le_pow_left hup 2
        _ < 10 ^ 12 := by norm_num
    have e3 : dw 12 (n ^ 3) = ((Nat.digits 10 (n ^ 3)).map (fun d => 32 ^ d)).sum := by
      apply dw_eq
      calc n ^ 3 ≤ 3162 ^ 3 := Nat.pow_le_pow_left hup 3
        _ < 10 ^ 12 := by norm_num
    have h := (hp.map (fun d : ℕ => 32 ^ d)).sum_eq
    simp only [List.map_append, List.sum_append] at h
    rw [e2, e3, h]
    norm_num
  have main : ∀ m : ℕ, 2155 ≤ m → m ≤ 3162 →
      dw 12 (m ^ 2) + dw 12 (m ^ 3) ≠ 72638703667264 := by
    intro m h1 h2
    rcases Nat.lt_or_ge m 2407 with h | h
    · have h3 := rchk_spec 2155 252 (by decide) (m - 2155) (by omega)
      rwa [show 2155 + (m - 2155) = m from by omega] at h3
    · rcases Nat.lt_or_ge m 2659 with h' | h'
      · have h3 := rchk_spec 2407 252 (by decide) (m - 2407) (by omega)
        rwa [show 2407 + (m - 2407) = m from by omega] at h3
      · rcases Nat.lt_or_ge m 2911 with h'' | h''
        · have h3 := rchk_spec 2659 252 (by decide) (m - 2659) (by omega)
          rwa [show 2659 + (m - 2659) = m from by omega] at h3
        · have h3 := rchk_spec 2911 252 (by decide) (m - 2911) (by omega)
          rwa [show 2911 + (m - 2911) = m from by omega] at h3
  exact main n hlow hup hkey
```
