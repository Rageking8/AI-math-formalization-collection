# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `23 August 2026`\
Line count: `412`\
Turn count: `5`

## Solution

```lean4
import Mathlib

namespace Mode7

/-! ### §1. Infinitude from unboundedness -/

theorem infinite_of_unbounded {S : Set ℕ} (h : ∀ N : ℕ, ∃ n ∈ S, N < n) : S.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨n, hnS, hlt⟩ := h N
  exact absurd (hN hnS) (not_le.mpr hlt)

/-! ### §2. The predicate `Dom7` -/

def Dom7 (x : ℕ) : Prop :=
  ∀ d : ℕ, d ≠ 7 → (Nat.digits 10 x).count d < (Nat.digits 10 x).count 7

def S : Set ℕ := {n : ℕ | 0 < n ∧ Dom7 ((n - 4) ^ 2) ∧ Dom7 (n ^ 3 + 12)}

theorem count_eq_zero_of_ten_le {x d : ℕ} (hd : 10 ≤ d) :
    (Nat.digits 10 x).count d = 0 := by
  rw [List.count_eq_zero]
  intro hmem
  have := Nat.digits_lt_base (by norm_num) hmem
  omega

theorem dom7_of_forall_lt_ten {x : ℕ}
    (h : ∀ d < 10, d ≠ 7 → (Nat.digits 10 x).count d < (Nat.digits 10 x).count 7) :
    Dom7 x := by
  intro d hd
  by_cases hlt : d < 10
  · exact h d hlt hd
  · have h0 : (Nat.digits 10 x).count d = 0 := count_eq_zero_of_ten_le (by omega)
    have h7 : 0 < (Nat.digits 10 x).count 7 :=
      lt_of_le_of_lt (Nat.zero_le _) (h 0 (by norm_num) (by norm_num))
    omega

/-! ### §3. Digit concatenation

If `r` fills a block of exactly `k` digits and `a ≠ 0`, the expansion of `a * 10 ^ k + r`
is the expansion of `r` followed (little-endian) by that of `a`. -/

theorem digits_mul_pow_add :
    ∀ (k a r : ℕ), a ≠ 0 → (Nat.digits 10 r).length = k →
      Nat.digits 10 (a * 10 ^ k + r) = Nat.digits 10 r ++ Nat.digits 10 a := by
  intro k
  induction k with
  | zero =>
    intro a r _ hr
    have hnil : Nat.digits 10 r = [] := List.eq_nil_of_length_eq_zero hr
    have hr0 : r = 0 := Nat.digits_eq_nil_iff_eq_zero.mp hnil
    subst hr0; simp
  | succ k ih =>
    intro a r ha hr
    have hr0 : r ≠ 0 := by intro h; subst h; simp at hr
    have hdr : Nat.digits 10 r = r % 10 :: Nat.digits 10 (r / 10) :=
      Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hr0)
    have hlen : (Nat.digits 10 (r / 10)).length = k := by
      rw [hdr] at hr; simpa using hr
    have hx : a * 10 ^ (k + 1) + r = r + 10 * (a * 10 ^ k) := by ring
    have hpos : 0 < a * 10 ^ (k + 1) + r := by
      have h1 : 0 < a * 10 ^ (k + 1) :=
        Nat.mul_pos (Nat.pos_of_ne_zero ha) (pow_pos (by norm_num) _)
      omega
    have h1 : (a * 10 ^ (k + 1) + r) % 10 = r % 10 := by
      rw [hx, Nat.add_mul_mod_self_left]
    have h2 : (a * 10 ^ (k + 1) + r) / 10 = a * 10 ^ k + r / 10 := by
      rw [hx, Nat.add_mul_div_left _ _ (by norm_num : 0 < 10), Nat.add_comm]
    rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 10) hpos, h1, h2,
      ih a (r / 10) ha hlen, hdr]
    rfl

/-! ### §4. Repeated blocks -/

/-- `rep A L t` : the block `A`, written in an `L`-digit slot, repeated `t` times. -/
def rep (A L : ℕ) : ℕ → ℕ
  | 0 => 0
  | (t + 1) => A * 10 ^ (L * t) + rep A L t

theorem rep_zero (A L : ℕ) : rep A L 0 = 0 := rfl
theorem rep_succ (A L t : ℕ) : rep A L (t + 1) = A * 10 ^ (L * t) + rep A L t := rfl

theorem rep_ne_zero {A L t : ℕ} (hA : A ≠ 0) (ht : t ≠ 0) : rep A L t ≠ 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
  rw [rep_succ]
  have : 0 < A * 10 ^ (L * s) :=
    Nat.mul_pos (Nat.pos_of_ne_zero hA) (pow_pos (by norm_num) _)
  omega

theorem rep_len {A L : ℕ} (hA : A ≠ 0) (hAL : (Nat.digits 10 A).length = L) :
    ∀ t, (Nat.digits 10 (rep A L t)).length = L * t := by
  intro t
  induction t with
  | zero => simp [rep_zero]
  | succ t ih =>
    rw [rep_succ, digits_mul_pow_add (L * t) A (rep A L t) hA ih,
      List.length_append, ih, hAL, Nat.mul_succ]

theorem rep_digits {A L : ℕ} (hA : A ≠ 0) (hAL : (Nat.digits 10 A).length = L) (t : ℕ) :
    Nat.digits 10 (rep A L (t + 1))
      = Nat.digits 10 (rep A L t) ++ Nat.digits 10 A := by
  rw [rep_succ, digits_mul_pow_add (L * t) A (rep A L t) hA (rep_len hA hAL t)]

theorem rep_count {A L : ℕ} (hA : A ≠ 0) (hAL : (Nat.digits 10 A).length = L) (d : ℕ) :
    ∀ t, (Nat.digits 10 (rep A L t)).count d = t * (Nat.digits 10 A).count d := by
  intro t
  induction t with
  | zero => simp [rep_zero]
  | succ t ih => rw [rep_digits hA hAL t, List.count_append, ih, Nat.succ_mul]

theorem rep_eq_mul (A L : ℕ) : ∀ t, rep A L t = A * rep 1 L t := by
  intro t
  induction t with
  | zero => simp [rep_zero]
  | succ t ih => rw [rep_succ, rep_succ, ih]; ring

theorem nine_rep1 : ∀ t, 9 * rep 1 1 t + 1 = 10 ^ t := by
  intro t
  induction t with
  | zero => simp [rep_zero]
  | succ t ih =>
    rw [rep_succ, one_mul, one_mul, pow_succ]
    omega

theorem nine99_rep3 : ∀ p, 999 * rep 1 3 p + 1 = 1000 ^ p := by
  intro p
  induction p with
  | zero => simp [rep_zero]
  | succ p ih =>
    have h : (10 : ℕ) ^ (3 * p) = 1000 ^ p := by rw [pow_mul]; norm_num
    rw [rep_succ, one_mul, h, pow_succ]
    omega

/-! ### §5. The family  `n_p = 19 33…3 19`  (with `3(p+2)` threes)

`n_p = 1931400000000 * u p + 1933333319`, where `u p = 1 + 1000 + … + 1000^(p-1)`.
Both `(n_p - 4)^2` and `n_p^3 + 12` are then polynomials in `u p`, and their decimal
expansions are exactly periodic — no digit needs to be "forced". -/

def u (p : ℕ) : ℕ := rep 1 3 p
theorem u_def (p : ℕ) : u p = rep 1 3 p := rfl

def N (p : ℕ) : ℕ := 1931400000000 * u p + 1933333319

theorem pow3 (p : ℕ) : (10 : ℕ) ^ (3 * p) = 999 * u p + 1 := by
  rw [pow_mul]; norm_num; exact (nine99_rep3 p).symm

theorem pow_split (c p : ℕ) : (10 : ℕ) ^ (3 * p + c) = 10 ^ c * (999 * u p + 1) := by
  rw [pow_add, pow3]; ring

theorem pow_split2 (c p : ℕ) : (10 : ℕ) ^ (6 * p + c) = 10 ^ c * (999 * u p + 1) ^ 2 := by
  have h : 6 * p + c = 3 * p + (3 * p + c) := by ring
  rw [h, pow_add, pow_split, pow3]; ring

theorem pow_split3 (c p : ℕ) : (10 : ℕ) ^ (9 * p + c) = 10 ^ c * (999 * u p + 1) ^ 3 := by
  have h : 9 * p + c = 3 * p + (6 * p + c) := by ring
  rw [h, pow_add, pow_split2, pow3]; ring

theorem rep7_val (p : ℕ) : rep 7 1 (3 * p + 4) = 7 * (1110000 * u p + 1111) := by
  rw [rep_eq_mul]
  have h := nine_rep1 (3 * p + 4)
  rw [pow_split 4 p] at h
  norm_num at h
  omega

theorem rep8_val (p : ℕ) : rep 8 1 (3 * p + 5) = 8 * (11100000 * u p + 11111) := by
  rw [rep_eq_mul]
  have h := nine_rep1 (3 * p + 5)
  rw [pow_split 5 p] at h
  norm_num at h
  omega

theorem rep370_succ (p : ℕ) : rep 370 3 (p + 1) = 370 * (1000 * u p + 1) := by
  rw [rep_eq_mul 370, rep_succ, one_mul, pow3, ← u_def]; ring

theorem rep592_succ (p : ℕ) : rep 592 3 (p + 1) = 592 * (1000 * u p + 1) := by
  rw [rep_eq_mul 592, rep_succ, one_mul, pow3, ← u_def]; ring

theorem rep370_val (p : ℕ) : rep 370 3 p = 370 * u p := by
  rw [rep_eq_mul 370, ← u_def]

/-- The decimal shape of `(n_p - 4)^2` :  `373 7…7 706 8…8 9225`. -/
def Sq (p : ℕ) : ℕ :=
  373 * 10 ^ (6 * p + 16) +
    (rep 7 1 (3 * p + 4) * 10 ^ (3 * p + 12) +
      (706 * 10 ^ (3 * p + 9) + (rep 8 1 (3 * p + 5) * 10 ^ 4 + 9225)))

/-- The decimal shape of `n_p ^ 3 + 12` :
`7226 (370)…(370) 20964 (592)…(592) 711750 (370)…(370) 3700771`. -/
def Cu (p : ℕ) : ℕ :=
  7226 * 10 ^ (9 * p + 24) +
    (rep 370 3 (p + 1) * 10 ^ (6 * p + 21) +
      (20964 * 10 ^ (6 * p + 16) +
        (rep 592 3 (p + 1) * 10 ^ (3 * p + 13) +
          (711750 * 10 ^ (3 * p + 7) + (rep 370 3 p * 10 ^ 7 + 3700771)))))

theorem N_sub_four (p : ℕ) : N p - 4 = 1931400000000 * u p + 1933333315 := by
  simp only [N]; omega

/-- **Exact identity for the square.** -/
theorem sq_eq (p : ℕ) : (N p - 4) ^ 2 = Sq p := by
  rw [N_sub_four, Sq, rep7_val, rep8_val, pow_split2 16, pow_split 12, pow_split 9]
  ring

/-- **Exact identity for the cube.** -/
theorem cu_eq (p : ℕ) : N p ^ 3 + 12 = Cu p := by
  rw [N, Cu, rep370_succ, rep592_succ, rep370_val, pow_split3 24, pow_split2 21,
    pow_split2 16, pow_split 13, pow_split 7]
  ring

/-! ### §6. Digit expansions of `Sq` and `Cu` -/

theorem d7' : Nat.digits 10 7 = [7] := by norm_num
theorem d8' : Nat.digits 10 8 = [8] := by norm_num
theorem d370 : Nat.digits 10 370 = [0, 7, 3] := by norm_num
theorem d592 : Nat.digits 10 592 = [2, 9, 5] := by norm_num
theorem l7' : (Nat.digits 10 7).length = 1 := by simp [d7']
theorem l8' : (Nat.digits 10 8).length = 1 := by simp [d8']
theorem l370 : (Nat.digits 10 370).length = 3 := by simp [d370]
theorem l592 : (Nat.digits 10 592).length = 3 := by simp [d592]

theorem digits_Sq (p : ℕ) :
    Nat.digits 10 (Sq p)
      = ((([5, 2, 2, 9] ++ Nat.digits 10 (rep 8 1 (3 * p + 5))) ++ [6, 0, 7])
          ++ Nat.digits 10 (rep 7 1 (3 * p + 4))) ++ [3, 7, 3] := by
  have e9225 : Nat.digits 10 9225 = [5, 2, 2, 9] := by norm_num
  have e706 : Nat.digits 10 706 = [6, 0, 7] := by norm_num
  have e373 : Nat.digits 10 373 = [3, 7, 3] := by norm_num
  have l0 : (Nat.digits 10 9225).length = 4 := by simp [e9225]
  have h8 : rep 8 1 (3 * p + 5) ≠ 0 := rep_ne_zero (by norm_num) (by omega)
  have h7 : rep 7 1 (3 * p + 4) ≠ 0 := rep_ne_zero (by norm_num) (by omega)
  have e1 : Nat.digits 10 (rep 8 1 (3 * p + 5) * 10 ^ 4 + 9225)
      = [5, 2, 2, 9] ++ Nat.digits 10 (rep 8 1 (3 * p + 5)) := by
    rw [digits_mul_pow_add 4 _ 9225 h8 l0, e9225]
  have l1 : (Nat.digits 10 (rep 8 1 (3 * p + 5) * 10 ^ 4 + 9225)).length = 3 * p + 9 := by
    rw [e1, List.length_append, rep_len (by norm_num) l8']
    simp; omega
  have e2 : Nat.digits 10 (706 * 10 ^ (3 * p + 9) + (rep 8 1 (3 * p + 5) * 10 ^ 4 + 9225))
      = ([5, 2, 2, 9] ++ Nat.digits 10 (rep 8 1 (3 * p + 5))) ++ [6, 0, 7] := by
    rw [digits_mul_pow_add (3 * p + 9) 706 _ (by norm_num) l1, e1, e706]
  have l2 : (Nat.digits 10
      (706 * 10 ^ (3 * p + 9) + (rep 8 1 (3 * p + 5) * 10 ^ 4 + 9225))).length
        = 3 * p + 12 := by
    rw [e2, List.length_append, List.length_append, rep_len (by norm_num) l8']
    simp; omega
  have e3 : Nat.digits 10 (rep 7 1 (3 * p + 4) * 10 ^ (3 * p + 12) +
      (706 * 10 ^ (3 * p + 9) + (rep 8 1 (3 * p + 5) * 10 ^ 4 + 9225)))
      = (([5, 2, 2, 9] ++ Nat.digits 10 (rep 8 1 (3 * p + 5))) ++ [6, 0, 7])
          ++ Nat.digits 10 (rep 7 1 (3 * p + 4)) := by
    rw [digits_mul_pow_add (3 * p + 12) _ _ h7 l2, e2]
  have l3 : (Nat.digits 10 (rep 7 1 (3 * p + 4) * 10 ^ (3 * p + 12) +
      (706 * 10 ^ (3 * p + 9) + (rep 8 1 (3 * p + 5) * 10 ^ 4 + 9225)))).length
        = 6 * p + 16 := by
    rw [e3, List.length_append, List.length_append, List.length_append,
      rep_len (by norm_num) l8', rep_len (by norm_num) l7']
    simp; omega
  rw [Sq, digits_mul_pow_add (6 * p + 16) 373 _ (by norm_num) l3, e3, e373]

theorem digits_Cu (p : ℕ) (hp : p ≠ 0) :
    Nat.digits 10 (Cu p)
      = ((((([1, 7, 7, 0, 0, 7, 3] ++ Nat.digits 10 (rep 370 3 p)) ++ [0, 5, 7, 1, 1, 7])
          ++ Nat.digits 10 (rep 592 3 (p + 1))) ++ [4, 6, 9, 0, 2])
          ++ Nat.digits 10 (rep 370 3 (p + 1))) ++ [6, 2, 2, 7] := by
  have e0 : Nat.digits 10 3700771 = [1, 7, 7, 0, 0, 7, 3] := by norm_num
  have e711 : Nat.digits 10 711750 = [0, 5, 7, 1, 1, 7] := by norm_num
  have e209 : Nat.digits 10 20964 = [4, 6, 9, 0, 2] := by norm_num
  have e7226 : Nat.digits 10 7226 = [6, 2, 2, 7] := by norm_num
  have l0 : (Nat.digits 10 3700771).length = 7 := by simp [e0]
  have hA : rep 370 3 p ≠ 0 := rep_ne_zero (by norm_num) hp
  have hB : rep 592 3 (p + 1) ≠ 0 := rep_ne_zero (by norm_num) (by omega)
  have hC : rep 370 3 (p + 1) ≠ 0 := rep_ne_zero (by norm_num) (by omega)
  have e1 : Nat.digits 10 (rep 370 3 p * 10 ^ 7 + 3700771)
      = [1, 7, 7, 0, 0, 7, 3] ++ Nat.digits 10 (rep 370 3 p) := by
    rw [digits_mul_pow_add 7 _ 3700771 hA l0, e0]
  have l1 : (Nat.digits 10 (rep 370 3 p * 10 ^ 7 + 3700771)).length = 3 * p + 7 := by
    rw [e1, List.length_append, rep_len (by norm_num) l370]; simp; omega
  have e2 : Nat.digits 10 (711750 * 10 ^ (3 * p + 7) + (rep 370 3 p * 10 ^ 7 + 3700771))
      = ([1, 7, 7, 0, 0, 7, 3] ++ Nat.digits 10 (rep 370 3 p)) ++ [0, 5, 7, 1, 1, 7] := by
    rw [digits_mul_pow_add (3 * p + 7) 711750 _ (by norm_num) l1, e1, e711]
  have l2 : (Nat.digits 10
      (711750 * 10 ^ (3 * p + 7) + (rep 370 3 p * 10 ^ 7 + 3700771))).length
        = 3 * p + 13 := by
    rw [e2, List.length_append, List.length_append, rep_len (by norm_num) l370]
    simp; omega
  have e3 : Nat.digits 10 (rep 592 3 (p + 1) * 10 ^ (3 * p + 13) +
      (711750 * 10 ^ (3 * p + 7) + (rep 370 3 p * 10 ^ 7 + 3700771)))
      = (([1, 7, 7, 0, 0, 7, 3] ++ Nat.digits 10 (rep 370 3 p)) ++ [0, 5, 7, 1, 1, 7])
          ++ Nat.digits 10 (rep 592 3 (p + 1)) := by
    rw [digits_mul_pow_add (3 * p + 13) _ _ hB l2, e2]
  have l3 : (Nat.digits 10 (rep 592 3 (p + 1) * 10 ^ (3 * p + 13) +
      (711750 * 10 ^ (3 * p + 7) + (rep 370 3 p * 10 ^ 7 + 3700771)))).length
        = 6 * p + 16 := by
    rw [e3, List.length_append, List.length_append, List.length_append,
      rep_len (by norm_num) l370, rep_len (by norm_num) l592]
    simp; omega
  have e4 : Nat.digits 10 (20964 * 10 ^ (6 * p + 16) +
      (rep 592 3 (p + 1) * 10 ^ (3 * p + 13) +
        (711750 * 10 ^ (3 * p + 7) + (rep 370 3 p * 10 ^ 7 + 3700771))))
      = ((([1, 7, 7, 0, 0, 7, 3] ++ Nat.digits 10 (rep 370 3 p)) ++ [0, 5, 7, 1, 1, 7])
          ++ Nat.digits 10 (rep 592 3 (p + 1))) ++ [4, 6, 9, 0, 2] := by
    rw [digits_mul_pow_add (6 * p + 16) 20964 _ (by norm_num) l3, e3, e209]
  have l4 : (Nat.digits 10 (20964 * 10 ^ (6 * p + 16) +
      (rep 592 3 (p + 1) * 10 ^ (3 * p + 13) +
        (711750 * 10 ^ (3 * p + 7) + (rep 370 3 p * 10 ^ 7 + 3700771))))).length
        = 6 * p + 21 := by
    rw [e4]
    simp only [List.length_append, rep_len (by norm_num) l370,
      rep_len (by norm_num) l592]
    simp; omega
  have e5 : Nat.digits 10 (rep 370 3 (p + 1) * 10 ^ (6 * p + 21) +
      (20964 * 10 ^ (6 * p + 16) +
        (rep 592 3 (p + 1) * 10 ^ (3 * p + 13) +
          (711750 * 10 ^ (3 * p + 7) + (rep 370 3 p * 10 ^ 7 + 3700771)))))
      = (((([1, 7, 7, 0, 0, 7, 3] ++ Nat.digits 10 (rep 370 3 p)) ++ [0, 5, 7, 1, 1, 7])
          ++ Nat.digits 10 (rep 592 3 (p + 1))) ++ [4, 6, 9, 0, 2])
          ++ Nat.digits 10 (rep 370 3 (p + 1)) := by
    rw [digits_mul_pow_add (6 * p + 21) _ _ hC l4, e4]
  have l5 : (Nat.digits 10 (rep 370 3 (p + 1) * 10 ^ (6 * p + 21) +
      (20964 * 10 ^ (6 * p + 16) +
        (rep 592 3 (p + 1) * 10 ^ (3 * p + 13) +
          (711750 * 10 ^ (3 * p + 7) + (rep 370 3 p * 10 ^ 7 + 3700771)))))).length
        = 9 * p + 24 := by
    rw [e5]
    simp only [List.length_append, rep_len (by norm_num) l370,
      rep_len (by norm_num) l592]
    simp; omega
  rw [Cu, digits_mul_pow_add (9 * p + 24) 7226 _ (by norm_num) l5, e5, e7226]

/-! ### §7. Digit counts, and 7-dominance -/

theorem count_Sq (p d : ℕ) :
    (Nat.digits 10 (Sq p)).count d
      = ([5, 2, 2, 9] : List ℕ).count d + (3 * p + 5) * ([8] : List ℕ).count d
        + ([6, 0, 7] : List ℕ).count d + (3 * p + 4) * ([7] : List ℕ).count d
        + ([3, 7, 3] : List ℕ).count d := by
  rw [digits_Sq p]
  simp only [List.count_append, rep_count (by norm_num) l8' d,
    rep_count (by norm_num) l7' d, d8', d7']

theorem count_Cu (p d : ℕ) (hp : p ≠ 0) :
    (Nat.digits 10 (Cu p)).count d
      = ([1, 7, 7, 0, 0, 7, 3] : List ℕ).count d + p * ([0, 7, 3] : List ℕ).count d
        + ([0, 5, 7, 1, 1, 7] : List ℕ).count d + (p + 1) * ([2, 9, 5] : List ℕ).count d
        + ([4, 6, 9, 0, 2] : List ℕ).count d + (p + 1) * ([0, 7, 3] : List ℕ).count d
        + ([6, 2, 2, 7] : List ℕ).count d := by
  rw [digits_Cu p hp]
  simp only [List.count_append, rep_count (by norm_num) l370 d,
    rep_count (by norm_num) l592 d, d370, d592]

theorem count7_Sq (p : ℕ) : (Nat.digits 10 (Sq p)).count 7 = 3 * p + 6 := by
  have h := count_Sq p 7; norm_num at h; omega

theorem count_le_Sq (p d : ℕ) (hd : d < 10) (hne : d ≠ 7) :
    (Nat.digits 10 (Sq p)).count d ≤ 3 * p + 5 := by
  have h := count_Sq p d
  interval_cases d <;> simp_all <;> omega

theorem count7_Cu (p : ℕ) (hp : p ≠ 0) : (Nat.digits 10 (Cu p)).count 7 = 2 * p + 7 := by
  have h := count_Cu p 7 hp; norm_num at h; omega

theorem count_le_Cu (p d : ℕ) (hp : p ≠ 0) (hd : d < 10) (hne : d ≠ 7) :
    (Nat.digits 10 (Cu p)).count d ≤ 2 * p + 5 := by
  have h := count_Cu p d hp
  interval_cases d <;> simp_all <;> omega

theorem dom7_Sq (p : ℕ) : Dom7 (Sq p) := by
  apply dom7_of_forall_lt_ten
  intro d hd hne
  rw [count7_Sq]
  have := count_le_Sq p d hd hne
  omega

theorem dom7_Cu (p : ℕ) (hp : p ≠ 0) : Dom7 (Cu p) := by
  apply dom7_of_forall_lt_ten
  intro d hd hne
  rw [count7_Cu p hp]
  have := count_le_Cu p d hp hd hne
  omega

/-! ### §8. Conclusion -/

theorem mem_S (p : ℕ) : N (p + 1) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [N]; omega
  · rw [sq_eq]; exact dom7_Sq (p + 1)
  · rw [cu_eq]; exact dom7_Cu (p + 1) (Nat.succ_ne_zero p)

theorem le_u (p : ℕ) : p ≤ u p := by
  induction p with
  | zero => simp [u, rep_zero]
  | succ p ih =>
    have h1 : (1 : ℕ) ≤ 10 ^ (3 * p) := Nat.one_le_pow _ _ (by norm_num)
    simp only [u, rep_succ, one_mul] at *
    omega

theorem infinite_S : S.Infinite := by
  apply infinite_of_unbounded
  intro M
  refine ⟨N (M + 1), mem_S M, ?_⟩
  have h1 : M + 1 ≤ u (M + 1) := le_u (M + 1)
  simp only [N]
  omega

end Mode7

theorem infinite_positive_integers_mode_digit_seven :
    Set.Infinite { n : ℕ | 0 < n ∧
      (∀ d : ℕ, d ≠ 7 → (Nat.digits 10 ((n - 4) ^ 2)).count d <
      (Nat.digits 10 ((n - 4) ^ 2)).count 7) ∧
      (∀ d : ℕ, d ≠ 7 → (Nat.digits 10 (n ^ 3 + 12)).count d <
      (Nat.digits 10 (n ^ 3 + 12)).count 7) } :=
  Mode7.infinite_S
```
