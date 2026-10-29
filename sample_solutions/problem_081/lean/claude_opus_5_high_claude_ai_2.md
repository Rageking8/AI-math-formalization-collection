# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `26 August 2026`\
Line count: `95`\
Turn count: `1`

## Note

The solution is more verbose as the model is explicitly told not to use `native_decide`.

## Solution

```lean4
import Mathlib

def O (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).filter (· % 2 == 1)).length

def E (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).filter (· % 2 == 0)).length

/-- Kernel-computable version of `Nat.digits 10`, with fuel. -/
def digAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else n % 10 :: digAux f (n / 10)

theorem digAux_eq : ∀ (f n : ℕ), n < 10 ^ f → digAux f n = Nat.digits 10 n := by
  intro f
  induction f with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by simpa using hn
    subst hn0
    simp [digAux]
  | succ f ih =>
    intro n hn
    rw [pow_succ] at hn
    by_cases h0 : n = 0
    · subst h0
      simp [digAux]
    · have hpos : 0 < n := Nat.pos_of_ne_zero h0
      have hlt : n / 10 < 10 ^ f := by omega
      have hstep : digAux (f + 1) n = n % 10 :: digAux f (n / 10) := by
        simp only [digAux]
        exact if_neg h0
      rw [hstep, ih _ hlt, Nat.digits_def' (by norm_num : (1:ℕ) < 10) hpos]

def O' (n : ℕ) : ℕ := ((digAux 8 n).filter (· % 2 == 1)).length
def E' (n : ℕ) : ℕ := ((digAux 8 n).filter (· % 2 == 0)).length

theorem O_eq {n : ℕ} (h : n < 10 ^ 8) : O n = O' n := by
  simp only [O, O', digAux_eq 8 n h]

theorem E_eq {n : ℕ} (h : n < 10 ^ 8) : E n = E' n := by
  simp only [E, E', digAux_eq 8 n h]

def bad (n : ℕ) : Bool :=
  (n != 0) && (O' (n * n + n) * O' (n * n + n) == 3 * O' n) &&
    (E' (n * n - n) == 5 * E' n)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000 in
theorem brute : ((List.range 1059).all fun n => !bad n) = true := by decide

theorem is_least_pos_int_odd_even_digit_count_eq_1059 :
    IsLeast { n : ℕ | 0 < n ∧ (O (n ^ 2 + n)) ^ 2 =
      3 * O n ∧ E (n ^ 2 - n) = 5 * E n } 1059 := by
  constructor
  · show 0 < 1059 ∧ (O (1059 ^ 2 + 1059)) ^ 2 = 3 * O 1059 ∧
      E (1059 ^ 2 - 1059) = 5 * E 1059
    refine ⟨by norm_num, ?_, ?_⟩
    · have hA : O 1122540 = 3 := by
        rw [O_eq (by norm_num : (1122540 : ℕ) < 10 ^ 8)]; decide
      have hB : O 1059 = 3 := by
        rw [O_eq (by norm_num : (1059 : ℕ) < 10 ^ 8)]; decide
      norm_num [hA, hB]
    · have hC : E 1120422 = 5 := by
        rw [E_eq (by norm_num : (1120422 : ℕ) < 10 ^ 8)]; decide
      have hD : E 1059 = 1 := by
        rw [E_eq (by norm_num : (1059 : ℕ) < 10 ^ 8)]; decide
      norm_num [hC, hD]
  · intro n hmem
    obtain ⟨hn, h1, h2⟩ := hmem
    by_contra hcon
    push_neg at hcon
    have hn1 : n ≤ 1058 := by omega
    have hsq : n * n ≤ 1058 * 1058 := Nat.mul_le_mul hn1 hn1
    have hb0 : n < 10 ^ 8 := lt_of_le_of_lt hn1 (by norm_num)
    have hb1 : n * n + n < 10 ^ 8 :=
      lt_of_le_of_lt (Nat.add_le_add hsq hn1) (by norm_num)
    have hb2 : n * n - n < 10 ^ 8 :=
      lt_of_le_of_lt (le_trans (Nat.sub_le _ _) hsq) (by norm_num)
    have hrw : n ^ 2 = n * n := by ring
    rw [hrw] at h1 h2
    have hrw2 : ∀ m : ℕ, m ^ 2 = m * m := fun m => by ring
    rw [hrw2] at h1
    rw [O_eq hb1, O_eq hb0] at h1
    rw [E_eq hb2, E_eq hb0] at h2
    have hz : (n != 0) = true := by simp [hn.ne']
    have hbad : bad n = true := by
      unfold bad
      rw [h1, h2, hz]
      simp
    have hb := brute
    simp only [List.all_eq_true, List.mem_range] at hb
    have hcontra := hb n hcon
    rw [hbad] at hcontra
    simp at hcontra
```
