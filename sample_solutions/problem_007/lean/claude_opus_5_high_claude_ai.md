# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `29 July 2026`\
Line count: `121`\
Turn count: `1`

## Solution

```lean4
import Mathlib

/-- Recursive description of the digit sum (valid also at `0`). -/
private lemma aux_sum_digits_rec (n : ℕ) :
    (Nat.digits 10 n).sum = n % 10 + (Nat.digits 10 (n / 10)).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · rw [Nat.digits_def' (by norm_num : (1:ℕ) < 10) h]
    simp

/-- Subadditivity, proved by induction on a bound for `m + n`. -/
private lemma aux_add_le : ∀ N m n : ℕ, m + n ≤ N →
    (Nat.digits 10 (m + n)).sum ≤ (Nat.digits 10 m).sum + (Nat.digits 10 n).sum := by
  intro N
  induction N with
  | zero =>
    intro m n h
    have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    subst hm; subst hn; simp
  | succ N ih =>
    intro m n h
    rcases Nat.eq_zero_or_pos (m + n) with h0 | h0
    · have hm : m = 0 := by omega
      have hn : n = 0 := by omega
      subst hm; subst hn; simp
    · obtain ⟨c, hc1, hdiv, hmod⟩ :
        ∃ c : ℕ, c ≤ 1 ∧ (m + n) / 10 = m / 10 + n / 10 + c ∧
          m % 10 + n % 10 = (m + n) % 10 + 10 * c :=
        ⟨(m % 10 + n % 10) / 10, by omega, by omega, by omega⟩
      have hle1 : m / 10 + n / 10 + c ≤ N := by omega
      have hle2 : m / 10 + n / 10 ≤ N := by omega
      have h1 := ih (m / 10 + n / 10) c hle1
      have h2 := ih (m / 10) (n / 10) hle2
      have h3 : (Nat.digits 10 c).sum ≤ c := by
        have h10 : c / 10 = 0 := by omega
        have h4 := aux_sum_digits_rec c
        rw [h10, Nat.digits_zero, List.sum_nil] at h4
        omega
      rw [aux_sum_digits_rec (m + n), aux_sum_digits_rec m, aux_sum_digits_rec n, hdiv]
      omega

private lemma aux_sum_digits_add_le (m n : ℕ) :
    (Nat.digits 10 (m + n)).sum ≤ (Nat.digits 10 m).sum + (Nat.digits 10 n).sum :=
  aux_add_le (m + n) m n le_rfl

private lemma aux_ten_mul (k : ℕ) :
    (Nat.digits 10 (10 * k)).sum = (Nat.digits 10 k).sum := by
  have h := aux_sum_digits_rec (10 * k)
  have e1 : 10 * k % 10 = 0 := by omega
  have e2 : 10 * k / 10 = k := by omega
  rw [e1, e2] at h
  omega

private lemma aux_mul_nat (m : ℕ) : ∀ d : ℕ,
    (Nat.digits 10 (m * d)).sum ≤ d * (Nat.digits 10 m).sum := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    calc (Nat.digits 10 (m * (d + 1))).sum
        = (Nat.digits 10 (m * d + m)).sum := by
          rw [show m * (d + 1) = m * d + m from by ring]
      _ ≤ (Nat.digits 10 (m * d)).sum + (Nat.digits 10 m).sum := aux_sum_digits_add_le _ _
      _ ≤ d * (Nat.digits 10 m).sum + (Nat.digits 10 m).sum := Nat.add_le_add_right ih _
      _ = (d + 1) * (Nat.digits 10 m).sum := by ring

private lemma aux_mul_le : ∀ N m n : ℕ, n ≤ N →
    (Nat.digits 10 (m * n)).sum ≤ (Nat.digits 10 m).sum * (Nat.digits 10 n).sum := by
  intro N
  induction N with
  | zero =>
    intro m n h
    have hn : n = 0 := by omega
    subst hn; simp
  | succ N ih =>
    intro m n h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hsplit : m * n = 10 * (m * (n / 10)) + m * (n % 10) := by
        have hn10 : n = 10 * (n / 10) + n % 10 := by omega
        calc m * n = m * (10 * (n / 10) + n % 10) := by rw [← hn10]
          _ = 10 * (m * (n / 10)) + m * (n % 10) := by ring
      have hlt : n / 10 ≤ N := by omega
      have h1 : (Nat.digits 10 (m * n)).sum
          ≤ (Nat.digits 10 (10 * (m * (n / 10)))).sum
            + (Nat.digits 10 (m * (n % 10))).sum := by
        rw [hsplit]; exact aux_sum_digits_add_le _ _
      have h2 := aux_ten_mul (m * (n / 10))
      have h3 := ih m (n / 10) hlt
      have h4 := aux_mul_nat m (n % 10)
      have h5 := aux_sum_digits_rec n
      calc (Nat.digits 10 (m * n)).sum
          ≤ (Nat.digits 10 (10 * (m * (n / 10)))).sum
            + (Nat.digits 10 (m * (n % 10))).sum := h1
        _ = (Nat.digits 10 (m * (n / 10))).sum
            + (Nat.digits 10 (m * (n % 10))).sum := by rw [h2]
        _ ≤ (Nat.digits 10 m).sum * (Nat.digits 10 (n / 10)).sum
            + (n % 10) * (Nat.digits 10 m).sum := Nat.add_le_add h3 h4
        _ = (Nat.digits 10 m).sum * (n % 10 + (Nat.digits 10 (n / 10)).sum) := by ring
        _ = (Nat.digits 10 m).sum * (Nat.digits 10 n).sum := by rw [← h5]

private lemma aux_sum_digits_mul_le (m n : ℕ) :
    (Nat.digits 10 (m * n)).sum ≤ (Nat.digits 10 m).sum * (Nat.digits 10 n).sum :=
  aux_mul_le n m n le_rfl

theorem digit_sum_pow_le (n x : ℕ) (hn : 0 < n) (hx : 0 < x) :
    (Nat.digits 10 (n ^ x)).sum ≤ ((Nat.digits 10 n).sum) ^ x := by
  clear hx hn
  induction x with
  | zero =>
    have h := aux_sum_digits_rec 1
    rw [show (1:ℕ) / 10 = 0 from by norm_num, Nat.digits_zero, List.sum_nil] at h
    simp only [pow_zero]
    omega
  | succ k ih =>
    calc (Nat.digits 10 (n ^ (k + 1))).sum
        = (Nat.digits 10 (n ^ k * n)).sum := by rw [pow_succ]
      _ ≤ (Nat.digits 10 (n ^ k)).sum * (Nat.digits 10 n).sum := aux_sum_digits_mul_le _ _
      _ ≤ (Nat.digits 10 n).sum ^ k * (Nat.digits 10 n).sum := Nat.mul_le_mul ih (le_refl _)
      _ = (Nat.digits 10 n).sum ^ (k + 1) := by rw [pow_succ]
```
