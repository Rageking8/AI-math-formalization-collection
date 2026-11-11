# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `10 November 2026`\
Line count: `152`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem ds_rec (n : ℕ) :
    (Nat.digits 10 n).sum = n % 10 + (Nat.digits 10 (n / 10)).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · rw [Nat.digits_def' (by norm_num) h, List.sum_cons]

theorem ds_lt (n : ℕ) (hn : 10 ≤ n) : (Nat.digits 10 n).sum < n := by
  rw [ds_rec]
  have := Nat.digit_sum_le 10 (n / 10)
  omega

def additivePersistence (n : ℕ) : ℕ :=
  if n < 10 then 0
  else 1 + additivePersistence (Nat.digits 10 n).sum
termination_by n
decreasing_by exact ds_lt n (by omega)

theorem ap_small (x : ℕ) (hx : x < 10) : additivePersistence x = 0 := by
  rw [additivePersistence]
  split_ifs
  rfl

theorem ap_large (x : ℕ) (hx : 10 ≤ x) :
    additivePersistence x = 1 + additivePersistence (Nat.digits 10 x).sum := by
  conv_lhs => rw [additivePersistence]
  split_ifs with h
  · omega
  · rfl

theorem ds_add (a : ℕ) : ∀ (m i : ℕ), i < 10 ^ m →
    (Nat.digits 10 (a * 10 ^ m + i)).sum = (Nat.digits 10 a).sum + (Nat.digits 10 i).sum := by
  intro m
  induction m with
  | zero =>
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simp
  | succ m ih =>
    intro i hi
    have e : a * 10 ^ (m + 1) = 10 * (a * 10 ^ m) := by ring
    have e2 : 10 ^ (m + 1) = 10 * 10 ^ m := by ring
    rw [e2] at hi
    rw [ds_rec (a * 10 ^ (m + 1) + i), ds_rec i, e]
    have h1 : (10 * (a * 10 ^ m) + i) % 10 = i % 10 := by omega
    have h2 : (10 * (a * 10 ^ m) + i) / 10 = a * 10 ^ m + i / 10 := by omega
    rw [h1, h2, ih (i / 10) (by omega)]
    ring

theorem ds_le : ∀ (m i : ℕ), i < 10 ^ m → (Nat.digits 10 i).sum ≤ 9 * m := by
  intro m
  induction m with
  | zero =>
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simp
  | succ m ih =>
    intro i hi
    have e2 : 10 ^ (m + 1) = 10 * 10 ^ m := by ring
    rw [e2] at hi
    rw [ds_rec]
    have := ih (i / 10) (by omega)
    omega

theorem ds_exists (n : ℕ) : ∃ P, (Nat.digits 10 P).sum = n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨10 * P + 1, ?_⟩
    rw [ds_rec, show (10 * P + 1) % 10 = 1 by omega,
      show (10 * P + 1) / 10 = P by omega, hP]
    omega

theorem ap_step (t m k : ℕ) (hm : 1 ≤ m)
    (hQ : ∃ n, 1 ≤ n ∧ ∀ j < t, additivePersistence (n + j) = additivePersistence n)
    (hk : ∀ i < k, i < 10 ^ m ∧ (Nat.digits 10 i).sum < t) :
    ∃ n, 1 ≤ n ∧ ∀ i < k, additivePersistence (n + i) = additivePersistence n := by
  obtain ⟨n', _, h⟩ := hQ
  obtain ⟨P, hP⟩ := ds_exists n'
  have hPpos : 1 ≤ P := by
    rcases Nat.eq_zero_or_pos P with h0 | h0
    · subst h0
      have : n' = 0 := by simpa using hP.symm
      omega
    · exact h0
  have h10 : 10 ≤ P * 10 ^ m := by
    have h1 : 10 ^ 1 ≤ 10 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    calc 10 = 1 * 10 ^ 1 := by norm_num
      _ ≤ P * 10 ^ m := Nat.mul_le_mul hPpos h1
  have e0 : (Nat.digits 10 (P * 10 ^ m)).sum = n' := by
    have h0 := ds_add P m 0 (by positivity)
    rw [Nat.add_zero] at h0
    rw [h0, hP]
    simp
  refine ⟨P * 10 ^ m, by omega, ?_⟩
  intro i hi
  obtain ⟨hi1, hi2⟩ := hk i hi
  rw [ap_large (P * 10 ^ m + i) (by omega), ap_large (P * 10 ^ m) h10,
    ds_add P m i hi1, hP, e0, h _ hi2]

theorem ap_base10 :
    ∃ n, 1 ≤ n ∧ ∀ j < 10, additivePersistence (n + j) = additivePersistence n := by
  refine ⟨189, by norm_num, ?_⟩
  have key : ∀ x, 10 ≤ x → 10 ≤ (Nat.digits 10 x).sum →
      (Nat.digits 10 (Nat.digits 10 x).sum).sum < 10 → additivePersistence x = 2 := by
    intro x h1 h2 h3
    rw [ap_large x h1, ap_large _ h2, ap_small _ h3]
  intro j hj
  rw [key 189 (by norm_num) (by norm_num) (by norm_num)]
  interval_cases j <;> exact key _ (by norm_num) (by norm_num) (by norm_num)

theorem ap_base19 :
    ∃ n, 1 ≤ n ∧ ∀ j < 19, additivePersistence (n + j) = additivePersistence n := by
  refine ap_step 10 2 19 (by norm_num) ap_base10 ?_
  intro i hi
  refine ⟨by omega, ?_⟩
  interval_cases i <;> norm_num

theorem pow_bound (m : ℕ) : 9 * (m + 3) < 10 ^ (m + 2) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have e : 10 ^ (m + 1 + 2) = 10 * 10 ^ (m + 2) := by ring
    rw [e]
    omega

theorem ap_pow (m : ℕ) :
    ∃ n, 1 ≤ n ∧ ∀ j < 10 ^ (m + 2), additivePersistence (n + j) = additivePersistence n := by
  induction m with
  | zero =>
    refine ap_step 19 2 _ (by norm_num) ap_base19 ?_
    intro i hi
    have := ds_le 2 i hi
    exact ⟨hi, by omega⟩
  | succ m ih =>
    refine ap_step (10 ^ (m + 2)) (m + 1 + 2) _ (by omega) ih ?_
    intro i hi
    have h1 := ds_le (m + 1 + 2) i hi
    have h2 := pow_bound m
    exact ⟨hi, by omega⟩

theorem arbitrary_consecutive_same_additive_persistence (k : ℕ) :
    ∃ n : ℕ, ∀ i < k, additivePersistence (n + i) = additivePersistence n := by
  obtain ⟨n, _, hn⟩ := ap_pow k
  refine ⟨n, fun i hi => hn i ?_⟩
  have h1 : k < 10 ^ k := Nat.lt_pow_self (by norm_num)
  have h2 : 10 ^ k ≤ 10 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega
```
