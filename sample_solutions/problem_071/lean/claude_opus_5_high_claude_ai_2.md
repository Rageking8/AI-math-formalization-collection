# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `21 August 2026`\
Line count: `163`\
Turn count: `1`

## Note

The solution is more verbose as the model is explicitly told not to use `native_decide`. The conversation contained 1 "Continue" message not included in the turn count.

## Solution

```lean4
import Mathlib

def R (n d : ℕ) : ℕ := d * ((10 ^ n - 1) / 9)

def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- The base-1000 repunit with `k` ones. -/
def rep1000 : ℕ → ℕ
  | 0 => 0
  | (k + 1) => 1 + 1000 * rep1000 k

lemma rep1000_spec (k : ℕ) : 999 * rep1000 k + 1 = 10 ^ (3 * k) := by
  induction k with
  | zero => simp [rep1000]
  | succ n ih =>
    have hp : (10 : ℕ) ^ (3 * (n + 1)) = 10 ^ (3 * n) * 1000 := by
      rw [show 3 * (n + 1) = 3 * n + 3 by ring, pow_add]
      norm_num
    simp only [rep1000]
    omega

lemma S_zero : S 0 = 0 := by simp [S]

lemma S_step (n : ℕ) : S n = n % 10 + S (n / 10) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [S]
  · simp only [S]
    rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 10) h]
    simp

lemma S_lt_ten (n : ℕ) (h : n < 10) : S n = n := by
  have h1 := S_step n
  have h2 : n % 10 = n := by omega
  have h3 : n / 10 = 0 := by omega
  rw [h2, h3, S_zero] at h1
  omega

lemma S_split : ∀ (k x y : ℕ), x < 10 ^ k → S (x + 10 ^ k * y) = S x + S y := by
  intro k
  induction k with
  | zero =>
    intro x y hx
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simp [S_zero]
  | succ n ih =>
    intro x y hx
    have hpow : (10 : ℕ) ^ (n + 1) = 10 ^ n * 10 := pow_succ 10 n
    have hx' : x / 10 < 10 ^ n := by omega
    have key : x + 10 ^ (n + 1) * y = x + 10 * (10 ^ n * y) := by rw [hpow]; ring
    have hdiv : (x + 10 * (10 ^ n * y)) / 10 = x / 10 + 10 ^ n * y := by omega
    have hmod : (x + 10 * (10 ^ n * y)) % 10 = x % 10 := by omega
    rw [key, S_step (x + 10 * (10 ^ n * y)), hdiv, hmod, ih _ _ hx', ← Nat.add_assoc,
      ← S_step x]

lemma S_split_pow (k x y b : ℕ) (hb : b = 10 ^ k) (hx : x < b) :
    S (x + b * y) = S x + S y := by
  subst hb; exact S_split k x y hx

lemma S_num (n r q : ℕ) (h : n = r + 10 * q) (hr : r < 10) : S n = r + S q := by
  subst h
  rw [S_split_pow 1 r q 10 (by norm_num) hr, S_lt_ten r hr]

lemma S_rep (v : ℕ) (hv : v < 1000) (k : ℕ) : S (v * rep1000 k) = k * S v := by
  induction k with
  | zero => simp [rep1000, S_zero]
  | succ n ih =>
    have h : v * rep1000 (n + 1) = v + 1000 * (v * rep1000 n) := by
      simp only [rep1000]; ring
    rw [h, S_split_pow 3 v (v * rep1000 n) 1000 (by norm_num) hv, ih]
    ring

lemma div9 (n t : ℕ) (h : n = 9 * t + 1) : (n - 1) / 9 = t := by
  subst h; omega

lemma sqrt_mul_self (n : ℕ) : Nat.sqrt (n * n) = n := by
  first
  | exact Nat.sqrt_eq n
  | exact Nat.sqrt_eq' n
  | (have h1 : n ≤ Nat.sqrt (n * n) := Nat.le_sqrt.mpr le_rfl
     have h2 : Nat.sqrt (n * n) < n + 1 := Nat.sqrt_lt.mpr (by nlinarith)
     omega)

theorem digit_sum_rep_digits_expr :
    S ((Nat.sqrt (R 3334 4 - R 1667 8) - 5) ^ 3) = 24994 := by
  have s2 : S 2 = 2 := S_lt_ten 2 (by norm_num)
  have s6 : S 6 = 6 := S_lt_ten 6 (by norm_num)
  have s7 : S 7 = 7 := S_lt_ten 7 (by norm_num)
  have s0 : S 0 = 0 := S_zero
  have s27 : S 27 = 9 := by
    have h := S_num 27 7 2 (by norm_num) (by norm_num); omega
  have s29 : S 29 = 11 := by
    have h := S_num 29 9 2 (by norm_num) (by norm_num); omega
  have s62 : S 62 = 8 := by
    have h := S_num 62 2 6 (by norm_num) (by norm_num); omega
  have s74 : S 74 = 11 := by
    have h := S_num 74 4 7 (by norm_num) (by norm_num); omega
  have s278 : S 278 = 17 := by
    have h := S_num 278 8 27 (by norm_num) (by norm_num); omega
  have s296 : S 296 = 17 := by
    have h := S_num 296 6 29 (by norm_num) (by norm_num); omega
  have s622 : S 622 = 10 := by
    have h := S_num 622 2 62 (by norm_num) (by norm_num); omega
  have s629 : S 629 = 17 := by
    have h := S_num 629 9 62 (by norm_num) (by norm_num); omega
  have s747 : S 747 = 18 := by
    have h := S_num 747 7 74 (by norm_num) (by norm_num); omega
  have s2781 : S 2781 = 18 := by
    have h := S_num 2781 1 278 (by norm_num) (by norm_num); omega
  have s7471 : S 7471 = 19 := by
    have h := S_num 7471 1 747 (by norm_num) (by norm_num); omega
  obtain ⟨G, hG, hS296, hS74, hS629⟩ :
      ∃ G : ℕ, 999 * G + 1 = 10 ^ 1662 ∧ S (296 * G) = 9418 ∧ S (74 * G) = 6094 ∧
        S (629 * G) = 9418 := by
    refine ⟨rep1000 554, ?_, ?_, ?_, ?_⟩
    · have h := rep1000_spec 554
      rw [show 3 * 554 = 1662 by norm_num] at h
      exact h
    · have h := S_rep 296 (by norm_num) 554; omega
    · have h := S_rep 74 (by norm_num) 554; omega
    · have h := S_rep 629 (by norm_num) 554; omega
  have h1663 : (10 : ℕ) ^ 1663 = 10 * 10 ^ 1662 := by
    rw [show (1663 : ℕ) = 1 + 1662 by norm_num, pow_add, pow_one]
  have h1667 : (10 : ℕ) ^ 1667 = 100000 * 10 ^ 1662 := by
    rw [show (1667 : ℕ) = 5 + 1662 by norm_num, pow_add,
      show (10 : ℕ) ^ 5 = 100000 by norm_num]
  have h3334 : (10 : ℕ) ^ 3334 = 10 ^ 1667 * 10 ^ 1667 := by
    rw [show (3334 : ℕ) = 1667 + 1667 by norm_num, pow_add]
  obtain ⟨t, htdef⟩ : ∃ t : ℕ, t = 11100000 * G + 11111 := ⟨_, rfl⟩
  have ht : (10 : ℕ) ^ 1667 = 9 * t + 1 := by
    rw [h1667, ← hG, htdef]; ring
  have hR8 : R 1667 8 = 8 * t := by
    show 8 * ((10 ^ 1667 - 1) / 9) = 8 * t
    rw [div9 _ _ ht]
  have hu : (10 : ℕ) ^ 3334 = 9 * (9 * (t * t) + 2 * t) + 1 := by
    rw [h3334, ht]; ring
  have hR4 : R 3334 4 = 4 * (9 * (t * t) + 2 * t) := by
    show 4 * ((10 ^ 3334 - 1) / 9) = 4 * (9 * (t * t) + 2 * t)
    rw [div9 _ _ hu]
  have hkey : 4 * (9 * (t * t) + 2 * t) = 6 * t * (6 * t) + 8 * t := by ring
  have hsub : R 3334 4 - R 1667 8 = 6 * t * (6 * t) := by
    rw [hR4, hR8]; omega
  have hsqrt : Nat.sqrt (R 3334 4 - R 1667 8) = 6 * t := by
    rw [hsub]; exact sqrt_mul_self (6 * t)
  have hN : 6 * t - 5 = 66600000 * G + 66661 := by omega
  have hb1 : 6 + 10 * (629 * G) < 10 ^ 1663 := by rw [h1663, ← hG]; omega
  have hb2 : 0 + 10 * (74 * G) < 10 ^ 1663 := by rw [h1663, ← hG]; omega
  have hA : (66600000 * G + 66661) ^ 3 =
      2781 + 10000 * (6 + 10 * (629 * G) + 10 ^ 1663 *
        (7471 + 10000 * (0 + 10 * (74 * G) + 10 ^ 1663 *
          (622 + 1000 * (29 + 100 * (296 * G)))))) := by
    rw [h1663, ← hG]; ring
  rw [hsqrt, hN, hA,
    S_split_pow 4 2781 _ 10000 (by norm_num) (by norm_num),
    S_split_pow 1663 (6 + 10 * (629 * G)) _ (10 ^ 1663) rfl hb1,
    S_split_pow 4 7471 _ 10000 (by norm_num) (by norm_num),
    S_split_pow 1663 (0 + 10 * (74 * G)) _ (10 ^ 1663) rfl hb2,
    S_split_pow 3 622 _ 1000 (by norm_num) (by norm_num),
    S_split_pow 2 29 _ 100 (by norm_num) (by norm_num),
    S_split_pow 1 6 _ 10 (by norm_num) (by norm_num),
    S_split_pow 1 0 _ 10 (by norm_num) (by norm_num)]
  clear hA hb1 hb2 hsub hsqrt hR4 hR8 hkey hu ht h3334 h1667 h1663 hG htdef
  omega
```
