# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `30 July 2026`\
Line count: `177`\
Turn count: `3`

## Solution

```lean4
import Mathlib

theorem digitSum_succ_le_aux : ∀ N m : ℕ, m ≤ N →
    (Nat.digits 10 (m + 1)).sum ≤ (Nat.digits 10 m).sum + 1 := by
  intro N
  induction N with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    have hd1 : Nat.digits 10 1 = [1] := by
      rw [Nat.digits_def' (by norm_num) (by norm_num : (0:ℕ) < 1)]
      simp
    simp [hd1]
  | succ N ihN =>
    intro m hm
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0; simp
    · have hmdef : Nat.digits 10 m = m % 10 :: Nat.digits 10 (m / 10) :=
        Nat.digits_def' (by norm_num) hm0
      have hm1pos : 0 < m + 1 := by omega
      have hm1def : Nat.digits 10 (m + 1) = (m + 1) % 10 :: Nat.digits 10 ((m + 1) / 10) :=
        Nat.digits_def' (by norm_num) hm1pos
      have hlt : m / 10 ≤ N := by omega
      by_cases hc : m % 10 < 9
      · have e1 : (m + 1) % 10 = m % 10 + 1 := by omega
        have e2 : (m + 1) / 10 = m / 10 := by omega
        rw [hm1def, hmdef, e1, e2]
        simp only [List.sum_cons]
        omega
      · have e1 : (m + 1) % 10 = 0 := by omega
        have e2 : (m + 1) / 10 = m / 10 + 1 := by omega
        have hih := ihN (m / 10) hlt
        rw [hm1def, hmdef, e1, e2]
        simp only [List.sum_cons]
        omega

theorem digitSum_succ_le (m : ℕ) :
    (Nat.digits 10 (m + 1)).sum ≤ (Nat.digits 10 m).sum + 1 :=
  digitSum_succ_le_aux m m le_rfl

theorem digitSum_add_le_aux : ∀ N a : ℕ, a ≤ N → ∀ b : ℕ,
    (Nat.digits 10 (a + b)).sum ≤ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum := by
  intro N
  induction N with
  | zero =>
    intro a ha b
    have ha0 : a = 0 := by omega
    subst ha0
    simp
  | succ N ihN =>
    intro a ha b
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0; simp
    · rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · subst hb0; simp
      · have hadef : Nat.digits 10 a = a % 10 :: Nat.digits 10 (a / 10) :=
          Nat.digits_def' (by norm_num) ha0
        have hbdef : Nat.digits 10 b = b % 10 :: Nat.digits 10 (b / 10) :=
          Nat.digits_def' (by norm_num) hb0
        have habpos : 0 < a + b := by omega
        have habdef : Nat.digits 10 (a + b) = (a + b) % 10 :: Nat.digits 10 ((a + b) / 10) :=
          Nat.digits_def' (by norm_num) habpos
        have hlt : a / 10 ≤ N := by omega
        have SA : (Nat.digits 10 a).sum = a % 10 + (Nat.digits 10 (a / 10)).sum := by
          rw [hadef, List.sum_cons]
        have SB : (Nat.digits 10 b).sum = b % 10 + (Nat.digits 10 (b / 10)).sum := by
          rw [hbdef, List.sum_cons]
        have SAB : (Nat.digits 10 (a + b)).sum = (a + b) % 10 + (Nat.digits 10 ((a + b) / 10)).sum := by
          rw [habdef, List.sum_cons]
        by_cases hcarry : a % 10 + b % 10 < 10
        · have e1 : (a + b) % 10 = a % 10 + b % 10 := by omega
          have e2 : (a + b) / 10 = a / 10 + b / 10 := by omega
          have hZ : (Nat.digits 10 ((a + b) / 10)).sum
              ≤ (Nat.digits 10 (a / 10)).sum + (Nat.digits 10 (b / 10)).sum := by
            rw [e2]; exact ihN (a / 10) hlt (b / 10)
          omega
        · have e1 : (a + b) % 10 = a % 10 + b % 10 - 10 := by omega
          have e2 : (a + b) / 10 = a / 10 + (b / 10 + 1) := by omega
          have h1 : (Nat.digits 10 (a / 10 + (b / 10 + 1))).sum
              ≤ (Nat.digits 10 (a / 10)).sum + (Nat.digits 10 (b / 10 + 1)).sum :=
            ihN (a / 10) hlt (b / 10 + 1)
          have h2 : (Nat.digits 10 (b / 10 + 1)).sum ≤ (Nat.digits 10 (b / 10)).sum + 1 :=
            digitSum_succ_le (b / 10)
          have hZ : (Nat.digits 10 ((a + b) / 10)).sum
              ≤ (Nat.digits 10 (a / 10)).sum + (Nat.digits 10 (b / 10)).sum + 1 := by
            rw [e2]; omega
          omega

theorem digitSum_add_le (a b : ℕ) :
    (Nat.digits 10 (a + b)).sum ≤ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum :=
  digitSum_add_le_aux a a le_rfl b

theorem digitSum_ten_mul (a : ℕ) :
    (Nat.digits 10 (10 * a)).sum = (Nat.digits 10 a).sum := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  · have hpos : 0 < 10 * a := by positivity
    have hdef : Nat.digits 10 (10 * a) = (10 * a) % 10 :: Nat.digits 10 ((10 * a) / 10) :=
      Nat.digits_def' (by norm_num) hpos
    have e1 : (10 * a) % 10 = 0 := by omega
    have e2 : (10 * a) / 10 = a := by omega
    rw [hdef, e1, e2, List.sum_cons]
    simp

theorem digitSum_mul_le (m c : ℕ) :
    (Nat.digits 10 (m * c)).sum ≤ m * (Nat.digits 10 c).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (m + 1) * c = m * c + c := by ring
    rw [e]
    calc (Nat.digits 10 (m * c + c)).sum
        ≤ (Nat.digits 10 (m * c)).sum + (Nat.digits 10 c).sum := digitSum_add_le (m * c) c
      _ ≤ m * (Nat.digits 10 c).sum + (Nat.digits 10 c).sum :=
          add_le_add ih (le_refl (Nat.digits 10 c).sum)
      _ = (m + 1) * (Nat.digits 10 c).sum := by ring

theorem digitSum_mul_le_mul_digitSum_aux : ∀ N a : ℕ, a ≤ N → ∀ c : ℕ,
    (Nat.digits 10 (a * c)).sum ≤ (Nat.digits 10 a).sum * (Nat.digits 10 c).sum := by
  intro N
  induction N with
  | zero =>
    intro a ha c
    have ha0 : a = 0 := by omega
    subst ha0
    simp
  | succ N ihN =>
    intro a ha c
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0; simp
    · have hadef : Nat.digits 10 a = a % 10 :: Nat.digits 10 (a / 10) :=
        Nat.digits_def' (by norm_num) ha0
      have hlt : a / 10 ≤ N := by omega
      have e : a * c = 10 * (a / 10) * c + a % 10 * c := by
        have h := Nat.div_add_mod a 10
        calc a * c = (10 * (a / 10) + a % 10) * c := by rw [h]
          _ = 10 * (a / 10) * c + a % 10 * c := by ring
      have step2 : (Nat.digits 10 (10 * (a / 10) * c)).sum = (Nat.digits 10 (a / 10 * c)).sum := by
        rw [mul_assoc]
        exact digitSum_ten_mul (a / 10 * c)
      have step3 : (Nat.digits 10 (a / 10 * c)).sum ≤ (Nat.digits 10 (a / 10)).sum * (Nat.digits 10 c).sum :=
        ihN (a / 10) hlt c
      have step4 : (Nat.digits 10 (a % 10 * c)).sum ≤ a % 10 * (Nat.digits 10 c).sum :=
        digitSum_mul_le (a % 10) c
      calc (Nat.digits 10 (a * c)).sum
          = (Nat.digits 10 (10 * (a / 10) * c + a % 10 * c)).sum := by rw [e]
        _ ≤ (Nat.digits 10 (10 * (a / 10) * c)).sum + (Nat.digits 10 (a % 10 * c)).sum :=
            digitSum_add_le _ _
        _ = (Nat.digits 10 (a / 10 * c)).sum + (Nat.digits 10 (a % 10 * c)).sum := by rw [step2]
        _ ≤ (Nat.digits 10 (a / 10)).sum * (Nat.digits 10 c).sum + a % 10 * (Nat.digits 10 c).sum :=
            add_le_add step3 step4
        _ = (a % 10 + (Nat.digits 10 (a / 10)).sum) * (Nat.digits 10 c).sum := by ring
        _ = (Nat.digits 10 a).sum * (Nat.digits 10 c).sum := by rw [hadef, List.sum_cons]

theorem digitSum_mul_le_mul_digitSum (a c : ℕ) :
    (Nat.digits 10 (a * c)).sum ≤ (Nat.digits 10 a).sum * (Nat.digits 10 c).sum :=
  digitSum_mul_le_mul_digitSum_aux a a le_rfl c

theorem digit_sum_pow_le (n x : ℕ) (hn : 0 < n) (hx : 0 < x) :
    (Nat.digits 10 (n ^ x)).sum ≤ ((Nat.digits 10 n).sum) ^ x := by
  clear hx
  induction x with
  | zero =>
    have hd1 : Nat.digits 10 1 = [1] := by
      rw [Nat.digits_def' (by norm_num) (by norm_num : (0:ℕ) < 1)]
      simp
    simp [hd1]
  | succ x ih =>
    have e : n ^ (x + 1) = n ^ x * n := pow_succ n x
    rw [e]
    calc (Nat.digits 10 (n ^ x * n)).sum
        ≤ (Nat.digits 10 (n ^ x)).sum * (Nat.digits 10 n).sum :=
          digitSum_mul_le_mul_digitSum (n ^ x) n
      _ ≤ (Nat.digits 10 n).sum ^ x * (Nat.digits 10 n).sum :=
          Nat.mul_le_mul ih (le_refl (Nat.digits 10 n).sum)
      _ = (Nat.digits 10 n).sum ^ (x + 1) := (pow_succ _ _).symm
```
