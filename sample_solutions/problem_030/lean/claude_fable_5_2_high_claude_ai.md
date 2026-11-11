# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `10 November 2026`\
Line count: `235`\
Turn count: `2`

## Solution

```lean4
import Mathlib

theorem odd_digit_sum_eq_xyz_iff (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxo : Odd x) (hyo : Odd y) (hzo : Odd z) :
      x * (Nat.digits 10 x).sum + y * (Nat.digits 10 y).sum + z * (Nat.digits 10 z).sum = x * y * z ↔
      x = 3 ∧ y = 3 ∧ z = 3 := by
  -- The digit sum `s` satisfies `s 0 = 0` and `s n = n % 10 + s (n / 10)`.
  have s0 : (Nat.digits 10 0).sum = 0 := by simp
  have srec : ∀ n : ℕ, (Nat.digits 10 n).sum = n % 10 + (Nat.digits 10 (n / 10)).sum := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [Nat.digits_def' (show (1:ℕ) < 10 by norm_num) h]; simp
  -- Everything else only uses those two facts, so we argue for an abstract `f`,
  -- and for a sorted triple `a ≤ b ≤ c`.
  have main : ∀ f : ℕ → ℕ, f 0 = 0 → (∀ n : ℕ, f n = n % 10 + f (n / 10)) →
      ∀ a b c : ℕ, a % 2 = 1 → b % 2 = 1 → c % 2 = 1 → a ≤ b → b ≤ c →
        a * f a + b * f b + c * f c = a * b * c → a = 3 ∧ b = 3 ∧ c = 3 := by
    intro f f0 frec
    -- a number below `10 ^ k` has digit sum at most `9 * k`
    have R : ∀ k n : ℕ, n < 10 ^ k → f n ≤ 9 * k := by
      intro k
      induction k with
      | zero =>
        intro n hn
        rw [pow_zero] at hn
        have hn0 : n = 0 := by omega
        have e : f n = 0 := by rw [hn0]; exact f0
        omega
      | succ k ih =>
        intro n hn
        rw [pow_succ] at hn
        have h1 : n / 10 < 10 ^ k := by omega
        have h2 := ih (n / 10) h1
        have h3 := frec n
        omega
    have E : ∀ k : ℕ, 486 * (k + 6) * (k + 6) < 10 ^ (k + 5) := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        have e : (10:ℕ) ^ (k + 1 + 5) = 10 * 10 ^ (k + 5) := by ring
        linarith [ih, e, Nat.zero_le (k * k), Nat.zero_le k]
    have big : ∀ n : ℕ, n < 10 ^ (n + 5) := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        have e : (10:ℕ) ^ (n + 1 + 5) = 10 * 10 ^ (n + 5) := by ring
        omega
    -- explicit digit sum below `10 ^ 5`
    have dig : ∀ n : ℕ, n < 100000 → f n = n % 10 + n / 10 % 10 + n / 10 / 10 % 10 + n / 10 / 10 / 10 % 10 + n / 10 / 10 / 10 / 10 := by
      intro n hn
      have h1 := frec n
      have h2 := frec (n / 10)
      have h3 := frec (n / 10 / 10)
      have h4 := frec (n / 10 / 10 / 10)
      have h5 := frec (n / 10 / 10 / 10 / 10)
      have h6 : f (n / 10 / 10 / 10 / 10 / 10) = 0 := by
        have h7 : n / 10 / 10 / 10 / 10 / 10 = 0 := by omega
        rw [h7]; exact f0
      omega
    have fle : ∀ n : ℕ, n < 100000 → f n ≤ n := by
      intro n hn
      have h1 := dig n hn
      omega
    have f45 : ∀ n : ℕ, n < 100000 → f n ≤ 45 := by
      intro n hn
      have h1 := dig n hn
      omega
    have fmod : ∀ n : ℕ, n < 100000 → f n % 3 = n % 3 := by
      intro n hn
      have h1 := dig n hn
      have h2 : n = f n + 9 * (n / 10 + n / 10 / 10 + n / 10 / 10 / 10 + n / 10 / 10 / 10 / 10) := by
        omega
      omega
    have mod3 : ∀ p : ℕ, p < 3 → ∀ q : ℕ, q < 3 → ∀ r : ℕ, r < 3 →
        (p * p + q * q + r * r) % 3 = (p * q * r) % 3 → p = 0 ∧ q = 0 ∧ r = 0 := by
      intro p hp q hq r hr hpqr
      interval_cases p <;> interval_cases q <;> interval_cases r <;>
        first | omega | (simp at hpqr)
    intro a b c ha hb hc hab hbc h
    have ha1 : 1 ≤ a := by omega
    have hb1 : 1 ≤ b := by omega
    have hc1 : 1 ≤ c := by omega
    have pa : 1 ≤ f a := by
      have h1 := frec a
      omega
    -- `c` divides `a * f a + b * f b`, in particular it is at most that
    have P2 : c ≤ a * f a + b * f b := by
      by_contra hcon
      push_neg at hcon
      have t0 : 1 * 1 ≤ a * f a := Nat.mul_le_mul ha1 pa
      have t1 : a * b ≤ f c := by
        by_contra h2
        push_neg at h2
        have h2' : f c + 1 ≤ a * b := by omega
        have t2 : c * (f c + 1) ≤ c * (a * b) := Nat.mul_le_mul (le_refl c) h2'
        linarith [t2, h, hcon]
      have t3 : c * (a * b) ≤ c * f c := Nat.mul_le_mul (le_refl c) t1
      linarith [t3, h, t0, Nat.zero_le (b * f b)]
    -- dividing the equation by `c`
    have P1 : a * b ≤ f a + f b + f c := by
      by_contra hcon
      push_neg at hcon
      have hcon' : f a + f b + f c + 1 ≤ a * b := by omega
      have t1 : a * f a ≤ c * f a := Nat.mul_le_mul (hab.trans hbc) (le_refl (f a))
      have t2 : b * f b ≤ c * f b := Nat.mul_le_mul hbc (le_refl (f b))
      have t4 : (f a + f b + f c + 1) * c ≤ a * b * c := Nat.mul_le_mul hcon' (le_refl c)
      linarith [t1, t2, t4, h, hc1]
    -- Step 1: `c < 10 ^ 5`
    have hc5 : c < 100000 := by
      have Cl : ∀ k : ℕ, c < 10 ^ (k + 5) → c < 100000 := by
        intro k
        induction k with
        | zero =>
          intro h0
          simpa using h0
        | succ k ih =>
          intro hk
          by_cases hlt : c < 10 ^ (k + 5)
          · exact ih hlt
          · exfalso
            push_neg at hlt
            have hk' : c < 10 ^ (k + 6) := by
              have e1 : k + 1 + 5 = k + 6 := by omega
              rw [← e1]
              exact hk
            have sa := R (k + 6) a (lt_of_le_of_lt (hab.trans hbc) hk')
            have sb := R (k + 6) b (lt_of_le_of_lt hbc hk')
            have sc := R (k + 6) c hk'
            have q1 : a * b ≤ 27 * (k + 6) := by omega
            have q2 : a * 1 ≤ a * b := Nat.mul_le_mul (le_refl a) hb1
            have q3 : 1 * b ≤ a * b := Nat.mul_le_mul ha1 (le_refl b)
            have q4 : a ≤ 27 * (k + 6) := by omega
            have q5 : b ≤ 27 * (k + 6) := by omega
            have q6 : a * f a ≤ 27 * (k + 6) * (9 * (k + 6)) := Nat.mul_le_mul q4 sa
            have q7 : b * f b ≤ 27 * (k + 6) * (9 * (k + 6)) := Nat.mul_le_mul q5 sb
            have q8 := E k
            linarith [q6, q7, q8, hlt, P2]
      exact Cl c (big c)
    have ha5 : a < 100000 := lt_of_le_of_lt (hab.trans hbc) hc5
    have hb5 : b < 100000 := lt_of_le_of_lt hbc hc5
    -- Step 2: `a`, `b`, `c` are all divisible by `3`
    have qa : Nat.ModEq 3 (f a) a := fmod a ha5
    have qb : Nat.ModEq 3 (f b) b := fmod b hb5
    have qc : Nat.ModEq 3 (f c) c := fmod c hc5
    have ra : Nat.ModEq 3 (a % 3) a := Nat.mod_modEq a 3
    have rb : Nat.ModEq 3 (b % 3) b := Nat.mod_modEq b 3
    have rc : Nat.ModEq 3 (c % 3) c := Nat.mod_modEq c 3
    have eL : Nat.ModEq 3 (a % 3 * (a % 3) + b % 3 * (b % 3) + c % 3 * (c % 3))
        (a * f a + b * f b + c * f c) :=
      ((ra.mul (ra.trans qa.symm)).add (rb.mul (rb.trans qb.symm))).add
        (rc.mul (rc.trans qc.symm))
    have eM : Nat.ModEq 3 (a * f a + b * f b + c * f c) (a * b * c) := by
      show (a * f a + b * f b + c * f c) % 3 = (a * b * c) % 3
      rw [h]
    have eR : Nat.ModEq 3 (a % 3 * (b % 3) * (c % 3)) (a * b * c) := (ra.mul rb).mul rc
    have key := mod3 (a % 3) (Nat.mod_lt a (by norm_num)) (b % 3) (Nat.mod_lt b (by norm_num))
      (c % 3) (Nat.mod_lt c (by norm_num)) ((eL.trans eM).trans eR.symm)
    obtain ⟨m1, m2, m3⟩ := key
    -- Step 3: `a = 3`, `b ∈ {3, 9, 15}`, `c ≤ 99`, then a finite check
    have la := fle a ha5
    have lb := fle b hb5
    have lc := f45 c hc5
    have ha3 : a = 3 := by
      by_contra hne
      have h9 : 9 ≤ a := by omega
      have t : 9 * b ≤ a * b := Nat.mul_le_mul h9 (le_refl b)
      omega
    subst ha3
    have hb24 : b ≤ 24 := by omega
    have db := dig b hb5
    have hb3 : b = 3 ∨ b = 9 ∨ b = 15 := by
      interval_cases b <;> omega
    have d3 := dig 3 (by norm_num)
    have d9 := dig 9 (by norm_num)
    have d15 := dig 15 (by norm_num)
    have dc := dig c hc5
    have hcu : c ≤ 99 := by
      rcases hb3 with rfl | rfl | rfl <;> omega
    obtain ⟨w, rfl⟩ : ∃ w : ℕ, c = 6 * w + 3 := ⟨c / 6, by omega⟩
    have hw : w ≤ 16 := by omega
    rcases hb3 with rfl | rfl | rfl <;> interval_cases w <;> omega
  -- Specialise to the digit sum.
  have s : ∀ a b c : ℕ, a % 2 = 1 → b % 2 = 1 → c % 2 = 1 → a ≤ b → b ≤ c →
      a * (Nat.digits 10 a).sum + b * (Nat.digits 10 b).sum + c * (Nat.digits 10 c).sum
        = a * b * c → a = 3 ∧ b = 3 ∧ c = 3 :=
    main (fun n => (Nat.digits 10 n).sum) s0 srec
  have ox : x % 2 = 1 := Nat.odd_iff.mp hxo
  have oy : y % 2 = 1 := Nat.odd_iff.mp hyo
  have oz : z % 2 = 1 := Nat.odd_iff.mp hzo
  constructor
  · intro h
    rcases le_total x y with hxy | hxy
    · rcases le_total y z with hyz | hyz
      · exact s x y z ox oy oz hxy hyz h
      · rcases le_total x z with hxz | hxz
        · have hp : x * (Nat.digits 10 x).sum + z * (Nat.digits 10 z).sum
              + y * (Nat.digits 10 y).sum = x * z * y := by
            have e : x * z * y = x * y * z := by ring
            rw [e, ← h]; ring
          obtain ⟨h1, h2, h3⟩ := s x z y ox oz oy hxz hyz hp
          exact ⟨h1, h3, h2⟩
        · have hp : z * (Nat.digits 10 z).sum + x * (Nat.digits 10 x).sum
              + y * (Nat.digits 10 y).sum = z * x * y := by
            have e : z * x * y = x * y * z := by ring
            rw [e, ← h]; ring
          obtain ⟨h1, h2, h3⟩ := s z x y oz ox oy hxz hxy hp
          exact ⟨h2, h3, h1⟩
    · rcases le_total y z with hyz | hyz
      · rcases le_total x z with hxz | hxz
        · have hp : y * (Nat.digits 10 y).sum + x * (Nat.digits 10 x).sum
              + z * (Nat.digits 10 z).sum = y * x * z := by
            have e : y * x * z = x * y * z := by ring
            rw [e, ← h]; ring
          obtain ⟨h1, h2, h3⟩ := s y x z oy ox oz hxy hxz hp
          exact ⟨h2, h1, h3⟩
        · have hp : y * (Nat.digits 10 y).sum + z * (Nat.digits 10 z).sum
              + x * (Nat.digits 10 x).sum = y * z * x := by
            have e : y * z * x = x * y * z := by ring
            rw [e, ← h]; ring
          obtain ⟨h1, h2, h3⟩ := s y z x oy oz ox hyz hxz hp
          exact ⟨h3, h1, h2⟩
      · have hp : z * (Nat.digits 10 z).sum + y * (Nat.digits 10 y).sum
            + x * (Nat.digits 10 x).sum = z * y * x := by
          have e : z * y * x = x * y * z := by ring
          rw [e, ← h]; ring
        obtain ⟨h1, h2, h3⟩ := s z y x oz oy ox hyz hxy hp
        exact ⟨h3, h2, h1⟩
  · rintro ⟨rfl, rfl, rfl⟩
    have e1 := srec 3
    have e0 : (3:ℕ) / 10 = 0 := by norm_num
    rw [e0, s0] at e1
    omega
```
