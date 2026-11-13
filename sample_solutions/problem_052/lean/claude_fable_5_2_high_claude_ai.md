# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `13 November 2026`\
Line count: `186`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem permutations_a_b_log_eq_unique_sol_count :
    Nat.card { p : ℕ × ℕ |
      let a := p.1
      let b := p.2
      0 < a ∧ 0 < b ∧ a + b = 2026 ∧
      ∃! x : ℝ, 0 < x ^ 3 + (a : ℝ) ∧ 0 < x ^ b - 3 * (a : ℝ) ∧
      Real.log (x ^ 3 + (a : ℝ)) = Real.log (x ^ b - 3 * (a : ℝ)) } = 1011 := by
  -- Step 1: remove the logarithm.
  have key : ∀ (a b : ℕ) (x : ℝ), (0 < x ^ 3 + (a : ℝ) ∧ 0 < x ^ b - 3 * (a : ℝ) ∧
      Real.log (x ^ 3 + (a : ℝ)) = Real.log (x ^ b - 3 * (a : ℝ))) ↔
      (x ^ b = x ^ 3 + 4 * (a : ℝ) ∧ 0 < x ^ 3 + (a : ℝ)) := by
    intro a b x
    constructor
    · rintro ⟨h1, h2, h3⟩
      have h4 : x ^ 3 + (a : ℝ) = x ^ b - 3 * (a : ℝ) :=
        Real.log_injOn_pos (Set.mem_Ioi.2 h1) (Set.mem_Ioi.2 h2) h3
      exact ⟨by linarith, h1⟩
    · rintro ⟨h1, h2⟩
      have e : x ^ b - 3 * (a : ℝ) = x ^ 3 + (a : ℝ) := by linarith
      rw [e]
      exact ⟨h2, h2, rfl⟩
  -- Step 2: the unique-solution condition holds iff `b` is odd and `b ≥ 5`.
  have main : ∀ a b : ℕ, 0 < a → 0 < b → a + b = 2026 →
      ((∃! x : ℝ, 0 < x ^ 3 + (a : ℝ) ∧ 0 < x ^ b - 3 * (a : ℝ) ∧
        Real.log (x ^ 3 + (a : ℝ)) = Real.log (x ^ b - 3 * (a : ℝ))) ↔
        (b % 2 = 1 ∧ 5 ≤ b)) := by
    intro a b ha hb hab
    simp only [key]
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have haR' : (a : ℝ) ≤ 2025 := by exact_mod_cast (by omega : a ≤ 2025)
    -- a root `x ≥ 1` exists as soon as `b ≥ 4`
    have pos_root : 4 ≤ b → ∃ x : ℝ, 1 ≤ x ∧ x ^ b = x ^ 3 + 4 * (a : ℝ) := by
      intro hb4
      have hcont : ContinuousOn (fun x : ℝ => x ^ b - x ^ 3) (Set.Icc 1 16) :=
        ((continuous_pow b).sub (continuous_pow 3)).continuousOn
      have h16 : (16 : ℝ) ^ 4 ≤ 16 ^ b := pow_le_pow_right₀ (by norm_num) hb4
      have hmem : (4 * (a : ℝ)) ∈ Set.Icc ((1 : ℝ) ^ b - 1 ^ 3) ((16 : ℝ) ^ b - 16 ^ 3) := by
        constructor
        · rw [one_pow, one_pow]; linarith
        · norm_num at h16 ⊢; linarith
      obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (by norm_num) hcont hmem
      have hfx' : x ^ b - x ^ 3 = 4 * (a : ℝ) := hfx
      exact ⟨x, hx.1, by linarith⟩
    -- for even `b ≥ 4` there is also a root `-t ≤ 0`
    have neg_root : Even b → 4 ≤ b →
        ∃ t : ℝ, 0 ≤ t ∧ t ^ b + t ^ 3 = 4 * (a : ℝ) ∧ t ^ 3 < a := by
      intro hev hb4
      have hcont : ContinuousOn (fun x : ℝ => x ^ b + x ^ 3) (Set.Icc 0 16) :=
        ((continuous_pow b).add (continuous_pow 3)).continuousOn
      have h16 : (16 : ℝ) ^ 4 ≤ 16 ^ b := pow_le_pow_right₀ (by norm_num) hb4
      have hmem : (4 * (a : ℝ)) ∈ Set.Icc ((0 : ℝ) ^ b + 0 ^ 3) ((16 : ℝ) ^ b + 16 ^ 3) := by
        constructor
        · rw [zero_pow (by omega), zero_pow (by norm_num)]; linarith
        · norm_num at h16 ⊢; linarith
      obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (by norm_num) hcont hmem
      have hft' : t ^ b + t ^ 3 = 4 * (a : ℝ) := hft
      refine ⟨t, ht.1, hft', ?_⟩
      by_contra hge
      have hge' : (a : ℝ) ≤ t ^ 3 := not_lt.1 hge
      have ht0 : 0 ≤ t := ht.1
      have ha2 : (2 : ℝ) ≤ a := by
        exact_mod_cast (by obtain ⟨k, hk⟩ := hev; omega : 2 ≤ a)
      have ht1 : 1 ≤ t := by
        by_contra h
        have h' : t < 1 := not_le.1 h
        have : t ^ 3 < 1 := pow_lt_one₀ ht0 h' (by norm_num)
        linarith
      have h3 : t ^ b ≤ 3 * t ^ 3 := by linarith
      have hsplit : t ^ b = t ^ (b - 3) * t ^ 3 := by
        rw [← pow_add]; congr 1; omega
      have ht3pos : 0 < t ^ 3 := pow_pos (by linarith) 3
      have h4 : t ^ (b - 3) ≤ 3 := by
        by_contra h
        have h' : 3 < t ^ (b - 3) := not_le.1 h
        have : 3 * t ^ 3 < t ^ (b - 3) * t ^ 3 := mul_lt_mul_of_pos_right h' ht3pos
        linarith
      by_cases hb9 : 9 ≤ b
      · have h5 : t ^ 6 ≤ t ^ (b - 3) := pow_le_pow_right₀ ht1 (by omega)
        have h6 : t ^ 6 = t ^ 3 * t ^ 3 := by ring
        have h7 : 2 * 2 ≤ t ^ 3 * t ^ 3 :=
          mul_le_mul (by linarith) (by linarith) (by norm_num) ht3pos.le
        linarith
      · have h5 : t ^ 1 ≤ t ^ (b - 3) := pow_le_pow_right₀ ht1 (by omega)
        rw [pow_one] at h5
        have ha3 : (2018 : ℝ) ≤ a := by exact_mod_cast (by omega : 2018 ≤ a)
        have h6 : t ≤ 3 := le_trans h5 h4
        have h7 : t ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ ht0 h6 3
        norm_num at h7
        linarith
    constructor
    · -- uniqueness forces `b` odd and `b ≥ 5`
      intro hex
      by_contra hcon
      obtain ⟨x, ⟨hx1, hx2⟩, huniq⟩ := hex
      rcases Nat.even_or_odd b with hev | hodd
      · by_cases hb2 : b = 2
        · subst hb2
          have ha' : (a : ℝ) = 2024 := by exact_mod_cast (by omega : a = 2024)
          rw [ha'] at hx1 hx2
          rcases le_or_gt 1 x with h | h
          · nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.2 h)]
          · have hx77 : x < -77 := by
              by_contra h'
              have h'' : -77 ≤ x := not_lt.1 h'
              nlinarith
            nlinarith [mul_pos (sub_pos.2 hx77) (by nlinarith : (0 : ℝ) < x ^ 2 - 6072)]
        · have hb4 : 4 ≤ b := by obtain ⟨k, hk⟩ := hev; omega
          obtain ⟨x1, hx1', hx1e⟩ := pos_root hb4
          obtain ⟨t, ht0, hte, hta⟩ := neg_root hev hb4
          have hx1pos : 0 ≤ x1 ^ 3 := pow_nonneg (by linarith) 3
          have e1 := huniq x1 ⟨hx1e, by linarith⟩
          have hneg3 : (-t) ^ 3 = -t ^ 3 := by ring
          have e2 := huniq (-t) ⟨by rw [hev.neg_pow, hneg3]; linarith, by rw [hneg3]; linarith⟩
          linarith
      · have hb13 : b = 1 ∨ b = 3 := by
          obtain ⟨k, hk⟩ := hodd; omega
        rcases hb13 with rfl | rfl
        · have ha' : (a : ℝ) = 2025 := by exact_mod_cast (by omega : a = 2025)
          rw [ha', pow_one] at hx1
          rw [ha'] at hx2
          have hx6 : 6075 < x := by linarith
          have hsq : 1 ≤ x ^ 2 := by nlinarith
          have hcube : x ≤ x ^ 3 := by nlinarith
          linarith
        · linarith
    · -- `b` odd and `b ≥ 5` gives exactly one solution
      rintro ⟨hodd, hb5⟩
      obtain ⟨x, hx1, hxe⟩ := pos_root (by omega)
      have hmono : ∀ u v : ℝ, 1 < u → u < v → u ^ b - u ^ 3 < v ^ b - v ^ 3 := by
        intro u v hu huv
        have e : ∀ w : ℝ, w ^ b - w ^ 3 = w ^ 3 * (w ^ (b - 3) - 1) := by
          intro w
          have : w ^ b = w ^ 3 * w ^ (b - 3) := by
            rw [← pow_add]; congr 1; omega
          rw [this]; ring
        rw [e, e]
        have hu0 : 0 ≤ u := by linarith
        have h1 : u ^ 3 < v ^ 3 := pow_lt_pow_left₀ huv hu0 (by norm_num)
        have h2 : u ^ (b - 3) < v ^ (b - 3) := pow_lt_pow_left₀ huv hu0 (by omega)
        have h3 : 1 < u ^ (b - 3) := one_lt_pow₀ hu (by omega)
        have h4 : 0 < u ^ 3 := pow_pos (by linarith) 3
        exact mul_lt_mul'' h1 (by linarith) h4.le (by linarith)
      have hgt : ∀ y : ℝ, y ^ b = y ^ 3 + 4 * (a : ℝ) → 0 < y ^ 3 + (a : ℝ) → 1 < y := by
        intro y hy1 hy2
        by_contra h
        have h' : y ≤ 1 := not_lt.1 h
        rcases le_or_gt 0 y with h0 | h0
        · have h5 : y ^ b ≤ 1 := pow_le_one₀ h0 h'
          have h6 : 0 ≤ y ^ 3 := pow_nonneg h0 3
          linarith
        · have h5 : y ^ b < 0 := Odd.pow_neg (Nat.odd_iff.2 hodd) h0
          linarith
      have hx3 : 0 ≤ x ^ 3 := pow_nonneg (by linarith) 3
      refine ⟨x, ⟨hxe, by linarith⟩, ?_⟩
      rintro y ⟨hy1, hy2⟩
      have hy := hgt y hy1 hy2
      have hx := hgt x hxe (by linarith)
      rcases lt_trichotomy y x with h | h | h
      · have := hmono y x hy h; linarith
      · exact h
      · have := hmono x y hx h; linarith
  -- Step 3: count.
  have hS : ∀ S : Set (ℕ × ℕ),
      (∀ p, p ∈ S ↔ ∃ k, k < 1011 ∧ (2021 - 2 * k, 2 * k + 5) = p) → Nat.card S = 1011 := by
    intro S hS
    have hSeq : S = ↑((Finset.range 1011).image (fun k : ℕ => (2021 - 2 * k, 2 * k + 5))) := by
      ext p
      rw [hS p]
      simp
    rw [hSeq, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn,
      Finset.card_range]
    intro k1 hk1 k2 hk2 h
    simp only [Prod.mk.injEq] at h
    omega
  apply hS
  rintro ⟨a, b⟩
  constructor
  · rintro ⟨ha, hb, hab, hex⟩
    have h := (main a b ha hb hab).1 hex
    exact ⟨(b - 5) / 2, by omega, by ext <;> simp <;> omega⟩
  · rintro ⟨k, hk, hp⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    refine ⟨by omega, by omega, by omega, ?_⟩
    exact (main _ _ (by omega) (by omega) (by omega)).2 ⟨by omega, by omega⟩
```
