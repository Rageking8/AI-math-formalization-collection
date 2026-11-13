# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `12 November 2026`\
Line count: `256`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem cos_eq_solutions_count :
    Set.ncard { x : ℝ | Real.cos (100 * Real.pi * x ^ 2) = 2.01 * x ^ 2 - 1 } = 198 := by
  have c : (2.01 : ℝ) = 201 / 100 := by norm_num
  rw [c]
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpisq : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four]
  -- reduce to one half-period
  have shift : ∀ (k : ℕ) (t : ℝ), Real.cos (100 * Real.pi * t)
      = (-1 : ℝ) ^ k * Real.cos (Real.pi * (100 * t - k)) := by
    intro k t
    rw [← Real.cos_add_nat_mul_pi]
    congr 1
    ring
  -- elementary bounds
  have lo : ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 25 → 617 / 625 ≤ Real.cos (Real.pi * s) := by
    intro s h0 h1
    have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi * s)
    have hs : s ^ 2 ≤ 1 / 625 := by nlinarith
    have : Real.pi ^ 2 * s ^ 2 ≤ 16 * (1 / 625) :=
      mul_le_mul hpisq hs (sq_nonneg s) (by norm_num)
    rw [mul_pow] at h
    linarith
  have sinlb : ∀ m : ℝ, 1 / 25 ≤ m → m ≤ 24 / 25 → 2 / 25 ≤ Real.sin (Real.pi * m) := by
    intro m h0 h1
    have aux : ∀ y : ℝ, 1 / 25 ≤ y → y ≤ 1 / 2 → 2 / 25 ≤ Real.sin (Real.pi * y) := by
      intro y hy0 hy1
      have h := Real.mul_le_sin (x := Real.pi * y) (mul_nonneg hpi0.le (by linarith))
        (by nlinarith [mul_nonneg hpi0.le (sub_nonneg.2 hy1)])
      have e : 2 / Real.pi * (Real.pi * y) = 2 * y := by field_simp
      rw [e] at h
      linarith
    rcases le_total m (1 / 2) with hm | hm
    · exact aux m h0 hm
    · have := aux (1 - m) (by linarith) (by linarith)
      rwa [show Real.pi * (1 - m) = Real.pi - Real.pi * m by ring, Real.sin_pi_sub] at this
  -- any root t ≥ 0 lies in (0, 99/100)
  have bd : ∀ t : ℝ, 0 ≤ t → Real.cos (100 * Real.pi * t) = 201 / 100 * t - 1 →
      0 < t ∧ 100 * t < 99 := by
    intro t h0 e
    constructor
    · rcases h0.lt_or_eq with h | h
      · exact h
      · rw [← h] at e; norm_num at e
    · by_contra h
      have h := not_lt.mp h
      have ht : 201 / 100 * t - 1 ≤ 1 := by rw [← e]; exact Real.cos_le_one _
      have e99 := shift 99 t
      rw [show ((-1 : ℝ)) ^ 99 = -1 by norm_num, show ((99 : ℕ) : ℝ) = 99 by norm_num] at e99
      have h3 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
        rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
          Real.cos_pi_div_three]
        norm_num
      have := Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi * (100 * t - 99))
        (y := 2 * Real.pi / 3) (mul_nonneg hpi0.le (by linarith)) (by linarith)
        (by nlinarith [mul_nonneg hpi0.le (show (0 : ℝ) ≤ 2 / 3 - (100 * t - 99) by linarith)])
      linarith
  -- at most one root in each half-period
  have uniq : ∀ k : ℕ, k < 99 → ∀ t₁ t₂ : ℝ, (k : ℝ) ≤ 100 * t₁ → t₁ < t₂ →
      100 * t₂ ≤ (k : ℝ) + 1 →
      Real.cos (100 * Real.pi * t₁) = 201 / 100 * t₁ - 1 →
      Real.cos (100 * Real.pi * t₂) = 201 / 100 * t₂ - 1 → False := by
    intro k hk t₁ t₂ h1 h12 h2 e1 e2
    rw [shift k] at e1 e2
    obtain ⟨s₁, hs₁⟩ : ∃ s : ℝ, s = 100 * t₁ - k := ⟨_, rfl⟩
    obtain ⟨s₂, hs₂⟩ : ∃ s : ℝ, s = 100 * t₂ - k := ⟨_, rfl⟩
    rw [← hs₁] at e1
    rw [← hs₂] at e2
    have a1 : 0 ≤ s₁ := by linarith
    have a2 : s₁ < s₂ := by linarith
    have a3 : s₂ ≤ 1 := by linarith
    have hkR : (k : ℝ) ≤ 98 := by exact_mod_cast Nat.lt_succ_iff.mp hk
    rcases Nat.even_or_odd k with he | ho
    · rw [he.neg_one_pow, one_mul] at e1 e2
      have m1 : Real.pi * s₁ ∈ Set.Icc 0 Real.pi :=
        ⟨mul_nonneg hpi0.le a1, by nlinarith⟩
      have m2 : Real.pi * s₂ ∈ Set.Icc 0 Real.pi :=
        ⟨mul_nonneg hpi0.le (by linarith), by nlinarith⟩
      have := Real.strictAntiOn_cos m1 m2 (by nlinarith)
      linarith
    · rw [ho.neg_one_pow] at e1 e2
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast ho.pos
      have hk97 : (k : ℝ) ≤ 97 := by
        obtain ⟨m, hm⟩ := ho
        have : k ≤ 97 := by omega
        exact_mod_cast this
      have mid : ∀ t s : ℝ, s = 100 * t - k → 0 ≤ s → s ≤ 1 →
          -1 * Real.cos (Real.pi * s) = 201 / 100 * t - 1 → 1 / 25 < s ∧ s < 24 / 25 := by
        intro t s hs h0 h1 e
        constructor
        · by_contra h
          have := lo s h0 (not_lt.mp h)
          linarith
        · by_contra h
          have := lo (1 - s) (by linarith) (by linarith [not_lt.mp h])
          rw [show Real.pi * (1 - s) = Real.pi - Real.pi * s by ring, Real.cos_pi_sub] at this
          linarith
      obtain ⟨b1, b2⟩ := mid t₁ s₁ hs₁ a1 (by linarith) e1
      obtain ⟨b3, b4⟩ := mid t₂ s₂ hs₂ (by linarith) a3 e2
      have hA := sinlb ((s₁ + s₂) / 2) (by linarith) (by linarith)
      have hB := Real.mul_le_sin (x := Real.pi * (s₂ - s₁) / 2)
        (by nlinarith [mul_pos hpi0 (sub_pos.2 a2)])
        (by nlinarith [mul_nonneg hpi0.le (show (0 : ℝ) ≤ 1 - (s₂ - s₁) by linarith)])
      have e : 2 / Real.pi * (Real.pi * (s₂ - s₁) / 2) = s₂ - s₁ := by field_simp
      rw [e] at hB
      have hC := Real.cos_sub_cos (Real.pi * s₁) (Real.pi * s₂)
      rw [show (Real.pi * s₁ + Real.pi * s₂) / 2 = Real.pi * ((s₁ + s₂) / 2) by ring,
        show (Real.pi * s₁ - Real.pi * s₂) / 2 = -(Real.pi * (s₂ - s₁) / 2) by ring,
        Real.sin_neg] at hC
      have hD : 2 / 25 * (s₂ - s₁) ≤ Real.sin (Real.pi * ((s₁ + s₂) / 2))
          * Real.sin (Real.pi * (s₂ - s₁) / 2) :=
        mul_le_mul hA hB (by linarith) (by linarith)
      nlinarith
  -- a root in each half-period, by the intermediate value theorem
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ,
      ∀ t, f t = Real.cos (100 * Real.pi * t) - (201 / 100 * t - 1) := ⟨_, fun _ => rfl⟩
  have fcont : Continuous f := by
    have : f = fun t => Real.cos (100 * Real.pi * t) - (201 / 100 * t - 1) := funext hf
    rw [this]
    fun_prop
  have ex : ∀ k : ℕ, k < 99 → ∃ t : ℝ, (k : ℝ) < 100 * t ∧ 100 * t < (k : ℝ) + 1 ∧
      Real.cos (100 * Real.pi * t) = 201 / 100 * t - 1 := by
    intro k hk
    have hkR : (k : ℝ) ≤ 98 := by exact_mod_cast Nat.lt_succ_iff.mp hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hab : (k : ℝ) / 100 ≤ ((k : ℝ) + 1) / 100 := by linarith
    have fa : f ((k : ℝ) / 100) = (-1 : ℝ) ^ k - (201 / 100 * ((k : ℝ) / 100) - 1) := by
      rw [hf, show 100 * Real.pi * ((k : ℝ) / 100) = k * Real.pi by ring, Real.cos_nat_mul_pi]
    have fb : f (((k : ℝ) + 1) / 100)
        = (-1 : ℝ) ^ (k + 1) - (201 / 100 * (((k : ℝ) + 1) / 100) - 1) := by
      rw [hf, show 100 * Real.pi * (((k : ℝ) + 1) / 100) = ((k + 1 : ℕ) : ℝ) * Real.pi by
        push_cast; ring, Real.cos_nat_mul_pi]
    rcases Nat.even_or_odd k with he | ho
    · have h1 : (-1 : ℝ) ^ k = 1 := he.neg_one_pow
      have h2 : (-1 : ℝ) ^ (k + 1) = -1 := by rw [pow_succ, h1]; norm_num
      have h0 : (0 : ℝ) ∈ Set.Ioo (f (((k : ℝ) + 1) / 100)) (f ((k : ℝ) / 100)) := by
        rw [fa, fb, h1, h2]; constructor <;> linarith
      obtain ⟨t, ⟨ht1, ht2⟩, ht⟩ := intermediate_value_Ioo' hab fcont.continuousOn h0
      rw [hf] at ht
      exact ⟨t, by linarith, by linarith, by linarith⟩
    · have h1 : (-1 : ℝ) ^ k = -1 := ho.neg_one_pow
      have h2 : (-1 : ℝ) ^ (k + 1) = 1 := by rw [pow_succ, h1]; norm_num
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast ho.pos
      have hk97 : (k : ℝ) ≤ 97 := by
        obtain ⟨m, hm⟩ := ho
        have : k ≤ 97 := by omega
        exact_mod_cast this
      have h0 : (0 : ℝ) ∈ Set.Ioo (f ((k : ℝ) / 100)) (f (((k : ℝ) + 1) / 100)) := by
        rw [fa, fb, h1, h2]; constructor <;> linarith
      obtain ⟨t, ⟨ht1, ht2⟩, ht⟩ := intermediate_value_Ioo hab fcont.continuousOn h0
      rw [hf] at ht
      exact ⟨t, by linarith, by linarith, by linarith⟩
  -- roots with the same ⌊100 t⌋ coincide
  have tinj : ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → 0 ≤ t₂ →
      Real.cos (100 * Real.pi * t₁) = 201 / 100 * t₁ - 1 →
      Real.cos (100 * Real.pi * t₂) = 201 / 100 * t₂ - 1 →
      ⌊100 * t₁⌋₊ = ⌊100 * t₂⌋₊ → t₁ = t₂ := by
    have aux : ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → 0 ≤ t₂ →
        Real.cos (100 * Real.pi * t₁) = 201 / 100 * t₁ - 1 →
        Real.cos (100 * Real.pi * t₂) = 201 / 100 * t₂ - 1 →
        ⌊100 * t₁⌋₊ = ⌊100 * t₂⌋₊ → ¬ t₁ < t₂ := by
      intro t₁ t₂ h1 h2 e1 e2 hfl h12
      have hk : ⌊100 * t₁⌋₊ < 99 :=
        (Nat.floor_lt (by linarith)).mpr (by exact_mod_cast (bd t₁ h1 e1).2)
      refine uniq _ hk t₁ t₂ (Nat.floor_le (by linarith)) h12 ?_ e1 e2
      rw [hfl]
      exact (Nat.lt_floor_add_one _).le
    intro t₁ t₂ h1 h2 e1 e2 hfl
    rcases lt_trichotomy t₁ t₂ with h | h | h
    · exact absurd h (aux t₁ t₂ h1 h2 e1 e2 hfl)
    · exact h
    · exact absurd h (aux t₂ t₁ h2 h1 e2 e1 hfl.symm)
  -- count: x ↦ ⌊100 x²⌋ (+ 99 if x ≤ 0) is a bijection onto {0, …, 197}
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℕ,
      ∀ x, ψ x = ⌊100 * x ^ 2⌋₊ + (if 0 < x then 0 else 99) := ⟨_, fun _ => rfl⟩
  have hfl : ∀ x : ℝ, Real.cos (100 * Real.pi * x ^ 2) = 201 / 100 * x ^ 2 - 1 →
      ⌊100 * x ^ 2⌋₊ < 99 := fun x hx =>
    (Nat.floor_lt (by positivity)).mpr (by exact_mod_cast (bd _ (sq_nonneg x) hx).2)
  have hinj : Set.InjOn ψ
      {x : ℝ | Real.cos (100 * Real.pi * x ^ 2) = 201 / 100 * x ^ 2 - 1} := by
    intro x hx y hy hxy
    have hx : Real.cos (100 * Real.pi * x ^ 2) = 201 / 100 * x ^ 2 - 1 := hx
    have hy : Real.cos (100 * Real.pi * y ^ 2) = 201 / 100 * y ^ 2 - 1 := hy
    rw [hψ, hψ] at hxy
    have fx := hfl x hx
    have fy := hfl y hy
    rcases lt_or_ge 0 x with px | px <;> rcases lt_or_ge 0 y with py | py
    · have ix : (if 0 < x then 0 else 99) = 0 := by simp [px]
      have iy : (if 0 < y then 0 else 99) = 0 := by simp [py]
      rw [ix, iy] at hxy
      have hsq := tinj _ _ (sq_nonneg x) (sq_nonneg y) hx hy (by omega)
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · exact h
      · linarith
    · have ix : (if 0 < x then 0 else 99) = 0 := by simp [px]
      have iy : (if 0 < y then 0 else 99) = 99 := by simp [not_lt.mpr py]
      rw [ix, iy] at hxy
      omega
    · have ix : (if 0 < x then 0 else 99) = 99 := by simp [not_lt.mpr px]
      have iy : (if 0 < y then 0 else 99) = 0 := by simp [py]
      rw [ix, iy] at hxy
      omega
    · have ix : (if 0 < x then 0 else 99) = 99 := by simp [not_lt.mpr px]
      have iy : (if 0 < y then 0 else 99) = 99 := by simp [not_lt.mpr py]
      rw [ix, iy] at hxy
      have hsq := tinj _ _ (sq_nonneg x) (sq_nonneg y) hx hy (by omega)
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · exact h
      · linarith
  have himg : ψ '' {x : ℝ | Real.cos (100 * Real.pi * x ^ 2) = 201 / 100 * x ^ 2 - 1}
      = (Finset.range 198 : Set ℕ) := by
    ext n
    rw [Finset.mem_coe, Finset.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx : Real.cos (100 * Real.pi * x ^ 2) = 201 / 100 * x ^ 2 - 1 := hx
      rw [hψ]
      have := hfl x hx
      split_ifs <;> omega
    · intro hn
      rcases lt_or_ge n 99 with h | h
      · obtain ⟨t, t1, t2, te⟩ := ex n h
        have t0 : 0 < t := by
          have := Nat.cast_nonneg (α := ℝ) n
          linarith
        have ix : (if 0 < Real.sqrt t then 0 else 99) = 0 := by
          simp [Real.sqrt_pos.mpr t0]
        refine ⟨Real.sqrt t, ?_, ?_⟩
        · show Real.cos (100 * Real.pi * Real.sqrt t ^ 2) = 201 / 100 * Real.sqrt t ^ 2 - 1
          rw [Real.sq_sqrt t0.le]; exact te
        · rw [hψ, Real.sq_sqrt t0.le, ix, add_zero]
          exact (Nat.floor_eq_iff (by linarith)).mpr ⟨t1.le, t2⟩
      · obtain ⟨t, t1, t2, te⟩ := ex (n - 99) (by omega)
        have t0 : 0 < t := by
          have := Nat.cast_nonneg (α := ℝ) (n - 99)
          linarith
        have ix : (if 0 < -Real.sqrt t then 0 else 99) = 99 := by
          have h1 := Real.sqrt_pos.mpr t0
          have h2 : ¬ (0 < -Real.sqrt t) := by linarith
          simp [h2]
        refine ⟨-Real.sqrt t, ?_, ?_⟩
        · show Real.cos (100 * Real.pi * (-Real.sqrt t) ^ 2) = 201 / 100 * (-Real.sqrt t) ^ 2 - 1
          rw [neg_sq, Real.sq_sqrt t0.le]; exact te
        · rw [hψ, neg_sq, Real.sq_sqrt t0.le, ix]
          have : ⌊100 * t⌋₊ = n - 99 := (Nat.floor_eq_iff (by linarith)).mpr ⟨t1.le, t2⟩
          omega
  have hcard : (ψ '' {x : ℝ | Real.cos (100 * Real.pi * x ^ 2) = 201 / 100 * x ^ 2 - 1}).ncard
      = {x : ℝ | Real.cos (100 * Real.pi * x ^ 2) = 201 / 100 * x ^ 2 - 1}.ncard := by
    first
      | exact Set.ncard_image_of_injOn hinj
      | exact hinj.ncard_image
  rw [← hcard, himg]
  first
    | exact (Set.ncard_coe_finset _).trans (Finset.card_range 198)
    | exact (Set.ncard_coe_Finset _).trans (Finset.card_range 198)
```
