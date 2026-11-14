# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `14 November 2026`\
Line count: `202`\
Turn count: `1`

## Solution

```lean4
import Mathlib

def curve : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | 3 * p.2 ^ 2 = Real.sin (9 * p.1 * p.2) + p.1 / Real.pi - 7 * p.2 }

def circle (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 = r ^ 2 }

theorem curve_circle_intersections_not_bounded_above :
    ¬ ∃ N : ℕ, ∀ (c : ℝ × ℝ) (r : ℝ), r > 0 → (circle c r ∩ curve).encard ≤ N := by
  rintro ⟨N, hN⟩
  have hpi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by linarith
  -- the circle: centre `(c1, c2)`, radius `r`
  obtain ⟨c2, hc2⟩ : ∃ c2 : ℝ, c2 = (N : ℝ) + 2 := ⟨_, rfl⟩
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hc2pos : 2 ≤ c2 := by linarith
  have h8 : (0 : ℝ) < 8 + 6 * c2 := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / (8 + 6 * c2) := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hr]; exact one_div_pos.mpr h8
  have hr8 : r * (8 + 6 * c2) = 1 := by
    rw [hr, one_div, inv_mul_cancel₀ h8.ne']
  have hr1 : r < 1 := by nlinarith
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = Real.pi * (7 * c2 + 3 * c2 ^ 2) := ⟨_, rfl⟩
  have hc1pos : 0 < c1 := by
    rw [hc1]; exact mul_pos hpi0 (by nlinarith)
  -- the arc `y ↦ (X y, y)` for `y ∈ [c2 - r, c2]`
  obtain ⟨X, hX⟩ : ∃ X : ℝ → ℝ, ∀ y, X y = c1 + Real.sqrt (r ^ 2 - (y - c2) ^ 2) :=
    ⟨_, fun _ => rfl⟩
  have hXc : Continuous X := by
    have : X = fun y => c1 + Real.sqrt (r ^ 2 - (y - c2) ^ 2) := funext hX
    rw [this]; fun_prop
  have hI : ∀ y, y ∈ Set.Icc (c2 - r) c2 → 0 ≤ r ^ 2 - (y - c2) ^ 2 := by
    rintro y ⟨h1, h2⟩
    have := mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ r + c2 - y)
    nlinarith [this]
  have hXlo : ∀ y, c1 ≤ X y := fun y => by
    rw [hX]; linarith [Real.sqrt_nonneg (r ^ 2 - (y - c2) ^ 2)]
  have hXhi : ∀ y, X y ≤ c1 + r := fun y => by
    rw [hX]
    have : Real.sqrt (r ^ 2 - (y - c2) ^ 2) ≤ r :=
      Real.sqrt_le_iff.mpr ⟨hrpos.le, by nlinarith [sq_nonneg (y - c2)]⟩
    linarith
  have hXcirc : ∀ y, y ∈ Set.Icc (c2 - r) c2 → (X y - c1) ^ 2 + (y - c2) ^ 2 = r ^ 2 := by
    intro y hy
    rw [hX, add_sub_cancel_left, Real.sq_sqrt (hI y hy)]
    ring
  have hXmono : ∀ y y', y ∈ Set.Icc (c2 - r) c2 → y' ∈ Set.Icc (c2 - r) c2 → y ≤ y' →
      X y ≤ X y' := by
    rintro y y' ⟨h1, h2⟩ ⟨h1', h2'⟩ hyy
    rw [hX, hX]
    have : Real.sqrt (r ^ 2 - (y - c2) ^ 2) ≤ Real.sqrt (r ^ 2 - (y' - c2) ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [mul_nonneg (sub_nonneg.2 hyy) (by linarith : (0 : ℝ) ≤ 2 * c2 - y - y')]
    linarith
  have hφmono : ∀ y y', y ∈ Set.Icc (c2 - r) c2 → y' ∈ Set.Icc (c2 - r) c2 → y ≤ y' →
      9 * X y * y ≤ 9 * X y' * y' := by
    intro y y' hy hy' hyy
    have h1 := hXmono y y' hy hy' hyy
    have h2 : 0 ≤ y := by linarith [hy.1]
    have h3 : 0 ≤ X y' := by linarith [hXlo y']
    have := mul_le_mul h1 hyy h2 h3
    linarith
  -- on the arc, the non-oscillating part lies in `[0, 1)`
  have hh : ∀ y, y ∈ Set.Icc (c2 - r) c2 →
      0 ≤ X y / Real.pi - 7 * y - 3 * y ^ 2 ∧ X y / Real.pi - 7 * y - 3 * y ^ 2 < 1 := by
    rintro y ⟨h1, h2⟩
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = X y / Real.pi := ⟨_, rfl⟩
    have hux : u * Real.pi = X y := by rw [hu, div_mul_cancel₀ _ hpi0.ne']
    rw [← hu]
    have hlo := hXlo y
    have hhi := hXhi y
    have hA : 7 * c2 + 3 * c2 ^ 2 ≤ u := by
      by_contra hcon
      have hcon := not_le.mp hcon
      have := mul_lt_mul_of_pos_right hcon hpi0
      nlinarith
    have hB : u ≤ 7 * c2 + 3 * c2 ^ 2 + r / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hA) (by linarith : (0 : ℝ) ≤ Real.pi - 2)]
    have hy0 : 0 < y := by linarith
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ 7 + 3 * (c2 + y))]
    · nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ 7 + 3 * (y + c2 - r)),
        sq_nonneg r]
  -- the phase `9 * X y * y` sweeps more than `N + 2` periods along the arc
  have hXa : X (c2 - r) = c1 := by
    rw [hX]
    have : r ^ 2 - (c2 - r - c2) ^ 2 = 0 := by ring
    rw [this, Real.sqrt_zero, add_zero]
  have hXb : X c2 = c1 + r := by
    rw [hX]
    have : r ^ 2 - (c2 - c2) ^ 2 = r ^ 2 := by ring
    rw [this, Real.sqrt_sq hrpos.le]
  have hab : c2 - r ≤ c2 := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 9 * X (c2 - r) * (c2 - r) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hL, hXa]
    have : 0 ≤ c1 * (c2 - r) := mul_nonneg hc1pos.le (by linarith)
    linarith
  have hgap : L + 2 * Real.pi * ((N : ℝ) + 2) ≤ 9 * X c2 * c2 := by
    rw [hL, ← hc2, hXa, hXb]
    have e : c2 = r * (8 * c2 + 6 * c2 ^ 2) := by linear_combination (-c2) * hr8
    have h3 : c2 ≤ 3 * (r * (7 * c2 + 3 * c2 ^ 2)) := by
      nlinarith [mul_nonneg hrpos.le (by nlinarith : (0 : ℝ) ≤ 13 * c2 + 3 * c2 ^ 2)]
    have h4 : Real.pi * c2 ≤ 3 * (r * c1) := by
      rw [hc1]
      nlinarith [mul_le_mul_of_nonneg_left h3 hpi0.le]
    nlinarith [mul_pos hrpos (by linarith : (0 : ℝ) < c2),
      mul_pos hpi0 (by linarith : (0 : ℝ) < c2)]
  obtain ⟨k0, hk1, hk2⟩ : ∃ k0 : ℕ, L ≤ k0 * (2 * Real.pi) ∧
      (k0 : ℝ) * (2 * Real.pi) < L + 2 * Real.pi := by
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = L / (2 * Real.pi) := ⟨_, rfl⟩
    have hqL : q * (2 * Real.pi) = L := by
      rw [hq, div_mul_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)]
    have hq0 : 0 ≤ q := by rw [hq]; exact div_nonneg hL0 h2pi
    refine ⟨⌈q⌉₊, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_right (Nat.le_ceil q) h2pi
      linarith
    · have := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one hq0)
        (by positivity : (0 : ℝ) < 2 * Real.pi)
      linarith
  have hgc : Continuous
      (fun y => Real.sin (9 * X y * y) + X y / Real.pi - 7 * y - 3 * y ^ 2) := by
    fun_prop
  have hφc : Continuous (fun y => 9 * X y * y) := by fun_prop
  -- one intersection point per period
  have key : ∀ j : Fin (N + 1), ∃ z : ℝ, z ∈ Set.Icc (c2 - r) c2 ∧
      Real.sin (9 * X z * z) + X z / Real.pi - 7 * z - 3 * z ^ 2 = 0 ∧
      Real.pi / 2 + ((k0 + (j : ℕ) : ℕ) : ℝ) * (2 * Real.pi) ≤ 9 * X z * z ∧
      9 * X z * z ≤ Real.pi / 2 + ((k0 + (j : ℕ) : ℕ) : ℝ) * (2 * Real.pi) + Real.pi := by
    intro j
    obtain ⟨T, hT⟩ :
        ∃ T : ℝ, T = Real.pi / 2 + ((k0 + (j : ℕ) : ℕ) : ℝ) * (2 * Real.pi) := ⟨_, rfl⟩
    rw [← hT]
    have hj : ((j : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp j.2
    have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    have hT1 : L ≤ T := by
      rw [hT]; push_cast
      nlinarith [mul_nonneg hj0 hpi0.le]
    have hT2 : T + Real.pi ≤ 9 * X c2 * c2 := by
      rw [hT]; push_cast
      nlinarith [mul_le_mul_of_nonneg_right hj hpi0.le]
    have hsin1 : Real.sin T = 1 := by
      rw [hT, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
    have hsin2 : Real.sin (T + Real.pi) = -1 := by
      rw [Real.sin_add_pi, hsin1]
    obtain ⟨a, ha, hφa⟩ : T ∈ (fun y => 9 * X y * y) '' Set.Icc (c2 - r) c2 :=
      intermediate_value_Icc hab hφc.continuousOn
        ⟨by rw [← hL]; exact hT1, by linarith⟩
    obtain ⟨b, hb, hφb⟩ : T + Real.pi ∈ (fun y => 9 * X y * y) '' Set.Icc (c2 - r) c2 :=
      intermediate_value_Icc hab hφc.continuousOn
        ⟨by rw [← hL]; linarith, hT2⟩
    have hφa : 9 * X a * a = T := hφa
    have hφb : 9 * X b * b = T + Real.pi := hφb
    have hale : a ≤ b := by
      by_contra hcon
      have hcon := not_le.mp hcon
      have := hφmono b a hb ha hcon.le
      linarith
    have hga : 0 ≤ Real.sin (9 * X a * a) + X a / Real.pi - 7 * a - 3 * a ^ 2 := by
      rw [hφa, hsin1]; linarith [(hh a ha).1]
    have hgb : Real.sin (9 * X b * b) + X b / Real.pi - 7 * b - 3 * b ^ 2 ≤ 0 := by
      rw [hφb, hsin2]; linarith [(hh b hb).2]
    obtain ⟨z, hz, hgz⟩ : (0 : ℝ) ∈
        (fun y => Real.sin (9 * X y * y) + X y / Real.pi - 7 * y - 3 * y ^ 2) '' Set.Icc a b :=
      intermediate_value_Icc' hale hgc.continuousOn ⟨hgb, hga⟩
    have hzI : z ∈ Set.Icc (c2 - r) c2 := ⟨ha.1.trans hz.1, hz.2.trans hb.2⟩
    refine ⟨z, hzI, hgz, ?_, ?_⟩
    · rw [← hφa]; exact hφmono a z ha hzI hz.1
    · rw [← hφb]; exact hφmono z b hzI hb hz.2
  choose z hzI hzg hzlo hzhi using key
  have hzne : ∀ i j : Fin (N + 1), i < j → z i ≠ z j := by
    intro i j hij heq
    have h1 := hzhi i
    have h2 := hzlo j
    rw [heq] at h1
    have hc : ((k0 + (i : ℕ) : ℕ) : ℝ) + 1 ≤ ((k0 + (j : ℕ) : ℕ) : ℝ) := by
      have : k0 + (i : ℕ) + 1 ≤ k0 + (j : ℕ) := by
        have := Fin.lt_def.mp hij
        omega
      exact_mod_cast this
    nlinarith [mul_le_mul_of_nonneg_right hc h2pi]
  have hinj : Function.Injective (fun j : Fin (N + 1) => ((X (z j), z j) : ℝ × ℝ)) := by
    intro i j hij
    have hz : z i = z j := congrArg Prod.snd hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hz (hzne i j h)
    · exact h
    · exact absurd hz.symm (hzne j i h)
  have hsub : Set.range (fun j : Fin (N + 1) => ((X (z j), z j) : ℝ × ℝ)) ⊆
      circle (c1, c2) r ∩ curve := by
    rintro _ ⟨j, rfl⟩
    refine ⟨hXcirc (z j) (hzI j), ?_⟩
    show 3 * (z j) ^ 2 = Real.sin (9 * X (z j) * z j) + X (z j) / Real.pi - 7 * z j
    linarith [hzg j]
  have h1 := hN (c1, c2) r hrpos
  have h2 := Set.encard_le_encard hsub
  rw [hinj.encard_range, ENat.card_eq_coe_fintype_card, Fintype.card_fin] at h2
  have h3 : ((N + 1 : ℕ) : ℕ∞) ≤ (N : ℕ∞) := h2.trans h1
  have h4 : N + 1 ≤ N := by exact_mod_cast h3
  omega
```
