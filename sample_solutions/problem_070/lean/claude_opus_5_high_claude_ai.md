# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `21 August 2026`\
Line count: `258`\
Turn count: `4`

## Solution

```lean4
import Mathlib

open MeasureTheory

namespace IntegralSgnSinAux

noncomputable def sgnF (x : ℝ) : ℝ :=
  x * Real.sign (Real.sin (3 * x)) * Real.sign (Real.sin (11 * x ^ 2))

noncomputable def brk (k : ℕ) : ℝ := Real.sqrt ((k : ℝ) * Real.pi / 11)

lemma sq_le_sq_imp {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u ^ 2 ≤ v ^ 2) : u ≤ v := by
  nlinarith

lemma brk_nonneg (k : ℕ) : 0 ≤ brk k := Real.sqrt_nonneg _

lemma brk_sq (k : ℕ) : brk k ^ 2 = (k : ℝ) * Real.pi / 11 :=
  Real.sq_sqrt (div_nonneg (mul_nonneg (Nat.cast_nonneg k) Real.pi_pos.le) (by norm_num))

lemma brk_sq_succ (k : ℕ) : brk (k + 1) ^ 2 = ((k : ℝ) + 1) * Real.pi / 11 := by
  have h := brk_sq (k + 1)
  push_cast at h
  exact h

lemma brk_mono {m n : ℕ} (h : m ≤ n) : brk m ≤ brk n := by
  refine sq_le_sq_imp (brk_nonneg m) (brk_nonneg n) ?_
  rw [brk_sq, brk_sq]
  have h1 : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr h
  have h2 := Real.pi_pos
  nlinarith

lemma sin_add_nat_pi (w : ℝ) (k : ℕ) :
    Real.sin (w + (k : ℝ) * Real.pi) = (-1 : ℝ) ^ k * Real.sin w := by
  induction k with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [show w + ((n : ℝ) + 1) * Real.pi = w + (n : ℝ) * Real.pi + Real.pi from by ring,
      Real.sin_add, Real.sin_pi, Real.cos_pi, ih]
    ring

lemma signSin (k : ℕ) (z : ℝ) (h1 : (k : ℝ) * Real.pi < z)
    (h2 : z < ((k : ℝ) + 1) * Real.pi) : Real.sign (Real.sin z) = (-1 : ℝ) ^ k := by
  have hz1 : 0 < z - (k : ℝ) * Real.pi := by linarith
  have hz2 : z - (k : ℝ) * Real.pi < Real.pi := by linarith
  have hs : 0 < Real.sin (z - (k : ℝ) * Real.pi) := Real.sin_pos_of_pos_of_lt_pi hz1 hz2
  have he : Real.sin z = (-1 : ℝ) ^ k * Real.sin (z - (k : ℝ) * Real.pi) := by
    have h := sin_add_nat_pi (z - (k : ℝ) * Real.pi) k
    rw [show z - (k : ℝ) * Real.pi + (k : ℝ) * Real.pi = z from by ring] at h
    exact h
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow] at he ⊢
    rw [he, one_mul, Real.sign_of_pos hs]
  · rw [hk.neg_one_pow] at he ⊢
    rw [he, Real.sign_of_neg (by linarith)]

lemma aeNe (b : ℝ) : ∀ᵐ x : ℝ, x ≠ b := by
  have h : {x : ℝ | ¬ (x ≠ b)} = {b} := by ext y; simp
  rw [MeasureTheory.ae_iff, h]
  simp

lemma pieceBase {a b c : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Set.Ioo a b, sgnF x = c * x) :
    IntervalIntegrable sgnF volume a b ∧
      (∫ x in a..b, sgnF x) = c * (b ^ 2 - a ^ 2) / 2 := by
  have hcont : Continuous fun x : ℝ => c * x := by exact continuous_const.mul continuous_id
  have hg : IntervalIntegrable (fun x : ℝ => c * x) volume a b := hcont.intervalIntegrable a b
  have hgo : Integrable (fun x : ℝ => c * x) (volume.restrict (Set.Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hg
  have hae0 : ∀ᵐ x : ℝ, x ∈ Set.Ioc a b → sgnF x = c * x := by
    filter_upwards [aeNe b] with x hx hmem
    exact h x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩
  have hae : sgnF =ᵐ[volume.restrict (Set.Ioc a b)] fun x : ℝ => c * x :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr hae0
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hgo.congr hae.symm), ?_⟩
  have heq : (∫ x in a..b, sgnF x) = ∫ x in a..b, c * x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [aeNe b] with x hx hmem
    rw [Set.uIoc_of_le hab] at hmem
    exact h x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩
  rw [heq, intervalIntegral.integral_const_mul, integral_id]
  ring

lemma pieceSame (a : ℝ) :
    IntervalIntegrable sgnF volume a a ∧ (∫ x in a..a, sgnF x) = 0 := by
  have h := pieceBase (a := a) (b := a) (c := 0) le_rfl
    (fun x hx => absurd (hx.1.trans hx.2) (lt_irrefl a))
  exact ⟨h.1, by rw [h.2]; ring⟩

lemma pieceGen (a b : ℝ) (j k : ℕ) (ha : 0 ≤ a) (hab : a ≤ b)
    (h1 : ((j : ℝ) * Real.pi) ^ 2 ≤ 9 * a ^ 2)
    (h2 : 9 * b ^ 2 ≤ (((j : ℝ) + 1) * Real.pi) ^ 2)
    (h3 : (k : ℝ) * Real.pi ≤ 11 * a ^ 2)
    (h4 : 11 * b ^ 2 ≤ ((k : ℝ) + 1) * Real.pi) :
    IntervalIntegrable sgnF volume a b ∧
      (∫ x in a..b, sgnF x) = (-1 : ℝ) ^ (j + k) * (b ^ 2 - a ^ 2) / 2 := by
  have hpi := Real.pi_pos
  have hb : 0 ≤ b := le_trans ha hab
  have hjA : (j : ℝ) * Real.pi ≤ 3 * a :=
    sq_le_sq_imp (mul_nonneg (Nat.cast_nonneg j) hpi.le) (by linarith) (by nlinarith)
  have hjB : 3 * b ≤ ((j : ℝ) + 1) * Real.pi :=
    sq_le_sq_imp (by linarith) (mul_nonneg (by positivity) hpi.le) (by nlinarith)
  refine pieceBase hab ?_
  intro x hx
  have hx1 := hx.1
  have hx2 := hx.2
  have hx0 : 0 ≤ x := le_trans ha hx1.le
  have e1 : Real.sign (Real.sin (3 * x)) = (-1 : ℝ) ^ j :=
    signSin j (3 * x) (by linarith) (by linarith)
  have e2 : Real.sign (Real.sin (11 * x ^ 2)) = (-1 : ℝ) ^ k :=
    signSin k (11 * x ^ 2) (by nlinarith) (by nlinarith)
  simp only [sgnF, e1, e2, pow_add]
  ring

lemma pieceStep (j k : ℕ)
    (h1 : ((j : ℝ) * Real.pi) ^ 2 ≤ 9 * ((k : ℝ) * Real.pi / 11))
    (h2 : 9 * (((k : ℝ) + 1) * Real.pi / 11) ≤ (((j : ℝ) + 1) * Real.pi) ^ 2) :
    IntervalIntegrable sgnF volume (brk k) (brk (k + 1)) ∧
      (∫ x in brk k..brk (k + 1), sgnF x) = (-1 : ℝ) ^ (j + k) * (Real.pi / 11) / 2 := by
  have hs1 := brk_sq k
  have hs2 := brk_sq_succ k
  have H := pieceGen (brk k) (brk (k + 1)) j k (brk_nonneg k) (brk_mono (Nat.le_succ k))
    (by rw [hs1]; exact h1) (by rw [hs2]; exact h2)
    (by rw [hs1]; linarith) (by rw [hs2]; linarith)
  refine ⟨H.1, ?_⟩
  rw [H.2, hs1, hs2]
  ring

lemma pieceRun (j m : ℕ) (h1 : ((j : ℝ) * Real.pi) ^ 2 ≤ 9 * ((m : ℝ) * Real.pi / 11)) :
    ∀ n : ℕ, m ≤ n → 9 * ((n : ℝ) * Real.pi / 11) ≤ (((j : ℝ) + 1) * Real.pi) ^ 2 →
      IntervalIntegrable sgnF volume (brk m) (brk n) ∧
        (∫ x in brk m..brk n, sgnF x) =
          (-1 : ℝ) ^ j * ((-1 : ℝ) ^ m - (-1 : ℝ) ^ n) / 2 * (Real.pi / 11) / 2 := by
  intro n hmn
  induction n, hmn using Nat.le_induction with
  | base =>
    intro _
    refine ⟨(pieceSame (brk m)).1, ?_⟩
    rw [(pieceSame (brk m)).2]
    ring
  | succ p hp ih =>
    intro h2
    have hpi := Real.pi_pos
    push_cast at h2
    have h2p : 9 * ((p : ℝ) * Real.pi / 11) ≤ (((j : ℝ) + 1) * Real.pi) ^ 2 := by linarith
    obtain ⟨hi1, he1⟩ := ih h2p
    have hmp : (m : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp
    have h1p : ((j : ℝ) * Real.pi) ^ 2 ≤ 9 * ((p : ℝ) * Real.pi / 11) := by nlinarith
    obtain ⟨hi2, he2⟩ := pieceStep j p h1p h2
    refine ⟨hi1.trans hi2, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, he1, he2, pow_succ, pow_add]
    ring

lemma glueI {a b c v w : ℝ}
    (H1 : IntervalIntegrable sgnF volume a b ∧ (∫ x in a..b, sgnF x) = v)
    (H2 : IntervalIntegrable sgnF volume b c ∧ (∫ x in b..c, sgnF x) = w) :
    IntervalIntegrable sgnF volume a c ∧ (∫ x in a..c, sgnF x) = v + w := by
  refine ⟨H1.1.trans H2.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals H1.1 H2.1, H1.2, H2.2]

/-! ### Self-contained numerical bounds on `π` -/

lemma cube_le {t C : ℝ} (ht : 0 ≤ t) (h : t ≤ C) : t ^ 3 ≤ C ^ 2 * t := by
  have hC : 0 ≤ C := le_trans ht h
  nlinarith [mul_nonneg (mul_nonneg ht (sub_nonneg.mpr h)) (add_nonneg ht hC)]

lemma quint_le {t C : ℝ} (ht : 0 ≤ t) (h : t ≤ C) : t ^ 5 ≤ C ^ 4 * t := by
  have hC : 0 ≤ C := le_trans ht h
  have e2 : t ^ 2 ≤ C ^ 2 := by nlinarith
  have e4 : t ^ 4 ≤ C ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr e2) (add_nonneg (sq_nonneg t) (sq_nonneg C))]
  nlinarith [mul_nonneg (sub_nonneg.mpr e4) ht]

lemma pi_est (t : ℝ) (ht0 : 0 < t) (htu : t ≤ 2 / 3) (hs : Real.sin t = 1 / 2) :
    31 / 60 < t ∧ t ≤ 53 / 100 := by
  have habs : |t| ≤ 1 := by rw [abs_of_pos ht0]; linarith
  have hb := Real.sin_bound habs
  rw [hs] at hb
  rw [abs_of_pos ht0] at hb
  rw [abs_le] at hb
  obtain ⟨hb1, hb2⟩ := hb
  have hu1 : t ≤ 11 / 20 := by
    have c1 := cube_le ht0.le htu
    have q1 := quint_le ht0.le htu
    linarith
  have hu2 : t ≤ 53 / 100 := by
    have c2 := cube_le ht0.le hu1
    have q2 := quint_le ht0.le hu1
    linarith
  refine ⟨?_, hu2⟩
  have cl : (3 / 4) * t - 1 / 4 ≤ t ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (t - 1 / 2)) (by linarith : (0:ℝ) ≤ t + 1)]
  have q3 := quint_le ht0.le hu2
  linarith

end IntegralSgnSinAux

open IntegralSgnSinAux in
theorem integral_sgn_sin :
    ∫ x in (0)..Real.pi,
      x * Real.sign (Real.sin (3 * x)) * Real.sign (Real.sin (11 * x ^ 2)) =
      (5 * Real.pi ^ 2) / 6 - (29 * Real.pi) / 11 := by
  have hpi := Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hE := pi_est (Real.pi / 6) (by linarith) (by linarith) Real.sin_pi_div_six
  have hpiL : (31 / 10 : ℝ) < Real.pi := by linarith [hE.1]
  have hpiH : Real.pi ≤ (159 / 50 : ℝ) := by linarith [hE.2]
  have hsqL : (31 / 10 : ℝ) * Real.pi < Real.pi ^ 2 := by
    nlinarith [mul_pos hpi (sub_pos.mpr hpiL)]
  have hsqH : Real.pi ^ 2 ≤ (159 / 50 : ℝ) * Real.pi := by
    nlinarith [mul_nonneg hpi.le (sub_nonneg.mpr hpiH)]
  have hb0 : brk 0 = 0 := by simp [brk]
  have hb3 : brk 3 ^ 2 = 3 * Real.pi / 11 := by rw [brk_sq]; norm_num
  have hb4 : brk 4 ^ 2 = 4 * Real.pi / 11 := by rw [brk_sq]; norm_num
  have hb15 : brk 15 ^ 2 = 15 * Real.pi / 11 := by rw [brk_sq]; norm_num
  have hb16 : brk 16 ^ 2 = 16 * Real.pi / 11 := by rw [brk_sq]; norm_num
  have hb34 : brk 34 ^ 2 = 34 * Real.pi / 11 := by rw [brk_sq]; norm_num
  have o1 : brk 3 ≤ Real.pi / 3 :=
    sq_le_sq_imp (brk_nonneg 3) (by linarith) (by rw [hb3]; linarith)
  have o2 : Real.pi / 3 ≤ brk 4 :=
    sq_le_sq_imp (by linarith) (brk_nonneg 4) (by rw [hb4]; linarith)
  have o3 : brk 15 ≤ 2 * Real.pi / 3 :=
    sq_le_sq_imp (brk_nonneg 15) (by linarith) (by rw [hb15]; linarith)
  have o4 : 2 * Real.pi / 3 ≤ brk 16 :=
    sq_le_sq_imp (by linarith) (brk_nonneg 16) (by rw [hb16]; linarith)
  have o5 : brk 34 ≤ Real.pi :=
    sq_le_sq_imp (brk_nonneg 34) hpi.le (by rw [hb34]; linarith)
  have P1 := pieceRun 0 0 (by push_cast <;> linarith) 3 (by norm_num)
    (by push_cast <;> linarith)
  have P2 := pieceGen (brk 3) (Real.pi / 3) 0 3 (brk_nonneg 3) o1
    (by rw [hb3] <;> push_cast <;> linarith) (by push_cast <;> linarith)
    (by rw [hb3] <;> push_cast <;> linarith) (by push_cast <;> linarith)
  have P3 := pieceGen (Real.pi / 3) (brk 4) 1 3 (by linarith) o2
    (by push_cast <;> linarith) (by rw [hb4] <;> push_cast <;> linarith)
    (by push_cast <;> linarith) (by rw [hb4] <;> push_cast <;> linarith)
  have P4 := pieceRun 1 4 (by push_cast <;> linarith) 15 (by norm_num)
    (by push_cast <;> linarith)
  have P5 := pieceGen (brk 15) (2 * Real.pi / 3) 1 15 (brk_nonneg 15) o3
    (by rw [hb15] <;> push_cast <;> linarith) (by push_cast <;> linarith)
    (by rw [hb15] <;> push_cast <;> linarith) (by push_cast <;> linarith)
  have P6 := pieceGen (2 * Real.pi / 3) (brk 16) 2 15 (by linarith) o4
    (by push_cast <;> linarith) (by rw [hb16] <;> push_cast <;> linarith)
    (by push_cast <;> linarith) (by rw [hb16] <;> push_cast <;> linarith)
  have P7 := pieceRun 2 16 (by push_cast <;> linarith) 34 (by norm_num)
    (by push_cast <;> linarith)
  have P8 := pieceGen (brk 34) Real.pi 2 34 (brk_nonneg 34) o5
    (by rw [hb34] <;> push_cast <;> linarith) (by push_cast <;> linarith)
    (by rw [hb34] <;> push_cast <;> linarith) (by push_cast <;> linarith)
  have G := glueI (glueI (glueI (glueI (glueI (glueI (glueI P1 P2) P3) P4) P5) P6) P7) P8
  rw [hb0] at G
  have key : (∫ x in (0:ℝ)..Real.pi, sgnF x) = 5 * Real.pi ^ 2 / 6 - 29 * Real.pi / 11 := by
    rw [G.2, hb3, hb4, hb15, hb16, hb34]
    first
      | (norm_num <;> ring)
      | (ring_nf <;> norm_num)
      | ring
  first
    | exact key
    | simpa only [sgnF] using key
```
