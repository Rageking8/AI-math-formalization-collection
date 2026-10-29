# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `13 August 2026`\
Line count: `318`\
Turn count: `4`

## Solution

```lean4
import Mathlib

private lemma plog_one_le_pow {t : ℝ} (ht : 1 ≤ t) (n : ℕ) : 1 ≤ t ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith

private lemma plog_pow_le_pow {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) : s ^ n ≤ t ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : (0:ℝ) ≤ s ^ k := pow_nonneg hs k
    have h2 : (0:ℝ) ≤ t ^ k := le_trans h1 ih
    rw [pow_succ, pow_succ]
    nlinarith

private lemma plog_pow_mono_exp {t : ℝ} (ht : 1 ≤ t) {m n : ℕ} (h : m ≤ n) : t ^ m ≤ t ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [pow_add]
  have h1 : (1:ℝ) ≤ t ^ k := plog_one_le_pow ht k
  have h2 : (0:ℝ) ≤ t ^ m := pow_nonneg (by linarith) m
  nlinarith

private lemma plog_pow_le_one {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) (n : ℕ) : y ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h2 : (0:ℝ) ≤ y ^ k := pow_nonneg h0 k
    rw [pow_succ]
    nlinarith

private lemma plog_odd_pow_nonpos {y : ℝ} (hy : y ≤ 0) {n : ℕ} (hn : Odd n) : y ^ n ≤ 0 := by
  obtain ⟨k, rfl⟩ := hn
  have h1 : y ^ (2 * k) = (y ^ k) ^ 2 := by rw [mul_comm 2 k, pow_mul]
  rw [pow_add, pow_one, h1]
  nlinarith [sq_nonneg (y ^ k)]

private lemma plog_logeq {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.log u = Real.log v ↔ u = v := by
  constructor
  · intro h
    have h2 := congrArg Real.exp h
    rwa [Real.exp_log hu, Real.exp_log hv] at h2
  · intro h; rw [h]

private lemma plog_pred_iff (a b : ℕ) (x : ℝ) :
    (0 < x ^ 3 + (a:ℝ) ∧ 0 < x ^ b - 3 * (a:ℝ) ∧
      Real.log (x ^ 3 + (a:ℝ)) = Real.log (x ^ b - 3 * (a:ℝ)))
      ↔ (0 < x ^ 3 + (a:ℝ) ∧ x ^ b = x ^ 3 + 4 * (a:ℝ)) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h4 := (plog_logeq h1 h2).mp h3
    exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    have h2' : (0:ℝ) < x ^ b - 3 * (a:ℝ) := by rw [h2]; linarith
    refine ⟨h1, h2', ?_⟩
    rw [plog_logeq h1 h2']
    linarith

private lemma plog_eu_congr {p q : ℝ → Prop} (h : ∀ x, p x ↔ q x) :
    (∃! x, p x) ↔ (∃! x, q x) := by
  constructor
  · rintro ⟨x, hx, hu⟩
    exact ⟨x, (h x).mp hx, fun y hy => hu y ((h y).mpr hy)⟩
  · rintro ⟨x, hx, hu⟩
    exact ⟨x, (h x).mpr hx, fun y hy => hu y ((h y).mp hy)⟩

private lemma plog_not_unique_of_two {P : ℝ → Prop} {x y : ℝ}
    (hx : P x) (hy : P y) (hxy : x ≠ y) : ¬ (∃! z, P z) := by
  rintro ⟨z, hz, hu⟩
  exact hxy ((hu x hx).trans (hu y hy).symm)

private lemma plog_mono_key {b : ℕ} (hb : 4 ≤ b) {s t : ℝ} (hs : 1 ≤ s) (hst : s < t) :
    s ^ b - s ^ 3 < t ^ b - t ^ 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, b = 3 + m := ⟨b - 3, by omega⟩
  have hm : 1 ≤ m := by omega
  have hs0 : (0:ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have ht0 : (0:ℝ) < t := lt_trans hs0 hst
  have ht1 : (1:ℝ) < t := lt_of_le_of_lt hs hst
  have h1 : s ^ 3 < t ^ 3 := by
    nlinarith [mul_pos (show (0:ℝ) < t - s by linarith)
      (show (0:ℝ) < t ^ 2 + t * s + s ^ 2 by
        nlinarith [mul_pos ht0 hs0, mul_pos ht0 ht0, mul_pos hs0 hs0])]
  have hs3 : (0:ℝ) < s ^ 3 := pow_pos hs0 3
  have h2 : s ^ m ≤ t ^ m := plog_pow_le_pow hs0.le hst.le m
  have h4 : (1:ℝ) < t ^ m := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h5 := plog_one_le_pow ht1.le m'
    rw [pow_succ]
    nlinarith
  rw [pow_add, pow_add]
  nlinarith [mul_le_mul_of_nonneg_left (sub_le_sub_right h2 1) hs3.le,
    mul_lt_mul_of_pos_right h1 (show (0:ℝ) < t ^ m - 1 by linarith)]

private lemma plog_pos_root {b : ℕ} (hb : 4 ≤ b) {A : ℝ} (hA : 1 ≤ A) :
    ∃ x : ℝ, 1 < x ∧ x ^ b - x ^ 3 = 4 * A := by
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 4 * A + 2 := ⟨_, rfl⟩
  have hT6 : (6:ℝ) ≤ T := by rw [hTdef]; linarith
  have h1T : (1:ℝ) ≤ T := by linarith
  have hcont : ContinuousOn (fun x : ℝ => x ^ b - x ^ 3) (Set.Icc 1 T) :=
    ((continuous_pow b).sub (continuous_pow 3)).continuousOn
  have hT3 : (36:ℝ) * T ≤ T ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ T by linarith)
      (show (0:ℝ) ≤ T - 6 by linarith)) (show (0:ℝ) ≤ T + 6 by linarith)]
  have hT4 : T ^ 4 ≤ T ^ b := plog_pow_mono_exp h1T hb
  have hfT : 4 * A ≤ T ^ b - T ^ 3 := by
    nlinarith [hT4, hT3, mul_nonneg (pow_nonneg (show (0:ℝ) ≤ T by linarith) 3)
      (show (0:ℝ) ≤ T - 6 by linarith)]
  have hmem : (4 * A : ℝ) ∈ Set.Icc ((1:ℝ) ^ b - (1:ℝ) ^ 3) (T ^ b - T ^ 3) := by
    constructor
    · rw [one_pow, one_pow]; linarith
    · exact hfT
  obtain ⟨x, hx, hxv⟩ := intermediate_value_Icc h1T hcont hmem
  have hxv' : x ^ b - x ^ 3 = 4 * A := hxv
  refine ⟨x, ?_, hxv'⟩
  rcases eq_or_lt_of_le hx.1 with h | h
  · exfalso
    rw [← h, one_pow, one_pow] at hxv'
    linarith
  · exact h

private lemma plog_neg_root {b : ℕ} (hb : 4 ≤ b) (hbe : Even b) {A t1 : ℝ} (ht1 : 0 < t1)
    (hlt : t1 ^ 3 < A) (hge : 4 * A ≤ t1 ^ b + t1 ^ 3) (hA : 0 < A) :
    ∃ x : ℝ, x ≤ 0 ∧ 0 < x ^ 3 + A ∧ x ^ b = x ^ 3 + 4 * A := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ b + t ^ 3) (Set.Icc 0 t1) :=
    ((continuous_pow b).add (continuous_pow 3)).continuousOn
  have h0b : (0:ℝ) ^ b = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, b = j + 1 := ⟨b - 1, by omega⟩
    rw [pow_succ, mul_zero]
  have h03 : (0:ℝ) ^ 3 = 0 := by norm_num
  have hmem : (4 * A : ℝ) ∈ Set.Icc ((0:ℝ) ^ b + (0:ℝ) ^ 3) (t1 ^ b + t1 ^ 3) := by
    constructor
    · rw [h0b, h03]; linarith
    · exact hge
  obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc ht1.le hcont hmem
  have hteq' : t ^ b + t ^ 3 = 4 * A := hteq
  have ht3 : t ^ 3 ≤ t1 ^ 3 := plog_pow_le_pow ht.1 ht.2 3
  refine ⟨-t, by linarith [ht.1], ?_, ?_⟩
  · have e2 : (-t) ^ 3 = - t ^ 3 := by ring
    rw [e2]; linarith
  · have e1 : (-t) ^ b = t ^ b := hbe.neg_pow t
    have e2 : (-t) ^ 3 = - t ^ 3 := by ring
    rw [e1, e2]; linarith

private lemma plog_even_not_unique {a b : ℕ} (hb : 4 ≤ b) (hbe : Even b) (ha : 1 ≤ a)
    {t1 : ℝ} (ht1 : 0 < t1) (hlt : t1 ^ 3 < (a:ℝ)) (hge : 4 * (a:ℝ) ≤ t1 ^ b + t1 ^ 3) :
    ¬ ∃! x : ℝ, 0 < x ^ 3 + (a:ℝ) ∧ x ^ b = x ^ 3 + 4 * (a:ℝ) := by
  have hA : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  obtain ⟨x0, hx0, hx0e⟩ := plog_pos_root hb hA
  obtain ⟨x1, hx1n, hx1a, hx1b⟩ := plog_neg_root hb hbe ht1 hlt hge (by linarith)
  apply plog_not_unique_of_two (x := x0) (y := x1)
  · refine ⟨?_, by linarith⟩
    have h : (0:ℝ) < x0 ^ 3 := pow_pos (by linarith) 3
    linarith
  · exact ⟨hx1a, hx1b⟩
  · intro h
    rw [h] at hx0
    linarith

private lemma plog_even_bad {a b : ℕ} (hb : 4 ≤ b) (he : Even b) (hab : a + b = 2026)
    (ha : 1 ≤ a) :
    ¬ ∃! x : ℝ, 0 < x ^ 3 + (a:ℝ) ∧ x ^ b = x ^ 3 + 4 * (a:ℝ) := by
  obtain ⟨r, hr⟩ := he
  have hb2024 : b ≤ 2024 := by omega
  have ha2 : 2 ≤ a := by omega
  have ha2022 : a ≤ 2022 := by omega
  have hAle : (a:ℝ) ≤ 2022 := by exact_mod_cast ha2022
  rcases le_or_gt b 60 with hbs | hbl
  · have ha1966 : 1966 ≤ a := by omega
    have hAge : (1966:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha1966
    refine plog_even_not_unique hb ⟨r, hr⟩ ha (t1 := 12) (by norm_num) ?_ ?_
    · have h12 : ((12:ℝ)) ^ 3 = 1728 := by norm_num
      rw [h12]; linarith
    · have h1 : ((12:ℝ)) ^ 4 ≤ (12:ℝ) ^ b := plog_pow_mono_exp (by norm_num) hb
      have h3 : (0:ℝ) ≤ (12:ℝ) ^ 3 := by positivity
      have h2 : ((12:ℝ)) ^ 4 = 20736 := by norm_num
      linarith
  · have hAge : (2:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha2
    refine plog_even_not_unique hb ⟨r, hr⟩ ha (t1 := 6/5) (by norm_num) ?_ ?_
    · have h12 : ((6/5:ℝ)) ^ 3 = 216/125 := by norm_num
      rw [h12]; linarith
    · have h1 : ((6/5:ℝ)) ^ 52 ≤ (6/5:ℝ) ^ b := plog_pow_mono_exp (by norm_num) (by omega)
      have h3 : (8088:ℝ) < (6/5:ℝ) ^ 52 := by norm_num
      have h4 : (0:ℝ) ≤ (6/5:ℝ) ^ 3 := by positivity
      linarith

private lemma plog_odd_case {a b : ℕ} (ha : 1 ≤ a) (hb : 5 ≤ b) (hbodd : Odd b) :
    ∃! x : ℝ, 0 < x ^ 3 + (a:ℝ) ∧ x ^ b = x ^ 3 + 4 * (a:ℝ) := by
  have hA : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  obtain ⟨x0, hx0, hx0e⟩ := plog_pos_root (show 4 ≤ b by omega) hA
  refine ⟨x0, ⟨?_, ?_⟩, ?_⟩
  · have h : (0:ℝ) < x0 ^ 3 := pow_pos (by linarith) 3
    linarith
  · linarith
  · rintro y ⟨hy1, hy2⟩
    have hyb : (3:ℝ) < y ^ b := by rw [hy2]; linarith
    have hypos : (0:ℝ) < y := by
      by_contra hcon
      push_neg at hcon
      have h := plog_odd_pow_nonpos hcon hbodd
      linarith
    have hy1' : (1:ℝ) < y := by
      by_contra hcon
      push_neg at hcon
      have h := plog_pow_le_one hypos.le hcon b
      linarith
    rcases lt_trichotomy y x0 with h | h | h
    · exfalso
      have hmm := plog_mono_key (show 4 ≤ b by omega) hy1'.le h
      linarith
    · exact h
    · exfalso
      have hmm := plog_mono_key (show 4 ≤ b by omega) hx0.le h
      linarith

private lemma plog_no_sol_b1 {a : ℕ} (ha : 1 ≤ a) :
    ¬ ∃ x : ℝ, 0 < x ^ 3 + (a:ℝ) ∧ x ^ 1 = x ^ 3 + 4 * (a:ℝ) := by
  rintro ⟨x, h1, h2⟩
  have hA : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  rw [pow_one] at h2
  have hx3 : (3:ℝ) < x := by linarith
  have hxx : (0:ℝ) < x * (x - 1) * (x + 1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  nlinarith [hxx]

private lemma plog_no_sol_b2 {a : ℕ} (ha : 1 ≤ a) :
    ¬ ∃ x : ℝ, 0 < x ^ 3 + (a:ℝ) ∧ x ^ 2 = x ^ 3 + 4 * (a:ℝ) := by
  rintro ⟨x, h1, h2⟩
  have hA : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  have hx2 : 3 * (a:ℝ) < x ^ 2 := by linarith
  rcases le_or_gt x 0 with hx | hx
  · have hxlt : x < -1 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_nonneg (show (0:ℝ) ≤ x + 1 by linarith) (show (0:ℝ) ≤ -x by linarith)]
    have hpos : (0:ℝ) < x ^ 2 := by linarith
    nlinarith [mul_pos hpos (show (0:ℝ) < -1 - x by linarith)]
  · have hx1 : 1 < x := by
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_nonneg (show (0:ℝ) ≤ x by linarith) (show (0:ℝ) ≤ 1 - x by linarith)]
    have hpos : (0:ℝ) < x ^ 2 := pow_pos hx 2
    nlinarith [mul_pos hpos (show (0:ℝ) < x - 1 by linarith)]

private lemma plog_no_sol_b3 {a : ℕ} (ha : 1 ≤ a) :
    ¬ ∃ x : ℝ, 0 < x ^ 3 + (a:ℝ) ∧ x ^ 3 = x ^ 3 + 4 * (a:ℝ) := by
  rintro ⟨x, h1, h2⟩
  have hA : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  linarith

theorem permutations_a_b_log_eq_unique_sol_count :
    Nat.card { p : ℕ × ℕ |
      let a := p.1
      let b := p.2
      0 < a ∧ 0 < b ∧ a + b = 2026 ∧
      ∃! x : ℝ, 0 < x ^ 3 + (a : ℝ) ∧ 0 < x ^ b - 3 * (a : ℝ) ∧
      Real.log (x ^ 3 + (a : ℝ)) = Real.log (x ^ b - 3 * (a : ℝ)) } = 1011 := by
  classical
  have hmem : ∀ a b : ℕ, ((a, b) ∈ { p : ℕ × ℕ |
      let a := p.1
      let b := p.2
      0 < a ∧ 0 < b ∧ a + b = 2026 ∧
        ∃! x : ℝ, 0 < x ^ 3 + (a : ℝ) ∧ 0 < x ^ b - 3 * (a : ℝ) ∧
          Real.log (x ^ 3 + (a : ℝ)) = Real.log (x ^ b - 3 * (a : ℝ)) })
      ↔ ∃ k : ℕ, k < 1011 ∧ a = 2 * k + 1 ∧ b = 2025 - 2 * k := by
    intro a b
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨ha, hb, hab, hu⟩
      have ha1 : 1 ≤ a := ha
      have hQ : ∃! x : ℝ, 0 < x ^ 3 + (a:ℝ) ∧ x ^ b = x ^ 3 + 4 * (a:ℝ) :=
        (plog_eu_congr (fun x => plog_pred_iff a b x)).mp hu
      have hex : ∃ x : ℝ, 0 < x ^ 3 + (a:ℝ) ∧ x ^ b = x ^ 3 + 4 * (a:ℝ) := by
        obtain ⟨x, hx, -⟩ := hQ
        exact ⟨x, hx⟩
      have hbge : 4 ≤ b := by
        by_contra hcon
        push_neg at hcon
        interval_cases b
        · exact plog_no_sol_b1 ha1 hex
        · exact plog_no_sol_b2 ha1 hex
        · exact plog_no_sol_b3 ha1 hex
      have hbodd : Odd b := by
        rcases Nat.even_or_odd b with he | ho
        · exact absurd hQ (plog_even_bad hbge he hab ha1)
        · exact ho
      obtain ⟨m, hm⟩ := hbodd
      exact ⟨1012 - m, by omega, by omega, by omega⟩
    · rintro ⟨k, hk, ha, hb⟩
      subst ha
      subst hb
      refine ⟨by omega, by omega, by omega, ?_⟩
      refine (plog_eu_congr (fun x => plog_pred_iff _ _ x)).mpr ?_
      exact plog_odd_case (by omega) (by omega) ⟨1012 - k, by omega⟩
  have main : Nat.card (Fin 1011) = Nat.card { p : ℕ × ℕ |
      let a := p.1
      let b := p.2
      0 < a ∧ 0 < b ∧ a + b = 2026 ∧
        ∃! x : ℝ, 0 < x ^ 3 + (a : ℝ) ∧ 0 < x ^ b - 3 * (a : ℝ) ∧
          Real.log (x ^ 3 + (a : ℝ)) = Real.log (x ^ b - 3 * (a : ℝ)) } := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun k : Fin 1011 =>
      ⟨(2 * (k : ℕ) + 1, 2025 - 2 * (k : ℕ)),
        (hmem _ _).mpr ⟨(k : ℕ), k.isLt, rfl, rfl⟩⟩) ?_
    constructor
    · intro k l h
      have h1 : (2 * (k : ℕ) + 1, 2025 - 2 * (k : ℕ))
          = (2 * (l : ℕ) + 1, 2025 - 2 * (l : ℕ)) := congrArg Subtype.val h
      have h2 : 2 * (k : ℕ) + 1 = 2 * (l : ℕ) + 1 := congrArg Prod.fst h1
      exact Fin.ext (by omega)
    · rintro ⟨⟨a, b⟩, hp⟩
      obtain ⟨k, hk, ha, hb⟩ := (hmem a b).mp hp
      refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
      subst ha
      subst hb
      rfl
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at main
  exact main.symm
```
