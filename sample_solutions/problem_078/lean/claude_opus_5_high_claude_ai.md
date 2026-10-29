# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `24 August 2026`\
Line count: `190`\
Turn count: `3`

## Solution

```lean4
import Mathlib

def IsEgyptianFractionDecomp (q : ℚ) (l : List ℕ) : Prop :=
  l.Pairwise (· < ·) ∧ (∀ x ∈ l, 2 ≤ x) ∧ (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = q

private lemma egypt_helper (N : ℚ) (hN : N ≠ 0) (S P a : ℚ) (ha : S * P = a) :
    ((1 : ℚ) / N + S) * (N * P) = P + N * a := by
  have h1 : (1 : ℚ) / N * (N * P) = P := by
    rw [one_div, inv_mul_cancel_left₀ hN]
  calc ((1 : ℚ) / N + S) * (N * P) = (1 : ℚ) / N * (N * P) + N * (S * P) := by ring
    _ = P + N * a := by rw [h1, ha]

private lemma egypt_prod_int :
    ∀ L : List ℕ, (∀ n ∈ L, n ≠ 0) →
      ∃ a : ℤ, (L.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum * (L.prod : ℚ) = (a : ℚ) := by
  intro L
  induction L with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons n L ih =>
    intro h
    obtain ⟨a, ha⟩ := ih fun m hm => h m (by simp [hm])
    have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (h n (by simp))
    refine ⟨(L.prod : ℤ) + (n : ℤ) * a, ?_⟩
    simp only [List.map_cons, List.sum_cons, List.prod_cons, Nat.cast_mul]
    rw [egypt_helper _ hn _ _ _ ha]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    try ring

private lemma egypt_prod_not_dvd :
    ∀ L : List ℕ, (∀ n ∈ L, ¬(457 ∣ n)) → ¬(457 ∣ L.prod) := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons n L ih =>
    intro h hdvd
    rw [List.prod_cons] at hdvd
    rcases (Nat.Prime.dvd_mul (by norm_num)).1 hdvd with h1 | h2
    · exact h n (by simp) h1
    · exact ih (fun m hm => h m (by simp [hm])) h2

private lemma egypt_split_dvd :
    ∀ L : List ℕ, L.Nodup → ∃ L₁ L₂ : List ℕ,
      L₁.Nodup ∧ (∀ n ∈ L₁, n ∈ L ∧ 457 ∣ n) ∧ (∀ n ∈ L₂, n ∈ L ∧ ¬(457 ∣ n)) ∧
        (L.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum
          = (L₁.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum
            + (L₂.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨[], [], by simp, by simp, by simp, by simp⟩
  | cons n L ih =>
    intro hnd
    rw [List.nodup_cons] at hnd
    obtain ⟨L₁, L₂, hnd1, hm1, hm2, hsum⟩ := ih hnd.2
    by_cases hn : (457 ∣ n)
    · refine ⟨n :: L₁, L₂, ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        exact ⟨fun hmem => hnd.1 (hm1 n hmem).1, hnd1⟩
      · intro m hm
        rcases List.mem_cons.1 hm with rfl | hm'
        · exact ⟨by simp, hn⟩
        · exact ⟨by simp [(hm1 m hm').1], (hm1 m hm').2⟩
      · intro m hm
        exact ⟨by simp [(hm2 m hm).1], (hm2 m hm).2⟩
      · simp only [List.map_cons, List.sum_cons, hsum]
        try ring
    · refine ⟨L₁, n :: L₂, hnd1, ?_, ?_, ?_⟩
      · intro m hm
        exact ⟨by simp [(hm1 m hm).1], (hm1 m hm).2⟩
      · intro m hm
        rcases List.mem_cons.1 hm with rfl | hm'
        · exact ⟨by simp, hn⟩
        · exact ⟨by simp [(hm2 m hm').1], (hm2 m hm').2⟩
      · simp only [List.map_cons, List.sum_cons, hsum]
        try ring

private lemma egypt_l1_sum :
    ∀ L : List ℕ,
      (∀ n ∈ L, n = 457 ∨ n = 914 ∨ n = 1371 ∨ n = 1828 ∨ n = 2285 ∨ n = 2742) →
      ∃ c : ℕ, c ≤ 60 * L.length ∧
        (L.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = (c : ℚ) / 27420 := by
  intro L
  induction L with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons n L ih =>
    intro h
    obtain ⟨c, hc, hcs⟩ := ih fun m hm => h m (by simp [hm])
    have key : ∃ k : ℕ, k ≤ 60 ∧ (1 : ℚ) / (n : ℚ) = (k : ℚ) / 27420 := by
      rcases h n (by simp) with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨60, by norm_num⟩
      · exact ⟨30, by norm_num⟩
      · exact ⟨20, by norm_num⟩
      · exact ⟨15, by norm_num⟩
      · exact ⟨12, by norm_num⟩
      · exact ⟨10, by norm_num⟩
    obtain ⟨k, hk, hkeq⟩ := key
    refine ⟨k + c, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · simp only [List.map_cons, List.sum_cons, hkeq, hcs]
      push_cast
      try ring

private lemma egypt_nodup_length_le :
    ∀ L S : List ℕ, L.Nodup → (∀ x ∈ L, x ∈ S) → L.length ≤ S.length := by
  intro L
  induction L with
  | nil => intro S _ _; simp
  | cons n L ih =>
    intro S hnd hsub
    rw [List.nodup_cons] at hnd
    have hnS : n ∈ S := hsub n (by simp)
    have hlen : (S.erase n).length + 1 = S.length := by
      first
        | exact List.length_erase_add_one hnS
        | (rw [List.length_erase_of_mem hnS]
           have : 0 < S.length := List.length_pos_of_mem hnS
           omega)
    have hsub' : ∀ x ∈ L, x ∈ S.erase n := by
      intro x hx
      have hne : x ≠ n := by
        intro hh
        rw [hh] at hx
        exact hnd.1 hx
      exact (List.mem_erase_of_ne hne).2 (hsub x (by simp [hx]))
    have hIH := ih (S.erase n) hnd.2 hsub'
    simp only [List.length_cons]
    omega

theorem egyptian_fraction_311_457_tight_lower_bound :
    (∀ l : List ℕ, IsEgyptianFractionDecomp (311 / 457) l → ∃ n ∈ l, 3199 ≤ n) ∧
      (∃ l : List ℕ, IsEgyptianFractionDecomp (311 / 457) l ∧ ∀ n ∈ l, n ≤ 3199) := by
  constructor
  · rintro l ⟨hpw, hge2, hsum⟩
    by_contra hcon
    push_neg at hcon
    have hnd : l.Nodup := by
      refine List.Pairwise.imp ?_ hpw
      intro a b hab
      exact Nat.ne_of_lt hab
    obtain ⟨L₁, L₂, hnd1, h1, h2, heq⟩ := egypt_split_dvd l hnd
    have hval : ∀ n ∈ L₁, n = 457 ∨ n = 914 ∨ n = 1371 ∨ n = 1828 ∨ n = 2285 ∨ n = 2742 := by
      intro n hn
      obtain ⟨hnl, hd⟩ := h1 n hn
      obtain ⟨k, rfl⟩ := hd
      have hb1 : 457 * k < 3199 := hcon _ hnl
      have hb2 : 2 ≤ 457 * k := hge2 _ hnl
      have hk1 : 1 ≤ k := by omega
      have hk2 : k ≤ 6 := by omega
      interval_cases k <;> omega
    have hsubset : ∀ x ∈ L₁, x ∈ [457, 914, 1371, 1828, 2285, 2742] := by
      intro x hx
      rcases hval x hx with h | h | h | h | h | h <;> subst h <;> simp
    have hlen : L₁.length ≤ 6 := by
      have h := egypt_nodup_length_le L₁ [457, 914, 1371, 1828, 2285, 2742] hnd1 hsubset
      simpa using h
    obtain ⟨c, hc, hcs⟩ := egypt_l1_sum L₁ hval
    have hc360 : c ≤ 360 := by omega
    obtain ⟨a, ha⟩ := egypt_prod_int L₂ fun n hn => by
      have := hge2 n (h2 n hn).1
      omega
    obtain ⟨P, hP⟩ : ∃ P : ℕ, L₂.prod = P := ⟨_, rfl⟩
    rw [hP] at ha
    have hPd : ¬(457 ∣ P) := by
      rw [← hP]
      exact egypt_prod_not_dvd L₂ fun n hn => (h2 n hn).2
    rw [hsum, hcs] at heq
    have h3 : (311 : ℚ) / 457 * (P : ℚ) = (c : ℚ) / 27420 * (P : ℚ) + (a : ℚ) := by
      rw [← ha, ← add_mul, ← heq]
    have hQ : (18660 : ℚ) * (P : ℚ) = (c : ℚ) * (P : ℚ) + 27420 * (a : ℚ) := by
      linear_combination (27420 : ℚ) * h3
    have hZ : (18660 : ℤ) * (P : ℤ) = (c : ℤ) * (P : ℤ) + 27420 * a := by exact_mod_cast hQ
    have hdvd : (457 : ℤ) ∣ (18660 - (c : ℤ)) * (P : ℤ) := ⟨60 * a, by linear_combination hZ⟩
    have hp : Prime (457 : ℤ) := by
      first
        | norm_num
        | exact_mod_cast Nat.Prime.prime_int (by norm_num : Nat.Prime 457)
    rcases hp.2.2 _ _ hdvd with hA | hB
    · obtain ⟨k, hk⟩ := hA
      have hcz : (c : ℤ) ≤ 360 := by exact_mod_cast hc360
      have hcz0 : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg c
      omega
    · exact hPd (by exact_mod_cast hB)
  · refine ⟨[2, 7, 28, 914, 1828, 3199], ⟨?_, ?_, ?_⟩, ?_⟩
    · norm_num [List.pairwise_cons]
    · norm_num
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      norm_num
    · norm_num
```
