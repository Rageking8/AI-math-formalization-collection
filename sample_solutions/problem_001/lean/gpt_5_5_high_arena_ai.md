# GPT-5.5 High (Arena AI)

Model: `gpt-5.5-high` (via Arena AI)\
Date: `2 August 2026`\
Line count: `145`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem ceil_pow_expr_odd (x : ℕ) :
    Odd ⌈(((5 : ℝ) + Real.sqrt 17) / 2) ^ x⌉ := by
  let a : ℝ := ((5 : ℝ) + Real.sqrt 17) / 2
  let b : ℝ := ((5 : ℝ) - Real.sqrt 17) / 2
  change Odd ⌈a ^ x⌉
  cases x with
  | zero =>
      rw [pow_zero]
      have hceil : ⌈(1 : ℝ)⌉ = (1 : ℤ) := by
        exact Int.ceil_eq_iff.mpr ⟨by norm_num, by norm_num⟩
      rw [hceil]
      exact ⟨0, by norm_num⟩
  | succ n =>
      change Odd ⌈a ^ (n + 1)⌉

      let p : ℕ → ℤ × ℤ :=
        fun m =>
          Nat.rec ((2 : ℤ), (5 : ℤ))
            (fun _ q => (q.2, (5 : ℤ) * q.2 - 2 * q.1)) m

      have hsqrt_sq : (Real.sqrt (17 : ℝ)) ^ 2 = (17 : ℝ) := by
        exact Real.sq_sqrt (by norm_num)

      have hsqrt_lt_five : Real.sqrt (17 : ℝ) < 5 := by
        by_contra h
        push_neg at h
        nlinarith [hsqrt_sq, Real.sqrt_nonneg (17 : ℝ)]

      have hsqrt_gt_three : (3 : ℝ) < Real.sqrt (17 : ℝ) := by
        by_contra h
        push_neg at h
        nlinarith [hsqrt_sq, Real.sqrt_nonneg (17 : ℝ)]

      have hb_pos : 0 < b := by
        dsimp [b]
        nlinarith [hsqrt_lt_five]

      have hb_lt_one : b < 1 := by
        dsimp [b]
        nlinarith [hsqrt_gt_three]

      have ha_root : a ^ 2 = 5 * a - 2 := by
        dsimp [a]
        nlinarith [hsqrt_sq]

      have hb_root : b ^ 2 = 5 * b - 2 := by
        dsimp [b]
        nlinarith [hsqrt_sq]

      have ha_rec : ∀ m : ℕ, 5 * a ^ (m + 1) - 2 * a ^ m = a ^ (m + 2) := by
        intro m
        calc
          5 * a ^ (m + 1) - 2 * a ^ m = a ^ m * (5 * a - 2) := by
            rw [pow_succ]
            ring
          _ = a ^ m * a ^ 2 := by
            rw [← ha_root]
          _ = a ^ (m + 2) := by
            rw [pow_add]

      have hb_rec : ∀ m : ℕ, 5 * b ^ (m + 1) - 2 * b ^ m = b ^ (m + 2) := by
        intro m
        calc
          5 * b ^ (m + 1) - 2 * b ^ m = b ^ m * (5 * b - 2) := by
            rw [pow_succ]
            ring
          _ = b ^ m * b ^ 2 := by
            rw [← hb_root]
          _ = b ^ (m + 2) := by
            rw [pow_add]

      have hrec_sum : ∀ m : ℕ,
          5 * (a ^ (m + 1) + b ^ (m + 1)) - 2 * (a ^ m + b ^ m)
            = a ^ (m + 2) + b ^ (m + 2) := by
        intro m
        calc
          5 * (a ^ (m + 1) + b ^ (m + 1)) - 2 * (a ^ m + b ^ m)
              = (5 * a ^ (m + 1) - 2 * a ^ m)
                + (5 * b ^ (m + 1) - 2 * b ^ m) := by
            ring
          _ = a ^ (m + 2) + b ^ (m + 2) := by
            rw [ha_rec m, hb_rec m]

      have hp : ∀ m : ℕ,
          ((p m).1 : ℝ) = a ^ m + b ^ m ∧
          ((p m).2 : ℝ) = a ^ (m + 1) + b ^ (m + 1) := by
        intro m
        induction m with
        | zero =>
            constructor
            · change ((2 : ℤ) : ℝ) = a ^ 0 + b ^ 0
              norm_num
            · change ((5 : ℤ) : ℝ) = a ^ (0 + 1) + b ^ (0 + 1)
              dsimp [a, b]
              ring
        | succ m ih =>
            constructor
            · change ((p m).2 : ℝ) = a ^ (Nat.succ m) + b ^ (Nat.succ m)
              simpa [Nat.succ_eq_add_one] using ih.2
            · change (((5 * (p m).2 - 2 * (p m).1 : ℤ) : ℝ)) =
                a ^ (Nat.succ m + 1) + b ^ (Nat.succ m + 1)
              calc
                ((5 * (p m).2 - 2 * (p m).1 : ℤ) : ℝ)
                    = 5 * ((p m).2 : ℝ) - 2 * ((p m).1 : ℝ) := by
                  norm_num
                _ = 5 * (a ^ (m + 1) + b ^ (m + 1))
                    - 2 * (a ^ m + b ^ m) := by
                  rw [ih.1, ih.2]
                _ = a ^ (Nat.succ m + 1) + b ^ (Nat.succ m + 1) := by
                  simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hrec_sum m

      have hodd : ∀ m : ℕ, Odd ((p m).2) := by
        intro m
        induction m with
        | zero =>
            change Odd (5 : ℤ)
            exact ⟨2, by norm_num⟩
        | succ m ih =>
            change Odd (5 * (p m).2 - 2 * (p m).1)
            rcases ih with ⟨k, hk⟩
            refine ⟨5 * k - (p m).1 + 2, ?_⟩
            rw [hk]
            ring

      have hb_pow_pos : 0 < b ^ (n + 1) := by
        exact pow_pos hb_pos _

      have hb_pow_lt_one : b ^ (n + 1) < 1 := by
        exact pow_lt_one₀ (le_of_lt hb_pos) hb_lt_one (by omega)

      have hp2 : ((p n).2 : ℝ) = a ^ (n + 1) + b ^ (n + 1) := (hp n).2

      have hlt : ((p n).2 : ℝ) - 1 < a ^ (n + 1) := by
        nlinarith [hp2, hb_pow_lt_one]

      have hle : a ^ (n + 1) ≤ ((p n).2 : ℝ) := by
        nlinarith [hp2, le_of_lt hb_pow_pos]

      have hceil : ⌈a ^ (n + 1)⌉ = (p n).2 := by
        exact Int.ceil_eq_iff.mpr ⟨hlt, hle⟩

      rw [hceil]
      exact hodd n
```
