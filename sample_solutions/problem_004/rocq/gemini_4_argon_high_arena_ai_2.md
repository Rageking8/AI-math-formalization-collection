# Gemini 4 Argon High (Arena AI)

Model: `gemini-4-argon-high` (via Arena AI)\
Date: `8 November 2026`\
Line count: `74`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals.
Open Scope R_scope.

Theorem log_abs_sum_lower_bound (x y : R) (hx : 0 < x) (hy : 0 < y) :
    Rabs (ln x) + Rabs (ln y) >= 2 * ln ((x + y) / (2 * sqrt (x * y))).
Proof.
  assert (Hmain : forall a b : R, 0 < a -> 0 < b -> a <= b ->
    2 * ln ((a + b) / (2 * sqrt (a * b))) <= Rabs (ln a) + Rabs (ln b)).
  { intros a b Ha Hb Hab.
    set (s := sqrt (a * b)).
    set (A := (a + b) / (2 * s)).
    assert (H2 : 0 < 2).
    { replace 2 with (1 + 1) by ring.
      apply Rplus_lt_0_compat; exact Rlt_0_1. }
    assert (Hab_pos : 0 < a * b).
    { apply Rmult_lt_0_compat; assumption. }
    assert (Hs : 0 < s).
    { unfold s; apply sqrt_lt_R0; exact Hab_pos. }
    assert (H2s : 0 < 2 * s).
    { apply Rmult_lt_0_compat; [exact H2 | exact Hs]. }
    assert (Hapb : 0 < a + b).
    { apply Rplus_lt_0_compat; assumption. }
    assert (HA : 0 < A).
    { unfold A, Rdiv.
      apply Rmult_lt_0_compat; [exact Hapb | apply Rinv_0_lt_compat; exact H2s]. }
    assert (E_apb : a + b = A * (2 * s)).
    { unfold A; field; apply Rgt_not_eq; exact Hs. }
    assert (E1 : ln (a + b) = ln A + (ln 2 + ln s)).
    { rewrite E_apb.
      rewrite (ln_mult A (2 * s) HA H2s).
      rewrite (ln_mult 2 s H2 Hs).
      reflexivity. }
    assert (E2 : ln (2 * b) = ln 2 + ln b).
    { apply ln_mult; [exact H2 | exact Hb]. }
    assert (E_ss : s * s = a * b).
    { unfold s; apply sqrt_sqrt; apply Rlt_le; exact Hab_pos. }
    assert (E3 : ln a + ln b = ln s + ln s).
    { rewrite <- (ln_mult a b Ha Hb).
      rewrite <- E_ss.
      apply ln_mult; exact Hs. }
    assert (Hle1 : a + b <= 2 * b).
    { replace (2 * b) with (b + b) by ring.
      apply Rplus_le_compat; [exact Hab | apply Rle_refl]. }
    assert (Hle2 : ln (a + b) <= ln (2 * b)).
    { destruct Hle1 as [Hlt | Heq].
      - left; apply ln_increasing; [exact Hapb | exact Hlt].
      - right; rewrite Heq; reflexivity. }
    assert (Hle3 : ln (a + b) + ln (a + b) <= ln (2 * b) + ln (2 * b)).
    { apply Rplus_le_compat; exact Hle2. }
    assert (Hle4 : 2 * ln A <= ln b - ln a).
    { apply Rplus_le_reg_r with (r := 2 * ln 2 + (ln a + ln b)).
      replace (2 * ln A + (2 * ln 2 + (ln a + ln b)))
        with (ln (a + b) + ln (a + b))
        by (rewrite E1, E3; ring).
      replace ((ln b - ln a) + (2 * ln 2 + (ln a + ln b)))
        with (ln (2 * b) + ln (2 * b))
        by (rewrite E2; ring).
      exact Hle3. }
    assert (Hle5 : ln b - ln a <= Rabs (ln a) + Rabs (ln b)).
    { replace (ln b - ln a) with (- ln a + ln b) by ring.
      apply Rplus_le_compat.
      - rewrite <- (Rabs_Ropp (ln a)).
        apply Rle_abs.
      - apply Rle_abs. }
    apply Rle_trans with (r2 := ln b - ln a); [exact Hle4 | exact Hle5]. }
  apply Rle_ge.
  destruct (Rle_or_lt x y) as [Hxy | Hyx].
  - apply Hmain; assumption.
  - apply Rlt_le in Hyx.
    rewrite (Rplus_comm x y).
    rewrite (Rmult_comm x y).
    rewrite (Rplus_comm (Rabs (ln x)) (Rabs (ln y))).
    apply Hmain; assumption.
Qed.
```
