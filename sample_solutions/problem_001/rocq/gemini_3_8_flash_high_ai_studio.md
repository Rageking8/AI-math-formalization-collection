# Gemini 3.8 Flash High (AI Studio)

Model: `Gemini 3.8 Flash High` (via AI Studio)\
Date: `31 October 2026`\
Line count: `164`\
Turn count: `2`

## Solution

```rocq
From Stdlib Require Import Reals ZArith.
Open Scope R_scope.

Theorem ceil_pow_expr_odd : forall x : nat,
    Z.Odd (Zceil (((5 + sqrt 17) / 2) ^ x)).
Proof.
  intro x.
  set (alpha := (5 + sqrt 17) / 2).
  set (beta := (5 - sqrt 17) / 2).
  assert (H17_ge : 0 <= 17).
  { apply (IZR_le 0 17). easy. }
  assert (Hsq17 : sqrt 17 * sqrt 17 = 17).
  { apply sqrt_def. exact H17_ge. }
  assert (Hsq4 : sqrt (4 * 4) = 4).
  { apply sqrt_square. apply (IZR_le 0 4). easy. }
  assert (Hsq5 : sqrt (5 * 5) = 5).
  { apply sqrt_square. apply (IZR_le 0 5). easy. }
  assert (Hlt1 : 4 < sqrt 17).
  { assert (Hstep : sqrt 16 < sqrt 17).
    { apply sqrt_lt_1_alt. split.
      - apply (IZR_le 0 16). easy.
      - apply (IZR_lt 16 17). easy. }
    assert (H16_eq : 16 = 4 * 4) by ring.
    rewrite H16_eq in Hstep.
    rewrite Hsq4 in Hstep.
    exact Hstep. }
  assert (Hlt2 : sqrt 17 < 5).
  { assert (Hstep : sqrt 17 < sqrt 25).
    { apply sqrt_lt_1_alt. split.
      - exact H17_ge.
      - apply (IZR_lt 17 25). easy. }
    assert (H25_eq : 25 = 5 * 5) by ring.
    rewrite H25_eq in Hstep.
    rewrite Hsq5 in Hstep.
    exact Hstep. }
  assert (Hinv2 : 0 < / 2).
  { apply Rinv_0_lt_compat.
    apply (IZR_lt 0 2).
    easy. }
  assert (Hbeta_pos : 0 < beta).
  { unfold beta, Rdiv.
    apply Rmult_lt_0_compat.
    - apply Rlt_0_minus. exact Hlt2.
    - exact Hinv2. }
  assert (Hbeta_lt_1 : beta < 1).
  { apply Rlt_0_minus.
    unfold beta.
    replace (1 - (5 - sqrt 17) / 2) with ((sqrt 17 - 4) / 2 + / 2) by field.
    apply Rplus_lt_0_compat.
    - unfold Rdiv. apply Rmult_lt_0_compat.
      + apply Rlt_0_minus. exact Hlt1.
      + exact Hinv2.
    - exact Hinv2. }
  assert (Halpha_sq : alpha * alpha = 5 * alpha - 2).
  { assert (Hf : alpha * alpha = 5 * alpha - 2 + (sqrt 17 * sqrt 17 - 17) / 4).
    { unfold alpha. field. }
    rewrite Hsq17 in Hf.
    assert (Hz : (17 - 17) / 4 = 0).
    { replace (17 - 17) with 0 by ring.
      unfold Rdiv.
      apply Rmult_0_l. }
    rewrite Hz in Hf.
    rewrite Rplus_0_r in Hf.
    exact Hf. }
  assert (Hbeta_sq : beta * beta = 5 * beta - 2).
  { assert (Hf : beta * beta = 5 * beta - 2 + (sqrt 17 * sqrt 17 - 17) / 4).
    { unfold beta. field. }
    rewrite Hsq17 in Hf.
    assert (Hz : (17 - 17) / 4 = 0).
    { replace (17 - 17) with 0 by ring.
      unfold Rdiv.
      apply Rmult_0_l. }
    rewrite Hz in Hf.
    rewrite Rplus_0_r in Hf.
    exact Hf. }
  assert (Hrec : forall m : nat,
    alpha ^ S (S m) + beta ^ S (S m) =
    5 * (alpha ^ S m + beta ^ S m) - 2 * (alpha ^ m + beta ^ m)).
  { intro m.
    change (alpha ^ S (S m)) with (alpha * (alpha * alpha ^ m)).
    change (alpha ^ S m) with (alpha * alpha ^ m).
    change (beta ^ S (S m)) with (beta * (beta * beta ^ m)).
    change (beta ^ S m) with (beta * beta ^ m).
    replace (alpha * (alpha * alpha ^ m)) with ((alpha * alpha) * alpha ^ m) by ring.
    replace (beta * (beta * beta ^ m)) with ((beta * beta) * beta ^ m) by ring.
    rewrite Halpha_sq, Hbeta_sq.
    ring. }
  assert (Hbase0 : alpha ^ 0 + beta ^ 0 = IZR 2).
  { change (alpha ^ 0) with 1.
    change (beta ^ 0) with 1.
    ring. }
  assert (Hbase1 : alpha ^ 1 + beta ^ 1 = IZR 5).
  { change (alpha ^ 1) with (alpha * 1).
    change (beta ^ 1) with (beta * 1).
    unfold alpha, beta.
    field. }
  assert (Hbeta_pow : forall k : nat, 0 < beta ^ S k /\ beta ^ S k < 1).
  { induction k as [| k IH].
    - change (beta ^ 1) with (beta * 1).
      replace (beta * 1) with beta by ring.
      split; [exact Hbeta_pos | exact Hbeta_lt_1].
    - destruct IH as [IHpos IHlt].
      change (beta ^ S (S k)) with (beta * beta ^ S k).
      split.
      + apply Rmult_lt_0_compat; [exact Hbeta_pos | exact IHpos].
      + assert (Hstep : beta * beta ^ S k < beta).
        { apply Rlt_0_minus.
          replace (beta - beta * beta ^ S k) with (beta * (1 - beta ^ S k)) by ring.
          apply Rmult_lt_0_compat; [exact Hbeta_pos |].
          apply Rlt_0_minus. exact IHlt. }
        apply Rlt_trans with beta; [exact Hstep | exact Hbeta_lt_1]. }
  assert (HP : forall n : nat, exists u v : Z,
    IZR u = alpha ^ n + beta ^ n /\
    IZR v = alpha ^ S n + beta ^ S n /\
    (n = 0%nat \/ Z.Odd u) /\
    Z.Odd v).
  { induction n as [| n IH].
    - exists 2%Z, 5%Z.
      split; [symmetry; exact Hbase0 |].
      split; [symmetry; exact Hbase1 |].
      split; [left; reflexivity |].
      exists 2%Z. reflexivity.
    - destruct IH as [u [v [Hu [Hv [Hodd_u Hodd_v]]]]].
      exists v, (5 * v - 2 * u)%Z.
      split; [exact Hv |].
      split.
      + rewrite minus_IZR; repeat rewrite mult_IZR.
        rewrite Hv, Hu, Hrec.
        ring.
      + split; [right; exact Hodd_v |].
        destruct Hodd_v as [k Hk].
        exists (5 * k + 2 - u)%Z.
        rewrite Hk.
        ring. }
  destruct x as [| n].
  - change (alpha ^ 0) with 1.
    assert (Hceil1 : Zceil 1 = 1%Z).
    { apply Zceil_eq.
      split.
      - replace (IZR 1 - 1) with 0 by ring.
        apply Rlt_0_1.
      - replace (IZR 1) with 1 by ring.
        apply Rle_refl. }
    rewrite Hceil1.
    exists 0%Z. reflexivity.
  - destruct (HP n) as [u [v [Hu [Hv [Hodd_u Hodd_v]]]]].
    assert (Hceil : Zceil (alpha ^ S n) = v).
    { apply Zceil_eq.
      split.
      + apply Rlt_0_minus.
        rewrite Hv.
        replace (alpha ^ S n - (alpha ^ S n + beta ^ S n - 1)) with (1 - beta ^ S n) by ring.
        apply Rlt_0_minus.
        destruct (Hbeta_pow n) as [_ Hlt].
        exact Hlt.
      + rewrite Hv.
        destruct (Hbeta_pow n) as [Hpos _].
        assert (Hle : 0 <= beta ^ S n) by (apply Rlt_le; exact Hpos).
        pose proof (Rplus_le_compat_l (alpha ^ S n) 0 (beta ^ S n) Hle) as Hle2.
        replace (alpha ^ S n + 0) with (alpha ^ S n) in Hle2 by ring.
        exact Hle2. }
    rewrite Hceil.
    exact Hodd_v.
Qed.
```
