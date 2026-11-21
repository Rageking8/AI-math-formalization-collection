# Gemini 4 Hydrogen High (AI Studio)

Model: `Gemini 4 Hydrogen High` (via AI Studio)\
Date: `21 November 2026`\
Line count: `130`\
Turn count: `2`

## Solution

```rocq
From Stdlib Require Import Reals ZArith.
Open Scope R_scope.

Theorem ceil_pow_expr_odd : forall x : nat,
    Z.Odd (Zceil (((5 + sqrt 17) / 2) ^ x)).
Proof.
  intro x.
  destruct x as [| n].
  - simpl.
    replace (Zceil 1) with 1%Z.
    + exists 0%Z. reflexivity.
    + symmetry. apply Zceil_eq.
      change (IZR 1) with 1.
      split.
      * unfold Rminus. rewrite Rplus_opp_r. apply Rlt_0_1.
      * apply Rle_refl.
  - set (a := (5 + sqrt 17) / 2).
    set (b := (5 - sqrt 17) / 2).
    assert (H2nz : 2 <> 0).
    { change (IZR 2 <> IZR 0). apply not_0_IZR. discriminate. }
    assert (H017 : 0 < 17).
    { change (IZR 0 < IZR 17). apply IZR_lt. unfold Z.lt. reflexivity. }
    assert (H17 : 0 <= 17) by (apply Rlt_le; exact H017).
    assert (Hsq : sqrt 17 * sqrt 17 = 17) by (apply sqrt_def; exact H17).
    assert (Hs0 : 0 <= sqrt 17) by apply sqrt_pos.
    assert (Hs4 : 4 < sqrt 17).
    { destruct (Rle_or_lt (sqrt 17) 4) as [Hle | Hlt]; [| exact Hlt].
      exfalso.
      assert (H16 : sqrt 17 * sqrt 17 <= 4 * 4)
        by (apply Rmult_le_compat; assumption).
      rewrite Hsq in H16.
      change (IZR 17 <= IZR 4 * IZR 4) in H16.
      rewrite <- mult_IZR in H16.
      apply (Rlt_not_le (IZR 17) (IZR (4 * 4)));
        [apply IZR_lt; unfold Z.lt; reflexivity | exact H16]. }
    assert (Hs5 : sqrt 17 < 5).
    { destruct (Rle_or_lt 5 (sqrt 17)) as [Hle | Hlt]; [| exact Hlt].
      exfalso.
      assert (H5 : 0 <= 5).
      { change (IZR 0 <= IZR 5). apply IZR_le. unfold Z.le. discriminate. }
      assert (H25 : 5 * 5 <= sqrt 17 * sqrt 17)
        by (apply Rmult_le_compat; assumption).
      rewrite Hsq in H25.
      change (IZR 5 * IZR 5 <= IZR 17) in H25.
      rewrite <- mult_IZR in H25.
      apply (Rlt_not_le (IZR (5 * 5)) (IZR 17));
        [apply IZR_lt; unfold Z.lt; reflexivity | exact H25]. }
    assert (H2pos : 0 < 2).
    { change (IZR 0 < IZR 2). apply IZR_lt. unfold Z.lt. reflexivity. }
    assert (Hinv2 : 0 < / 2) by (apply Rinv_0_lt_compat; exact H2pos).
    assert (Hb0 : 0 < b).
    { unfold b, Rdiv.
      apply Rmult_lt_0_compat; [| exact Hinv2].
      apply Rplus_lt_reg_r with (r := sqrt 17).
      replace (0 + sqrt 17) with (sqrt 17) by ring.
      replace (5 - sqrt 17 + sqrt 17) with 5 by ring.
      exact Hs5. }
    assert (Hb1 : b < 1).
    { unfold b, Rdiv.
      rewrite <- (Rinv_l 2 H2nz).
      rewrite (Rmult_comm (5 - sqrt 17) (/ 2)).
      apply Rmult_lt_compat_l; [exact Hinv2 |].
      apply Rlt_trans with (r2 := IZR 5 - IZR 4).
      - unfold Rminus. apply Rplus_lt_compat_l. apply Ropp_lt_contravar. exact Hs4.
      - rewrite <- minus_IZR. change 2 with (IZR 2).
        apply IZR_lt. unfold Z.lt. reflexivity. }
    assert (Hbp : forall m : nat, 0 < b ^ m).
    { induction m as [| m IH].
      - simpl. apply Rlt_0_1.
      - simpl. apply Rmult_lt_0_compat; assumption. }
    assert (Hb1m : forall m : nat, b ^ S m < 1).
    { induction m as [| m IH].
      - simpl. replace (b * 1) with b by ring. exact Hb1.
      - replace (b ^ S (S m)) with (b * b ^ S m) by reflexivity.
        apply Rlt_trans with (r2 := b * 1).
        + apply Rmult_lt_compat_l; assumption.
        + replace (b * 1) with b by ring. exact Hb1. }
    assert (Hapb : a + b = 5).
    { unfold a, b. field; try exact H2nz. }
    assert (Hab : a * b = 2).
    { unfold a, b.
      transitivity ((25 - sqrt 17 * sqrt 17) * (/ 2 * / 2)).
      - field; try exact H2nz.
      - rewrite Hsq. field; try exact H2nz. }
    assert (Hseq : forall m : nat,
      exists z1 z2 : Z,
        IZR z1 = a ^ S m + b ^ S m /\ Z.Odd z1 /\
        IZR z2 = a ^ S (S m) + b ^ S (S m) /\ Z.Odd z2).
    { induction m as [| m [z1 [z2 [Hz1 [Hodd1 [Hz2 Hodd2]]]]]].
      - exists 5%Z, 21%Z. split; [| split; [| split]].
        + simpl. unfold a, b. field; try exact H2nz.
        + exists 2%Z. reflexivity.
        + simpl. unfold a, b.
          transitivity ((50 + 2 * (sqrt 17 * sqrt 17)) * (/ 2 * / 2)).
          * rewrite Hsq. field; try exact H2nz.
          * field; try exact H2nz.
        + exists 10%Z. reflexivity.
      - exists z2, (5 * z2 - 2 * z1)%Z. split; [| split; [| split]].
        + exact Hz2.
        + exact Hodd2.
        + rewrite minus_IZR, !mult_IZR.
          change (IZR 5) with 5.
          change (IZR 2) with 2.
          rewrite Hz1, Hz2, <- Hapb, <- Hab.
          replace (a ^ S (S (S m))) with (a * (a * a ^ S m)) by reflexivity.
          replace (b ^ S (S (S m))) with (b * (b * b ^ S m)) by reflexivity.
          replace (a ^ S (S m)) with (a * a ^ S m) by reflexivity.
          replace (b ^ S (S m)) with (b * b ^ S m) by reflexivity.
          ring.
        + destruct Hodd2 as [k Hk].
          exists (5 * k + 2 - z1)%Z.
          rewrite Hk. ring. }
    destruct (Hseq n) as [z1 [z2 [Hz1 [Hodd1 _]]]].
    assert (Hlb : IZR z1 - 1 < a ^ S n).
    { replace (a ^ S n) with (IZR z1 - b ^ S n) by (rewrite Hz1; ring).
      unfold Rminus.
      apply Rplus_lt_compat_l.
      apply Ropp_lt_contravar.
      exact (Hb1m n). }
    assert (Hub : a ^ S n <= IZR z1).
    { apply Rlt_le.
      replace (a ^ S n) with (IZR z1 - b ^ S n) by (rewrite Hz1; ring).
      apply Rplus_lt_reg_r with (r := b ^ S n).
      replace (IZR z1 - b ^ S n + b ^ S n) with (IZR z1 + 0) by ring.
      apply Rplus_lt_compat_l.
      exact (Hbp (S n)). }
    replace (Zceil (a ^ S n)) with z1.
    + exact Hodd1.
    + symmetry. apply Zceil_eq. split; [exact Hlb | exact Hub].
Qed.
```
