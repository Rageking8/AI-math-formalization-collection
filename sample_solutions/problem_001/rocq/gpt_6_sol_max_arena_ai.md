# GPT-6 Sol Max (Arena AI)

Model: `gpt-6-sol-max` (via Arena AI)\
Date: `2 November 2026`\
Line count: `115`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals ZArith Lia Lra Psatz Ring.
Open Scope R_scope.

Theorem ceil_pow_expr_odd : forall x : nat,
    Z.Odd (Zceil (((5 + sqrt 17) / 2) ^ x)).
Proof.
  intro x.
  set (a := (5 + sqrt 17) / 2).
  set (b := (5 - sqrt 17) / 2).

  assert (Hspos : 0 <= sqrt 17) by (apply sqrt_pos; lra).
  assert (Hsq : sqrt 17 * sqrt 17 = 17)
    by (apply sqrt_sqrt; lra).
  assert (Hsrange : 3 < sqrt 17 < 5) by (split; nra).
  assert (Hb : 0 < b < 1).
  { unfold b. destruct Hsrange as [Hlo Hhi]. split; nra. }
  assert (Hsum : a + b = 5) by (unfold a, b; nra).
  assert (Ha : a * a = 5 * a - 2) by (unfold a; nra).
  assert (Hbroot : b * b = 5 * b - 2) by (unfold b; nra).

  assert (Hrec : forall (t : R) (n : nat),
      t * t = 5 * t - 2 ->
      t ^ (S (S n)) = 5 * t ^ (S n) - 2 * t ^ n).
  {
    intros t n Ht.
    replace (t ^ (S (S n))) with ((t * t) * t ^ n)
      by (simpl; ring).
    replace (t ^ (S n)) with (t * t ^ n)
      by (simpl; ring).
    rewrite Ht; ring.
  }

  assert (Htrace : forall n : nat, exists u v : Z,
      IZR u = a ^ n + b ^ n /\
      IZR v = a ^ (S n) + b ^ (S n) /\
      Z.Odd v).
  {
    intro n; induction n as [|n [u [v [Hu [Hv Hodd]]]]].
    - exists 2%Z, 5%Z.
      split; [simpl; ring |].
      split.
      + replace (a ^ (S 0) + b ^ (S 0)) with (a + b)
          by (simpl; ring).
        rewrite Hsum; reflexivity.
      + exists 2%Z; lia.
    - exists v, (5 * v - 2 * u)%Z.
      split; [exact Hv |].
      split.
      + rewrite minus_IZR, !mult_IZR.
        change (IZR 5%Z) with (5 : R).
        change (IZR 2%Z) with (2 : R).
        rewrite Hu, Hv.
        rewrite (Hrec a n Ha), (Hrec b n Hbroot).
        ring.
      + destruct Hodd as [k Hk].
        exists (5 * k + 2 - u)%Z; lia.
  }

  assert (Hsmall : forall n : nat, 0 < b ^ (S n) < 1).
  {
    intro n; induction n as [|n IH].
    - simpl. destruct Hb as [Hbpos Hblt]. nra.
    - replace (b ^ (S (S n))) with (b * b ^ (S n))
        by (simpl; ring).
      destruct IH as [IHpos IHlt].
      split.
      + apply Rmult_lt_0_compat; [exact (proj1 Hb) | exact IHpos].
      + eapply Rlt_trans with (r2 := b * 1).
        * apply Rmult_lt_compat_l; [exact (proj1 Hb) | exact IHlt].
        * replace (b * 1) with b by ring.
          exact (proj2 Hb).
  }

  assert (Hceil : forall (y : R) (z : Z),
      IZR z - 1 < y <= IZR z -> Zceil y = z).
  {
    intros y z [Hylo Hyhi].
    destruct (archimed (- y)) as [Hu1 Hu2].
    assert (Hup : (up (- y) = 1 - z)%Z).
    {
      destruct (Z.eq_dec (up (- y)) (1 - z)%Z) as [Heq | Hneq].
      - exact Heq.
      - assert (Hcase :
          (up (- y) <= - z)%Z \/
          (2 - z <= up (- y))%Z) by lia.
        destruct Hcase as [Hcase | Hcase].
        + assert (Hreal : IZR (up (- y)) <= IZR (- z)%Z).
          { first [apply le_IZR; lia | apply IZR_le; lia]. }
          rewrite opp_IZR in Hreal.
          lra.
        + assert (Hreal : IZR (2 - z)%Z <= IZR (up (- y))).
          { first [apply le_IZR; lia | apply IZR_le; lia]. }
          rewrite minus_IZR in Hreal.
          change (IZR 2%Z) with (2 : R) in Hreal.
          lra.
    }
    cbv [Zceil Zfloor].
    rewrite Hup.
    lia.
  }

  destruct x as [|n].
  - change (Z.Odd (Zceil (1 : R))).
    rewrite (Hceil 1 1%Z) by (simpl; lra).
    exists 0%Z; lia.
  - destruct (Htrace n) as [u [v [Hu [Hv Hodd]]]].
    assert (Hbetween : IZR v - 1 < a ^ (S n) <= IZR v).
    {
      rewrite Hv.
      destruct (Hsmall n) as [Hpos Hlt].
      lra.
    }
    rewrite (Hceil (a ^ (S n)) v Hbetween).
    exact Hodd.
Qed.
```
