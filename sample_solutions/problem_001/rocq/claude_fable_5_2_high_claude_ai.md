# Claude Fable 5.2 High (Claude AI)

Model: `Claude Fable 5.2 High` (via Claude AI)\
Date: `10 November 2026`\
Line count: `86`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals ZArith.
From Stdlib Require Import Lra Lia.
Open Scope R_scope.

(* s n = (t_n, t_{n+1}) where t_n = a^n + b^n, a,b = (5 ± sqrt 17)/2,
   so t_0 = 2, t_1 = 5, t_{n+2} = 5 t_{n+1} - 2 t_n. *)
Fixpoint ceil_aux_seq (n : nat) : Z * Z :=
  match n with
  | O => (2, 5)%Z
  | S k => (snd (ceil_aux_seq k),
            5 * snd (ceil_aux_seq k) - 2 * fst (ceil_aux_seq k))%Z
  end.

Lemma ceil_aux_sqrt17 : sqrt 17 * sqrt 17 = 17 /\ 4 < sqrt 17 < 5.
Proof.
  assert (H : sqrt 17 * sqrt 17 = 17) by (apply sqrt_sqrt; lra).
  assert (H0 : 0 <= sqrt 17) by apply sqrt_pos.
  split; [exact H|]. split; nra.
Qed.

Lemma ceil_aux_spec : forall n,
    IZR (fst (ceil_aux_seq n))
    = ((5 + sqrt 17) / 2) ^ n + ((5 - sqrt 17) / 2) ^ n /\
    IZR (snd (ceil_aux_seq n))
    = ((5 + sqrt 17) / 2) ^ S n + ((5 - sqrt 17) / 2) ^ S n.
Proof.
  destruct ceil_aux_sqrt17 as [Hr _].
  set (a := (5 + sqrt 17) / 2). set (b := (5 - sqrt 17) / 2).
  assert (Ha : a * a = 5 * a - 2) by (unfold a; nra).
  assert (Hb : b * b = 5 * b - 2) by (unfold b; nra).
  induction n as [|n [IH1 IH2]].
  - simpl. unfold a, b. split; lra.
  - split.
    + exact IH2.
    + change (snd (ceil_aux_seq (S n)))
        with (5 * snd (ceil_aux_seq n) - 2 * fst (ceil_aux_seq n))%Z.
      rewrite minus_IZR, !mult_IZR, IH1, IH2.
      change (a ^ S (S n)) with (a * (a * a ^ n)).
      change (b ^ S (S n)) with (b * (b * b ^ n)).
      change (a ^ S n) with (a * a ^ n).
      change (b ^ S n) with (b * b ^ n).
      replace (a * (a * a ^ n)) with ((a * a) * a ^ n) by ring.
      replace (b * (b * b ^ n)) with ((b * b) * b ^ n) by ring.
      rewrite Ha, Hb. ring.
Qed.

Lemma ceil_aux_odd : forall n, Z.Odd (snd (ceil_aux_seq n)).
Proof.
  induction n as [|n [m Hm]].
  - exists 2%Z. reflexivity.
  - change (snd (ceil_aux_seq (S n)))
      with (5 * snd (ceil_aux_seq n) - 2 * fst (ceil_aux_seq n))%Z.
    exists (5 * m + 2 - fst (ceil_aux_seq n))%Z. lia.
Qed.

Lemma ceil_aux_small : forall n, 0 < ((5 - sqrt 17) / 2) ^ S n < 1.
Proof.
  destruct ceil_aux_sqrt17 as [_ Hr].
  set (b := (5 - sqrt 17) / 2).
  assert (Hb : 0 < b < 1) by (unfold b; lra).
  induction n as [|n IH].
  - simpl. lra.
  - change (b ^ S (S n)) with (b * b ^ S n). nra.
Qed.

Lemma ceil_aux_Zceil : forall (z : Z) (x : R),
    IZR z - 1 < x <= IZR z -> Zceil x = z.
Proof.
  intros z x [H1 H2].
  destruct (Zceil_bound x) as [H3 H4].
  assert (Zceil x < z + 1)%Z by (apply lt_IZR; rewrite plus_IZR; lra).
  assert (z < Zceil x + 1)%Z by (apply lt_IZR; rewrite plus_IZR; lra).
  lia.
Qed.

Theorem ceil_pow_expr_odd : forall x : nat,
    Z.Odd (Zceil (((5 + sqrt 17) / 2) ^ x)).
Proof.
  intros [|n].
  - rewrite (ceil_aux_Zceil 1) by (simpl; lra).
    exists 0%Z. reflexivity.
  - destruct (ceil_aux_spec n) as [_ H].
    pose proof (ceil_aux_small n) as Hs.
    rewrite (ceil_aux_Zceil (snd (ceil_aux_seq n))) by lra.
    apply ceil_aux_odd.
Qed.
```
