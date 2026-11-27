# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `27 November 2026`\
Line count: `20`\
Turn count: `1`

## Note

This solution uses `vm_compute`.

## Solution

```rocq
From Stdlib Require Import Arith.

Theorem no_nat_cube_sum_mod_eq (x y : nat) :
    (((x ^ 3 + y ^ 3) mod 18) mod 17) <> 15.
Proof.
  assert (Hc : forall n : nat, n ^ 3 mod 18 = (n mod 18) ^ 3 mod 18).
  { intros n. cbn [Nat.pow]. rewrite !Nat.mul_1_r.
    rewrite (Nat.Div0.mul_mod n (n * n)), (Nat.Div0.mul_mod n n).
    rewrite (Nat.Div0.mul_mod (n mod 18) (n mod 18 * (n mod 18))),
            (Nat.Div0.mul_mod (n mod 18) (n mod 18)).
    rewrite !Nat.Div0.mod_mod. reflexivity. }
  assert (Hgen : forall a b : nat, (a <? 18) = true -> (b <? 18) = true ->
            ((a ^ 3 mod 18 + b ^ 3 mod 18) mod 18) mod 17 <> 15).
  { intros a b Ha Hb.
    destruct a as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|a]]]]]]]]]]]]]]]]]]; try discriminate Ha;
    destruct b as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|b]]]]]]]]]]]]]]]]]]; try discriminate Hb;
    vm_compute; discriminate. }
  rewrite Nat.Div0.add_mod, (Hc x), (Hc y).
  apply Hgen; apply Nat.ltb_lt, Nat.mod_upper_bound; discriminate.
Qed.
```
