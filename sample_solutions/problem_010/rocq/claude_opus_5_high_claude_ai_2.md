# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `27 November 2026`\
Line count: `44`\
Turn count: `1`

## Note

The model was explicitly told not to use `vm_compute`.

## Solution

```rocq
From Stdlib Require Import Arith.

Theorem no_nat_cube_sum_mod_eq (x y : nat) :
    (((x ^ 3 + y ^ 3) mod 18) mod 17) <> 15.
Proof.
  assert (pow3 : forall n : nat, n ^ 3 = n * n * n) by (intros n; simpl; ring).
  assert (cubes : forall r : nat, r < 18 ->
            exists k m : nat, r * r * r = m + k * 18 /\
              (m = 0 \/ m = 1 \/ m = 8 \/ m = 9 \/ m = 10 \/ m = 17)).
  { intros r Hr.
    destruct r as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|r]]]]]]]]]]]]]]]]]];
    [ exists 0, 0 | exists 0, 1 | exists 0, 8 | exists 1, 9 | exists 3, 10
    | exists 6, 17 | exists 12, 0 | exists 19, 1 | exists 28, 8 | exists 40, 9
    | exists 55, 10 | exists 73, 17 | exists 96, 0 | exists 122, 1
    | exists 152, 8 | exists 187, 9 | exists 227, 10 | exists 272, 17
    | exfalso; exact (Nat.lt_irrefl 18
        (Nat.le_lt_trans 18 (18 + r) 18 (Nat.le_add_r 18 r) Hr)) ];
    (split; [ reflexivity | tauto ]). }
  assert (Hr : x mod 18 < 18) by (apply Nat.mod_upper_bound; discriminate).
  assert (Ht : y mod 18 < 18) by (apply Nat.mod_upper_bound; discriminate).
  destruct (cubes _ Hr) as (k1 & m1 & E1 & H1).
  destruct (cubes _ Ht) as (k2 & m2 & E2 & H2).
  pose proof (Nat.div_mod_eq x 18) as Hx.
  pose proof (Nat.div_mod_eq y 18) as Hy.
  rewrite !pow3.
  remember (x / 18) as q eqn:Eq; remember (x mod 18) as r eqn:Er.
  remember (y / 18) as p eqn:Ep; remember (y mod 18) as t eqn:Et.
  clear Eq Er Ep Et Hr Ht cubes pow3.
  assert (EX : x * x * x + y * y * y =
                 m1 + m2 +
                 (k1 + k2 +
                  (324 * (q * q * q) + 54 * (q * q) * r + 3 * q * (r * r) +
                   324 * (p * p * p) + 54 * (p * p) * t + 3 * p * (t * t))) * 18).
  { rewrite Hx, Hy.
    transitivity (r * r * r + t * t * t +
                  (324 * (q * q * q) + 54 * (q * q) * r + 3 * q * (r * r) +
                   324 * (p * p * p) + 54 * (p * p) * t + 3 * p * (t * t)) * 18).
    - ring.
    - rewrite E1, E2; ring. }
  rewrite EX, Nat.Div0.mod_add.
  destruct H1 as [e1|[e1|[e1|[e1|[e1|e1]]]]];
  destruct H2 as [e2|[e2|[e2|[e2|[e2|e2]]]]];
  subst; compute; discriminate.
Qed.
```
