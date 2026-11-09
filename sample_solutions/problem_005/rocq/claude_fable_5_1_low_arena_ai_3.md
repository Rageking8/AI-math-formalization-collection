# Claude Fable 5.1 Low (Arena AI)

Model: `claude-fable-5.1-low` (via Arena AI)\
Date: `9 November 2026`\
Line count: `26`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

Theorem power_tower_inequality (x y : R) (hx : 1 < x)
    (hxy : x < y) (heq : Rpower x y = Rpower y x) :
      Rpower x (Rpower y y) > Rpower y (Rpower x x).
Proof.
  assert (hy : 1 < y) by lra.
  assert (hx0 : 0 < x) by lra.
  assert (hy0 : 0 < y) by lra.
  assert (H1 : Rpower y ((y - 1) + 1) = y * Rpower y (y - 1)).
  { rewrite Rpower_plus, Rpower_1 by lra. ring. }
  replace ((y - 1) + 1) with y in H1 by ring.
  assert (H2 : Rpower x ((x - 1) + 1) = x * Rpower x (x - 1)).
  { rewrite Rpower_plus, Rpower_1 by lra. ring. }
  replace ((x - 1) + 1) with x in H2 by ring.
  rewrite H1, H2.
  rewrite <- Rpower_mult, heq, Rpower_mult.
  apply Rlt_gt.
  apply Rpower_lt; auto.
  apply Rmult_lt_compat_l; auto.
  apply Rlt_trans with (Rpower x (y - 1)).
  - apply Rpower_lt; auto; lra.
  - apply Rlt_Rpower_l; [lra | split; lra].
Qed.
```
