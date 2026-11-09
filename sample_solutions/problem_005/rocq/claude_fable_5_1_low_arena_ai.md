# Claude Fable 5.1 Low (Arena AI)

Model: `claude-fable-5.1-low` (via Arena AI)\
Date: `9 November 2026`\
Line count: `31`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Theorem power_tower_inequality (x y : R) (hx : 1 < x)
    (hxy : x < y) (heq : Rpower x y = Rpower y x) :
      Rpower x (Rpower y y) > Rpower y (Rpower x x).
Proof.
  assert (Hx0 : 0 < x) by lra.
  assert (Hy0 : 0 < y) by lra.
  assert (Hlnx : 0 < ln x).
  { rewrite <- ln_1. apply ln_increasing; lra. }
  assert (Hln : y * ln x = x * ln y).
  { unfold Rpower in heq. apply exp_inv; exact heq. }
  assert (Hxx : Rpower x (x - 1) * Rpower x 1 = Rpower x x).
  { rewrite <- Rpower_plus. replace (x - 1 + 1) with x by ring. reflexivity. }
  rewrite Rpower_1 in Hxx by assumption.
  assert (Hyy : Rpower y (y - 1) * Rpower y 1 = Rpower y y).
  { rewrite <- Rpower_plus. replace (y - 1 + 1) with y by ring. reflexivity. }
  rewrite Rpower_1 in Hyy by assumption.
  assert (Hab : Rpower x (x - 1) < Rpower y (y - 1)).
  { apply Rlt_trans with (Rpower x (y - 1)).
    - apply Rpower_lt; lra.
    - apply Rlt_Rpower_l; [lra | split; lra]. }
  set (a := Rpower x (x - 1)) in *.
  set (b := Rpower y (y - 1)) in *.
  rewrite <- Hxx, <- Hyy.
  unfold Rpower. apply exp_increasing.
  replace (a * x * ln y) with (a * (y * ln x)) by (rewrite Hln; ring).
  replace (b * y * ln x) with (b * (y * ln x)) by ring.
  apply Rmult_lt_compat_r; [apply Rmult_lt_0_compat; assumption | exact Hab].
Qed.
```
