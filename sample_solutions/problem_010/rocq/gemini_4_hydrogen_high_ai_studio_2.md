# Gemini 4 Hydrogen High (AI Studio)

Model: `Gemini 4 Hydrogen High` (via AI Studio)\
Date: `27 November 2026`\
Line count: `55`\
Turn count: `1`

## Note

The model was explicitly told not to use `vm_compute`.

## Solution

```rocq
From Stdlib Require Import Arith.

Theorem no_nat_cube_sum_mod_eq (x y : nat) :
    (((x ^ 3 + y ^ 3) mod 18) mod 17) <> 15.
Proof.
  intro H.
  assert (Hz : (x ^ 3 + y ^ 3) mod 18 = 15).
  {
    assert (Hlt : (x ^ 3 + y ^ 3) mod 18 < 18)
      by (apply Nat.mod_upper_bound; discriminate).
    revert H Hlt.
    generalize ((x ^ 3 + y ^ 3) mod 18).
    intros z Hmod Hlt'.
    do 18 (destruct z as [|z]; [cbv in Hmod; (discriminate Hmod || reflexivity) |]).
    exfalso.
    do 18 (apply (proj2 (Nat.succ_lt_mono _ _)) in Hlt').
    exact (Nat.nlt_0_r z Hlt').
  }
  assert (H9 : (x ^ 3 + y ^ 3) mod 9 = 6).
  {
    assert (Hdm : x ^ 3 + y ^ 3 = 18 * ((x ^ 3 + y ^ 3) / 18) + (x ^ 3 + y ^ 3) mod 18)
      by apply Nat.Div0.div_mod.
    rewrite Hdm, Hz.
    rewrite Nat.Div0.add_mod.
    rewrite Nat.Div0.mul_mod.
    change (18 mod 9) with 0.
    rewrite Nat.mul_0_l.
    change (0 mod 9) with 0.
    change (15 mod 9) with 6.
    rewrite Nat.add_0_l.
    change (6 mod 9) with 6.
    reflexivity.
  }
  assert (Hcube : forall a : nat, (a ^ 3) mod 9 = 0 \/ (a ^ 3) mod 9 = 1 \/ (a ^ 3) mod 9 = 8).
  {
    intro a.
    change (a ^ 3) with (a * (a * (a * 1))).
    rewrite Nat.mul_1_r.
    rewrite Nat.Div0.mul_mod.
    rewrite (Nat.Div0.mul_mod a a 9).
    assert (Hr : a mod 9 < 9) by (apply Nat.mod_upper_bound; discriminate).
    revert Hr.
    generalize (a mod 9).
    intros r Hr.
    do 9 (destruct r as [|r];
          [cbv; (left; reflexivity) || (right; left; reflexivity) || (right; right; reflexivity) |]).
    exfalso.
    do 9 (apply (proj2 (Nat.succ_lt_mono _ _)) in Hr).
    exact (Nat.nlt_0_r r Hr).
  }
  rewrite Nat.Div0.add_mod in H9.
  destruct (Hcube x) as [Hx | [Hx | Hx]];
  destruct (Hcube y) as [Hy | [Hy | Hy]];
  rewrite Hx, Hy in H9; cbv in H9; discriminate H9.
Qed.
```
