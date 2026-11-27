# Gemini 4 Hydrogen High (AI Studio)

Model: `Gemini 4 Hydrogen High` (via AI Studio)\
Date: `27 November 2026`\
Line count: `55`\
Turn count: `2`

## Note

This solution uses `vm_compute`.

## Solution

```rocq
From Stdlib Require Import Arith.

Theorem no_nat_cube_sum_mod_eq (x y : nat) :
    (((x ^ 3 + y ^ 3) mod 18) mod 17) <> 15.
Proof.
  intro H.
  remember ((x ^ 3 + y ^ 3) mod 18) as z eqn:Hz_eq.
  assert (Hz : (z <? 18) = true).
  { subst z. rewrite Nat.ltb_lt. apply Nat.mod_upper_bound. discriminate. }
  assert (Hz15 : z = 15).
  {
    do 18 (destruct z as [|z]; [simpl in H; try discriminate; reflexivity | ]).
    unfold Nat.ltb in Hz. simpl in Hz. discriminate.
  }
  rewrite Hz15 in Hz_eq.
  assert (Hmod9 : forall a, (a mod 18) mod 9 = a mod 9).
  {
    intro a.
    rewrite <- (Nat.Div0.mod_add (a mod 18) ((a / 18) * 2) 9).
    f_equal.
    rewrite Nat.add_comm, <- Nat.mul_assoc.
    change (2 * 9) with 18.
    rewrite (Nat.mul_comm (a / 18) 18).
    rewrite <- Nat.Div0.div_mod.
    reflexivity.
  }
  apply (f_equal (fun k => k mod 9)) in Hz_eq.
  rewrite Hmod9 in Hz_eq.
  change (15 mod 9) with 6 in Hz_eq.
  assert (Hpow_mod : forall n, n ^ 3 mod 9 = (n mod 9) ^ 3 mod 9).
  {
    intro n.
    change (n ^ 3) with (n * (n * (n * 1))).
    change ((n mod 9) ^ 3) with ((n mod 9) * ((n mod 9) * ((n mod 9) * 1))).
    rewrite !Nat.mul_1_r.
    rewrite (Nat.Div0.mul_mod n (n * n) 9).
    rewrite (Nat.Div0.mul_mod n n 9).
    rewrite Nat.Div0.mul_mod_idemp_r.
    reflexivity.
  }
  rewrite Nat.Div0.add_mod, (Hpow_mod x), (Hpow_mod y) in Hz_eq.
  assert (Hcube : forall n, (n <? 9) = true ->
            n ^ 3 mod 9 = 0 \/ n ^ 3 mod 9 = 1 \/ n ^ 3 mod 9 = 8).
  {
    intros n Hn.
    do 9 (destruct n as [|n];
          [vm_compute; first [left; reflexivity | right; left; reflexivity | right; right; reflexivity] | ]).
    unfold Nat.ltb in Hn. simpl in Hn. discriminate.
  }
  assert (Ha : (x mod 9 <? 9) = true) by (rewrite Nat.ltb_lt; apply Nat.mod_upper_bound; discriminate).
  assert (Hb : (y mod 9 <? 9) = true) by (rewrite Nat.ltb_lt; apply Nat.mod_upper_bound; discriminate).
  destruct (Hcube (x mod 9) Ha) as [Hcx | [Hcx | Hcx]]; rewrite Hcx in Hz_eq;
  destruct (Hcube (y mod 9) Hb) as [Hcy | [Hcy | Hcy]]; rewrite Hcy in Hz_eq;
  vm_compute in Hz_eq; discriminate.
Qed.
```
