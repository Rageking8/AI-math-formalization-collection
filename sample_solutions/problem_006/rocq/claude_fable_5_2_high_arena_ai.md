# Claude Fable 5.2 High (Arena AI)

Model: `claude-fable-5.2-high` (via Arena AI)\
Date: `11 November 2026`\
Line count: `50`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Lemma key (x y z : nat) : 0 < x -> 0 < y -> 0 < z -> x <= y -> x <= z ->
  ((x mod y) mod z) * ((y mod z) mod x) * ((z mod x) mod y) <>
  Nat.gcd (Nat.gcd x y) z.
Proof.
  intros hx hy hz hxy hxz H.
  assert (hg : Nat.gcd (Nat.gcd x y) z <> 0).
  { intro e. apply Nat.gcd_eq_0_r in e. lia. }
  assert (ha : (x mod y) mod z <> 0) by (intro e; rewrite e in H; lia).
  assert (hc : (z mod x) mod y <> 0) by (intro e; rewrite e in H; lia).
  assert (nxy : x <> y).
  { intro e. apply ha. rewrite e.
    rewrite Nat.Div0.mod_same. apply Nat.Div0.mod_0_l. }
  assert (e1 : x mod y = x) by (apply Nat.mod_small; lia).
  rewrite e1 in ha.
  assert (nxz : x <> z).
  { intro e. apply ha. rewrite e. apply Nat.Div0.mod_same. }
  assert (e2 : x mod z = x) by (apply Nat.mod_small; lia).
  rewrite e1, e2 in H.
  apply hc.
  assert (hd : Nat.divide x z).
  { apply Nat.divide_trans with (Nat.gcd (Nat.gcd x y) z).
    - rewrite <- H. apply Nat.divide_mul_l. apply Nat.divide_mul_l.
      apply Nat.divide_refl.
    - apply Nat.gcd_divide_r. }
  destruct hd as [k hk].
  assert (hzx : z mod x = 0).
  { rewrite hk. apply Nat.Div0.mod_mul. }
  rewrite hzx. apply Nat.Div0.mod_0_l.
Qed.

Theorem no_mod_mod_mod_eq_gcd (x y z : nat)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
      ((x mod y) mod z) * ((y mod z) mod x) * ((z mod x) mod y) <>
      Nat.gcd (Nat.gcd x y) z.
Proof.
  assert (C : (x <= y /\ x <= z) \/ (y <= z /\ y <= x) \/ (z <= x /\ z <= y)) by lia.
  destruct C as [[h1 h2]|[[h1 h2]|[h1 h2]]].
  - apply key; assumption.
  - intro H. apply (key y z x hy hz hx h1 h2).
    assert (E : Nat.gcd (Nat.gcd y z) x = Nat.gcd (Nat.gcd x y) z).
    { rewrite <- (Nat.gcd_assoc x y z). apply Nat.gcd_comm. }
    rewrite E, <- H. first [ring | lia].
  - intro H. apply (key z x y hz hx hy h1 h2).
    assert (E : Nat.gcd (Nat.gcd z x) y = Nat.gcd (Nat.gcd x y) z).
    { rewrite <- (Nat.gcd_assoc z x y). apply Nat.gcd_comm. }
    rewrite E, <- H. first [ring | lia].
Qed.
```
