# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `9 November 2026`\
Line count: `102`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import Arith.

Theorem no_mod_mod_mod_eq_gcd (x y z : nat)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
      ((x mod y) mod z) * ((y mod z) mod x) * ((z mod x) mod y) <>
      Nat.gcd (Nat.gcd x y) z.
Proof.
  (* A common divisor of a and b also divides a mod b. *)
  assert (dmod : forall d a b,
             Nat.divide d a -> Nat.divide d b -> Nat.divide d (a mod b)).
  { intros d a b Ha Hb.
    apply (Nat.divide_add_cancel_r d (b * (a / b))).
    - apply Nat.divide_mul_l. exact Hb.
    - rewrite <- (Nat.div_mod_eq a b). exact Ha. }

  (* Main combinatorial step, assuming p is the largest of the three. *)
  assert (helper : forall p q r, 0 < p -> 0 < q -> 0 < r -> q <= p -> r <= p ->
             (q mod r) mod p = 1 -> (r mod p) mod q = 1 -> False).
  { intros p q r Hp Hq Hr Hqp Hrp H2 H3.
    assert (Hr0 : r <> 0) by (intro HH; rewrite HH in Hr; inversion Hr).
    assert (Hlt : r < p).
    { destruct (Nat.lt_trichotomy r p) as [L | [E | G]].
      - exact L.
      - exfalso. rewrite E in H3. rewrite Nat.Div0.mod_same in H3.
        rewrite (Nat.mod_small 0 q Hq) in H3. discriminate.
      - exfalso. apply (Nat.lt_irrefl p). apply (Nat.lt_le_trans p r p G Hrp). }
    rewrite (Nat.mod_small r p Hlt) in H3.
    assert (Hub : q mod r < r) by (apply Nat.mod_upper_bound; exact Hr0).
    rewrite (Nat.mod_small (q mod r) p (Nat.lt_trans _ _ _ Hub Hlt)) in H2.
    destruct (Nat.lt_trichotomy q r) as [L | [E | G]].
    - rewrite (Nat.mod_small q r L) in H2. rewrite H2 in H3.
      rewrite Nat.mod_1_r in H3. discriminate.
    - rewrite E in H2. rewrite Nat.Div0.mod_same in H2. discriminate.
    - rewrite (Nat.mod_small r q G) in H3. rewrite H3 in H2.
      rewrite Nat.mod_1_r in H2. discriminate. }

  (* The three cyclic remainders cannot all be 1. *)
  assert (key : forall a b c, 0 < a -> 0 < b -> 0 < c ->
             (a mod b) mod c = 1 -> (b mod c) mod a = 1 -> (c mod a) mod b = 1 ->
             False).
  { intros a b c Ha Hb Hc H1 H2 H3.
    destruct (Nat.le_gt_cases b a) as [Hba | Hba];
      destruct (Nat.le_gt_cases c a) as [Hca | Hca].
    - exact (helper a b c Ha Hb Hc Hba Hca H2 H3).
    - apply (helper c a b Hc Ha Hb (Nat.lt_le_incl _ _ Hca)
               (Nat.le_trans _ _ _ Hba (Nat.lt_le_incl _ _ Hca)) H1 H2).
    - apply (helper b c a Hb Hc Ha
               (Nat.le_trans _ _ _ Hca (Nat.lt_le_incl _ _ Hba))
               (Nat.lt_le_incl _ _ Hba) H3 H1).
    - destruct (Nat.le_gt_cases b c) as [Hbc | Hbc].
      + apply (helper c a b Hc Ha Hb (Nat.lt_le_incl _ _ Hca) Hbc H1 H2).
      + apply (helper b c a Hb Hc Ha (Nat.lt_le_incl _ _ Hbc)
                 (Nat.lt_le_incl _ _ Hba) H3 H1). }

  intro Heq.

  (* The gcd divides x, y and z, hence each of the three factors. *)
  assert (Hgx : Nat.divide (Nat.gcd (Nat.gcd x y) z) x).
  { apply Nat.divide_trans with (Nat.gcd x y);
      [ apply Nat.gcd_divide_l | apply Nat.gcd_divide_l ]. }
  assert (Hgy : Nat.divide (Nat.gcd (Nat.gcd x y) z) y).
  { apply Nat.divide_trans with (Nat.gcd x y);
      [ apply Nat.gcd_divide_l | apply Nat.gcd_divide_r ]. }
  assert (Hgz : Nat.divide (Nat.gcd (Nat.gcd x y) z) z) by apply Nat.gcd_divide_r.
  assert (Hg0 : Nat.gcd (Nat.gcd x y) z <> 0).
  { intro HH. apply Nat.gcd_eq_0_l in HH. apply Nat.gcd_eq_0_l in HH.
    rewrite HH in hx. inversion hx. }

  assert (Ha : Nat.divide (Nat.gcd (Nat.gcd x y) z) ((x mod y) mod z))
    by (apply dmod; [ apply dmod; assumption | assumption ]).
  assert (Hb : Nat.divide (Nat.gcd (Nat.gcd x y) z) ((y mod z) mod x))
    by (apply dmod; [ apply dmod; assumption | assumption ]).
  assert (Hc : Nat.divide (Nat.gcd (Nat.gcd x y) z) ((z mod x) mod y))
    by (apply dmod; [ apply dmod; assumption | assumption ]).

  (* Conversely, each factor divides the product, i.e. the gcd. *)
  assert (Ha' : Nat.divide ((x mod y) mod z) (Nat.gcd (Nat.gcd x y) z)).
  { rewrite <- Heq. apply Nat.divide_mul_l. apply Nat.divide_factor_l. }
  assert (Hb' : Nat.divide ((y mod z) mod x) (Nat.gcd (Nat.gcd x y) z)).
  { rewrite <- Heq. apply Nat.divide_mul_l. apply Nat.divide_factor_r. }
  assert (Hc' : Nat.divide ((z mod x) mod y) (Nat.gcd (Nat.gcd x y) z)).
  { rewrite <- Heq. apply Nat.divide_factor_r. }

  assert (Ea : (x mod y) mod z = Nat.gcd (Nat.gcd x y) z)
    by (apply Nat.divide_antisym; assumption).
  assert (Eb : (y mod z) mod x = Nat.gcd (Nat.gcd x y) z)
    by (apply Nat.divide_antisym; assumption).
  assert (Ec : (z mod x) mod y = Nat.gcd (Nat.gcd x y) z)
    by (apply Nat.divide_antisym; assumption).

  (* So g * g * g = g with g <> 0, forcing g = 1. *)
  rewrite Ea, Eb, Ec in Heq.
  rewrite <- Nat.mul_assoc in Heq.
  assert (Hsq : Nat.gcd (Nat.gcd x y) z * Nat.gcd (Nat.gcd x y) z = 1).
  { apply (proj1 (Nat.mul_cancel_l _ _ _ Hg0)).
    rewrite Nat.mul_1_r. exact Heq. }
  assert (Hg1 : Nat.gcd (Nat.gcd x y) z = 1).
  { destruct (proj1 (Nat.eq_mul_1 _ _) Hsq) as [H _]. exact H. }

  rewrite Hg1 in Ea, Eb, Ec.
  exact (key x y z hx hy hz Ea Eb Ec).
Qed.
```
