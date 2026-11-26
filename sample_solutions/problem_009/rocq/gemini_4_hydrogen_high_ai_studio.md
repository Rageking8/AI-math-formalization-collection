# Gemini 4 Hydrogen High (AI Studio)

Model: `Gemini 4 Hydrogen High` (via AI Studio)\
Date: `26 November 2026`\
Line count: `318`\
Turn count: `7`

## Solution

```rocq
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Theorem eq_one_of_dvd_pow_add_one (n : Z) (hn : 0 < n)
    (h2 : (n | 2 ^ n + 1)) (h3 : (n | 3 ^ n + 1)) : n = 1.
Proof.
  destruct (Z.eq_dec n 1) as [-> | Hn1]; [reflexivity |].
  assert (Hn2 : 2 <= n).
  { assert (H1n : 1 <= n) by (apply (proj2 (Z.le_succ_l 0 n)); exact hn).
    destruct (proj1 (Z.lt_eq_cases 1 n) H1n) as [Hlt | Heq].
    - change 2 with (Z.succ 1). rewrite Z.le_succ_l. exact Hlt.
    - exfalso. apply Hn1. symmetry. exact Heq. }
  assert (Hmin : forall (k : nat) (d : Z),
    2 <= d -> n = d + Z.of_nat k ->
    (forall q, 1 < q < d -> ~ (q | n)) ->
    exists p, 1 < p /\ (p | n) /\ (forall q, 1 < q < p -> ~ (q | n))).
  { intro k. induction k as [| k IH]; intros d Hd Hn Hprev.
    - exists n. repeat split.
      + rewrite Hn. simpl. rewrite Z.add_0_r.
        change 2 with (Z.succ 1) in Hd. rewrite Z.le_succ_l in Hd. exact Hd.
      + apply Z.divide_refl.
      + intros q [Hq1 Hqd]. apply Hprev. split; [exact Hq1 |].
        rewrite Hn in Hqd. simpl in Hqd. rewrite Z.add_0_r in Hqd. exact Hqd.
    - assert (Hd0 : d <> 0).
      { intro Heq. subst d. apply Hd. reflexivity. }
      destruct (Z.eq_dec (n mod d) 0) as [Hmod | Hnmod].
      + exists d. repeat split.
        * change 2 with (Z.succ 1) in Hd. rewrite Z.le_succ_l in Hd. exact Hd.
        * apply Z.mod_divide; assumption.
        * exact Hprev.
      + apply (IH (d + 1)).
        * rewrite Z.add_1_r. apply Z.le_le_succ_r. exact Hd.
        * rewrite Hn, Nat2Z.inj_succ, <- Z.add_1_r. ring.
        * intros q [Hq1 Hqd].
          rewrite Z.add_1_r, Z.lt_succ_r in Hqd.
          destruct (proj1 (Z.lt_eq_cases q d) Hqd) as [Hlt | Heq].
          -- apply Hprev. split; assumption.
          -- subst q. intro Hdiv. apply Hnmod. apply (Z.mod_divide n d Hd0). exact Hdiv. }
  destruct (Hmin (Z.to_nat (n - 2)) 2 (Z.le_refl 2)) as [p [Hp1 [Hpn Hpmin]]].
  { rewrite Z2Nat.id; [ring | apply Z.le_0_sub; exact Hn2]. }
  { intros q [Hq1 Hq2] _.
    change 2 with (Z.succ 1) in Hq2. rewrite Z.lt_succ_r in Hq2.
    apply (Z.lt_irrefl 1). eapply Z.lt_le_trans; eassumption. }
  assert (Hp_mul : forall x y, (p | x * y) -> (p | x) \/ (p | y)).
  { intros x y Hxy.
    assert (Hp0 : p <> 0) by (intro Heq; subst p; discriminate Hp1).
    destruct (Z.eq_dec (x mod p) 0) as [Hx | Hnx].
    - left. apply Z.mod_divide; assumption.
    - right.
      assert (Hpx : Z.gcd p x = 1).
      { set (g := Z.gcd p x).
        assert (Hg0 : 0 <= g) by apply Z.gcd_nonneg.
        assert (Hgp : (g | p)) by apply Z.gcd_divide_l.
        assert (Hgx : (g | x)) by apply Z.gcd_divide_r.
        assert (Hp_pos : 0 < p) by (apply Z.lt_trans with 1; [reflexivity | exact Hp1]).
        assert (Hgp_le : g <= p) by (apply Z.divide_pos_le; assumption).
        assert (Hg0' : g <> 0).
        { intro Heq. rewrite Heq in Hgp. apply Z.divide_0_l in Hgp. exact (Hp0 Hgp). }
        destruct (proj1 (Z.lt_eq_cases 0 g) Hg0) as [Hg_pos | Hg_zero];
          [| exfalso; apply Hg0'; symmetry; exact Hg_zero].
        assert (H1g : 1 <= g) by (apply (proj2 (Z.le_succ_l 0 g)); exact Hg_pos).
        destruct (proj1 (Z.lt_eq_cases 1 g) H1g) as [Hg1 | Hg1]; [| symmetry; exact Hg1].
        destruct (proj1 (Z.lt_eq_cases g p) Hgp_le) as [Hgp_lt | Hgp_eq].
        - exfalso. apply (Hpmin g); [split; assumption | apply (Z.divide_trans _ _ _ Hgp Hpn)].
        - exfalso. apply Hnx. apply Z.mod_divide; [exact Hp0 | rewrite <- Hgp_eq; exact Hgx]. }
      destruct (Z.gcd_bezout p x 1 Hpx) as [u [v Huv]].
      replace y with (u * p * y + v * (x * y)).
      + apply Z.divide_add_r.
        * replace (u * p * y) with (p * (u * y)) by ring. apply Z.divide_factor_l.
        * apply Z.divide_mul_r. exact Hxy.
      + transitivity ((u * p + v * x) * y); [ring | rewrite Huv; ring]. }
  assert (Hp2 : p <> 2).
  { intro Heq. subst p.
    assert (H2_pow : (2 | 2 ^ n)).
    { replace n with (1 + (n - 1)) by ring.
      rewrite Z.pow_add_r;
        [rewrite Z.pow_1_r; apply Z.divide_factor_l
        | intro H; discriminate H
        | apply Z.le_0_sub; apply (proj2 (Z.le_succ_l 0 n)); exact hn]. }
    assert (H2_1 : (2 | 1)).
    { replace 1 with ((2 ^ n + 1) - 2 ^ n) by ring.
      apply Z.divide_sub_r; [apply (Z.divide_trans _ _ _ Hpn h2) | exact H2_pow]. }
    destruct (Z.divide_1_r 2 H2_1) as [Habs | Habs]; discriminate Habs. }
  assert (Hflt2 : (p | 2 ^ (p - 1) - 1)).
  { pose (binom := fix binom (a b : nat) : Z :=
      match a, b with
      | _, O => 1
      | O, S _ => 0
      | S a', S b' => binom a' b' + binom a' (S b')
      end).
    assert (Hb0 : forall a, binom a O = 1) by (intro a; destruct a; reflexivity).
    assert (Hb0S : forall b, binom O (S b) = 0) by (intro b; reflexivity).
    assert (HbSS : forall a b, binom (S a) (S b) = binom a b + binom a (S b))
      by (intros a b; reflexivity).
    assert (Hb_gt : forall a b, (a < b)%nat -> binom a b = 0).
    { intro a. induction a as [| a IH]; intros [| b] Hab.
      - inversion Hab.
      - apply Hb0S.
      - inversion Hab.
      - rewrite HbSS, (IH b (le_S_n _ _ Hab)), (IH (S b) (le_S _ _ (le_S_n _ _ Hab))). ring. }
    assert (Hb_nn : forall a, binom a a = 1).
    { intro a. induction a as [| a IH].
      - apply Hb0.
      - rewrite HbSS, IH, (Hb_gt a (S a) (le_n (S a))). ring. }
    assert (Hb_1 : forall a, binom a 1%nat = Z.of_nat a).
    { intro a. induction a as [| a IH].
      - apply Hb0S.
      - rewrite HbSS, Hb0, IH, Nat2Z.inj_succ, <- Z.add_1_r. ring. }
    assert (Hb_abs : forall a b,
      Z.of_nat (S b) * binom (S a) (S b) = Z.of_nat (S a) * binom a b).
    { intro a. induction a as [| a IH]; intro b.
      - destruct b as [| b].
        + rewrite Hb_1, Hb0. simpl. ring.
        + rewrite HbSS, !Hb0S. ring.
      - destruct b as [| b].
        + rewrite Hb_1, Hb0. ring.
        + rewrite HbSS.
          replace (Z.of_nat (S (S b)) * (binom (S a) (S b) + binom (S a) (S (S b))))
            with (Z.of_nat (S b) * binom (S a) (S b) + binom (S a) (S b) +
                  Z.of_nat (S (S b)) * binom (S a) (S (S b)))
            by (rewrite (Nat2Z.inj_succ (S b)), <- Z.add_1_r; ring).
          rewrite (IH b), (IH (S b)), (HbSS a b), (Nat2Z.inj_succ (S a)), <- Z.add_1_r.
          ring. }
    pose (sum_binom := fix sb (a b : nat) : Z :=
      match b with
      | O => 0
      | S b' => sb a b' + binom a b'
      end).
    assert (Hsb0 : forall a, sum_binom a O = 0) by (intro a; reflexivity).
    assert (HsbS : forall a b, sum_binom a (S b) = sum_binom a b + binom a b)
      by (intros a b; reflexivity).
    assert (Hsb_succ : forall a b,
      sum_binom (S a) (S b) = sum_binom a (S b) + sum_binom a b).
    { intros a b. induction b as [| b IH].
      - rewrite !HsbS, !Hsb0, !Hb0. ring.
      - rewrite (HsbS (S a) (S b)), IH, HbSS, (HsbS a (S b)), (HsbS a b). ring. }
    assert (Hsb_pow : forall a, sum_binom a (S a) = 2 ^ Z.of_nat a).
    { intro a. induction a as [| a IH].
      - rewrite HsbS, Hsb0, Hb0. reflexivity.
      - rewrite Hsb_succ, (HsbS a (S a)), (Hb_gt a (S a) (le_n (S a))), IH.
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by apply Nat2Z.is_nonneg. ring. }
    assert (H0p : 0 <= p)
      by (apply Z.lt_le_incl; apply Z.lt_trans with 1; [reflexivity | exact Hp1]).
    assert (Hpm : Z.of_nat (Z.to_nat p) = p) by (apply Z2Nat.id; exact H0p).
    destruct (Z.to_nat p) as [| m'] eqn:Em.
    { exfalso.
      assert (Hp0 : p = 0).
      { transitivity (Z.of_nat O);
          [symmetry; first [exact Hpm | rewrite <- Em; exact Hpm] | reflexivity]. }
      subst p. discriminate Hp1. }
    assert (Hp_eq' : Z.of_nat (S m') = p)
      by (first [exact Hpm | rewrite <- Em; exact Hpm]).
    clear Em Hpm.
    destruct m' as [| m].
    { exfalso. simpl in Hp_eq'. subst p. discriminate Hp1. }
    assert (Hb_dvd : forall k,
      (1 <= k)%nat -> (k < S (S m))%nat -> (p | binom (S (S m)) k)).
    { intros k Hk1 Hkp.
      destruct k as [| k']; [inversion Hk1 |].
      assert (Hmul : Z.of_nat (S k') * binom (S (S m)) (S k') = p * binom (S m) k').
      { rewrite Hb_abs, Hp_eq'. reflexivity. }
      assert (Hdvd_mul : (p | Z.of_nat (S k') * binom (S (S m)) (S k'))).
      { rewrite Hmul. apply Z.divide_factor_l. }
      destruct (Hp_mul _ _ Hdvd_mul) as [Hdvd_k | Hdvd_b]; [| exact Hdvd_b].
      exfalso.
      assert (Hk_pos : 0 < Z.of_nat (S k')).
      { rewrite Nat2Z.inj_succ, Z.lt_succ_r. apply Nat2Z.is_nonneg. }
      assert (Hpk : p <= Z.of_nat (S k')).
      { apply Z.divide_pos_le; assumption. }
      assert (HkpZ : Z.of_nat (S k') < p).
      { rewrite <- Hp_eq'. apply (proj1 (Nat2Z.inj_lt _ _)). exact Hkp. }
      apply (Z.lt_irrefl p). eapply Z.le_lt_trans; eassumption. }
    assert (Hle0 : forall x : nat, (O <= x)%nat)
      by (intro x; induction x; [apply le_n | apply le_S; assumption]).
    assert (Hsb_dvd : forall k,
      (k < S (S m))%nat -> (p | sum_binom (S (S m)) (S k) - 1)).
    { intro k. induction k as [| k IH]; intro Hkp.
      - rewrite HsbS, Hsb0, Hb0. replace (0 + 1 - 1) with 0 by ring. apply Z.divide_0_r.
      - rewrite HsbS.
        replace (sum_binom (S (S m)) (S k) + binom (S (S m)) (S k) - 1)
          with ((sum_binom (S (S m)) (S k) - 1) + binom (S (S m)) (S k)) by ring.
        assert (Hk'p : (k < S (S m))%nat).
        { apply (proj2 (Nat2Z.inj_lt k (S (S m)))).
          eapply Z.lt_trans; [| apply (proj1 (Nat2Z.inj_lt (S k) (S (S m)))); exact Hkp].
          rewrite Nat2Z.inj_succ. apply Z.lt_succ_diag_r. }
        apply Z.divide_add_r.
        + apply IH. exact Hk'p.
        + apply Hb_dvd; [apply le_n_S, Hle0 | exact Hkp]. }
    assert (H2p : (p | 2 ^ p - 2)).
    { pose proof (Hsb_dvd (S m) (le_n (S (S m)))) as Hs.
      replace (2 ^ p) with (sum_binom (S (S m)) (S (S (S m))))
        by (rewrite Hsb_pow, Hp_eq'; reflexivity).
      rewrite HsbS, Hb_nn.
      replace (sum_binom (S (S m)) (S (S m)) + 1 - 2)
        with (sum_binom (S (S m)) (S (S m)) - 1) by ring.
      exact Hs. }
    assert (H0p1 : 0 <= p - 1) by (apply Z.le_0_sub; apply Z.lt_le_incl; exact Hp1).
    replace p with (1 + (p - 1)) in H2p at 2 by ring.
    rewrite Z.pow_add_r in H2p; [rewrite Z.pow_1_r in H2p | intro H; discriminate H | exact H0p1].
    replace (2 * 2 ^ (p - 1) - 2) with (2 * (2 ^ (p - 1) - 1)) in H2p by ring.
    destruct (Hp_mul _ _ H2p) as [Hp_dvd_2 | Hp_dvd]; [| exact Hp_dvd].
    assert (Hp_le_2 : p <= 2) by (apply Z.divide_pos_le; [reflexivity | exact Hp_dvd_2]).
    destruct (proj1 (Z.lt_eq_cases p 2) Hp_le_2) as [Hlt | Heq].
    - change 2 with (Z.succ 1) in Hlt. rewrite Z.lt_succ_r in Hlt.
      exfalso. apply (Z.lt_irrefl 1). eapply Z.lt_le_trans; eassumption.
    - exfalso. apply Hp2. exact Heq. }
  assert (Hp1_pos : 0 < p - 1) by (apply Z.lt_0_sub; exact Hp1).
  assert (Hcop : Z.gcd n (p - 1) = 1).
  { set (g := Z.gcd n (p - 1)).
    assert (Hg0 : 0 <= g) by apply Z.gcd_nonneg.
    assert (Hgn : (g | n)) by apply Z.gcd_divide_l.
    assert (Hgp : (g | p - 1)) by apply Z.gcd_divide_r.
    assert (Hgp_le : g <= p - 1) by (apply Z.divide_pos_le; assumption).
    assert (Hg_lt_p : g < p).
    { replace p with (Z.succ (p - 1)) by (rewrite Z.sub_1_r, Z.succ_pred; reflexivity).
      rewrite Z.lt_succ_r. exact Hgp_le. }
    assert (Hg0' : g <> 0).
    { intro Heq. rewrite Heq in Hgp. apply Z.divide_0_l in Hgp.
      rewrite Hgp in Hp1_pos. discriminate Hp1_pos. }
    destruct (proj1 (Z.lt_eq_cases 0 g) Hg0) as [Hg_pos | Hg_zero];
      [| exfalso; apply Hg0'; symmetry; exact Hg_zero].
    assert (H1g : 1 <= g) by (apply (proj2 (Z.le_succ_l 0 g)); exact Hg_pos).
    destruct (proj1 (Z.lt_eq_cases 1 g) H1g) as [Hg1 | Hg1]; [| symmetry; exact Hg1].
    exfalso. apply (Hpmin g); [split; assumption | exact Hgn]. }
  destruct (Z.gcd_bezout n (p - 1) 1 Hcop) as [u [v Huv]].
  set (k := Z.max 0 (-u) + Z.max 0 v).
  assert (Hk0 : 0 <= k) by (unfold k; apply Z.add_nonneg_nonneg; apply Z.le_max_l).
  assert (Huk : -u <= k).
  { unfold k. eapply Z.le_trans; [apply Z.le_max_r |].
    rewrite <- (Z.add_0_r (Z.max 0 (-u))) at 1.
    apply (proj1 (Z.add_le_mono_l 0 (Z.max 0 v) (Z.max 0 (-u)))).
    apply Z.le_max_l. }
  assert (Hvk : v <= k).
  { unfold k. eapply Z.le_trans; [apply Z.le_max_r |].
    rewrite (Z.add_comm (Z.max 0 (-u)) (Z.max 0 v)).
    rewrite <- (Z.add_0_r (Z.max 0 v)) at 1.
    apply (proj1 (Z.add_le_mono_l 0 (Z.max 0 (-u)) (Z.max 0 v))).
    apply Z.le_max_l. }
  set (a := u + k * (p - 1)).
  set (b := -v + k * n).
  assert (Ha0 : 0 <= a).
  { unfold a. replace (u + k * (p - 1)) with (k * (p - 1) - (-u)) by ring.
    apply Z.le_0_sub. eapply Z.le_trans; [exact Huk |].
    rewrite <- (Z.mul_1_r k) at 1.
    apply Z.mul_le_mono_nonneg_l; [exact Hk0 |].
    apply (proj2 (Z.le_succ_l 0 (p - 1))). exact Hp1_pos. }
  assert (Hb0 : 0 <= b).
  { unfold b. replace (-v + k * n) with (k * n - v) by ring.
    apply Z.le_0_sub. eapply Z.le_trans; [exact Hvk |].
    rewrite <- (Z.mul_1_r k) at 1.
    apply Z.mul_le_mono_nonneg_l; [exact Hk0 |].
    apply (proj2 (Z.le_succ_l 0 n)). exact hn. }
  assert (Hab_eq : a * n = 1 + b * (p - 1)).
  { unfold a, b.
    transitivity ((u * n + v * (p - 1)) + (-v + k * n) * (p - 1));
      [ring | rewrite Huv; ring]. }
  assert (Hpow_cong : forall x y e, 0 <= e -> (p | x - y) -> (p | x ^ e - y ^ e)).
  { intros x y e He Hxy.
    rewrite <- (Z2Nat.id e He).
    induction (Z.to_nat e) as [| m IH].
    - simpl. replace (1 - 1) with 0 by ring. apply Z.divide_0_r.
    - rewrite Nat2Z.inj_succ, !Z.pow_succ_r by apply Nat2Z.is_nonneg.
      replace (x * x ^ Z.of_nat m - y * y ^ Z.of_nat m)
        with ((x - y) * x ^ Z.of_nat m + y * (x ^ Z.of_nat m - y ^ Z.of_nat m)) by ring.
      apply Z.divide_add_r; [apply Z.divide_mul_l; exact Hxy | apply Z.divide_mul_r; exact IH]. }
  assert (Hp_2n : (p | 2 ^ n - (-1))).
  { replace (2 ^ n - -1) with (2 ^ n + 1) by ring. apply (Z.divide_trans _ _ _ Hpn h2). }
  assert (H2a0 : 0 <= 2 * a)
    by (apply Z.mul_nonneg_nonneg; [intro H; discriminate H | exact Ha0]).
  assert (Hp_2an1 : (p | 2 ^ (2 * a * n) - 1)).
  { pose proof (Hpow_cong (2 ^ n) (-1) (2 * a) H2a0 Hp_2n) as Hpow1.
    rewrite <- Z.pow_mul_r in Hpow1; [| apply Z.lt_le_incl; exact hn | exact H2a0].
    replace (n * (2 * a)) with (2 * a * n) in Hpow1 by ring.
    replace ((-1) ^ (2 * a)) with 1 in Hpow1.
    - exact Hpow1.
    - rewrite Z.pow_mul_r; [| intro H; discriminate H | exact Ha0].
      rewrite Z.pow_2_r. replace ((-1) * (-1)) with 1 by ring.
      symmetry. apply Z.pow_1_l. exact Ha0. }
  assert (H2b0 : 0 <= 2 * b)
    by (apply Z.mul_nonneg_nonneg; [intro H; discriminate H | exact Hb0]).
  assert (Hp_2an4 : (p | 2 ^ (2 * a * n) - 4)).
  { pose proof (Hpow_cong (2 ^ (p - 1)) 1 (2 * b) H2b0 Hflt2) as Hpow2.
    rewrite <- Z.pow_mul_r in Hpow2; [| apply Z.lt_le_incl; exact Hp1_pos | exact H2b0].
    rewrite (Z.pow_1_l (2 * b) H2b0) in Hpow2.
    assert (Hpow2' : (p | 4 * (2 ^ ((p - 1) * (2 * b)) - 1))).
    { apply Z.divide_mul_r. exact Hpow2. }
    replace (4 * (2 ^ ((p - 1) * (2 * b)) - 1))
      with (2 ^ 2 * 2 ^ ((p - 1) * (2 * b)) - 4) in Hpow2'
      by (rewrite Z.pow_2_r; ring).
    rewrite <- Z.pow_add_r in Hpow2'.
    - replace (2 + (p - 1) * (2 * b)) with (2 * a * n) in Hpow2'
        by (transitivity (2 * (a * n)); [ring | rewrite Hab_eq; ring]).
      exact Hpow2'.
    - intro H. discriminate H.
    - apply Z.mul_nonneg_nonneg; [apply Z.lt_le_incl; exact Hp1_pos | exact H2b0]. }
  assert (Hp_3 : (p | 3)).
  { replace 3 with ((2 ^ (2 * a * n) - 1) - (2 ^ (2 * a * n) - 4)) by ring.
    apply Z.divide_sub_r; assumption. }
  assert (Hp_le_3 : p <= 3) by (apply Z.divide_pos_le; [reflexivity | exact Hp_3]).
  assert (Hp3 : p = 3).
  { destruct (proj1 (Z.lt_eq_cases p 3) Hp_le_3) as [Hlt | Heq]; [| exact Heq].
    change 3 with (Z.succ 2) in Hlt. rewrite Z.lt_succ_r in Hlt.
    destruct (proj1 (Z.lt_eq_cases p 2) Hlt) as [Hlt2 | Heq2].
    - change 2 with (Z.succ 1) in Hlt2. rewrite Z.lt_succ_r in Hlt2.
      exfalso. apply (Z.lt_irrefl 1). eapply Z.lt_le_trans; eassumption.
    - exfalso. apply Hp2. exact Heq2. }
  subst p.
  assert (H3_pow : (3 | 3 ^ n)).
  { replace n with (1 + (n - 1)) by ring.
    rewrite Z.pow_add_r;
      [rewrite Z.pow_1_r; apply Z.divide_factor_l
      | intro H; discriminate H
      | apply Z.le_0_sub; apply (proj2 (Z.le_succ_l 0 n)); exact hn]. }
  assert (H3_1 : (3 | 1)).
  { replace 1 with ((3 ^ n + 1) - 3 ^ n) by ring.
    apply Z.divide_sub_r; [apply (Z.divide_trans _ _ _ Hpn h3) | exact H3_pow]. }
  destruct (Z.divide_1_r 3 H3_1) as [Habs | Habs]; discriminate Habs.
Qed.
```
