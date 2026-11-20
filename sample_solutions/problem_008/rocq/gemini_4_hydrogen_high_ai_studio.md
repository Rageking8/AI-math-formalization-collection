# Gemini 4 Hydrogen High (AI Studio)

Model: `Gemini 4 Hydrogen High` (via AI Studio)\
Date: `20 November 2026`\
Line count: `340`\
Turn count: `7`

## Note

This solution uses `vm_compute`.

## Solution

```rocq
From Stdlib Require Import ZArith Znumtheory Lia List Permutation.
Open Scope Z_scope.

Lemma mod_0_divide : forall a b : Z, a mod b = 0 -> b <> 0 -> (b | a).
Proof. intros a b H Hb. apply Z.mod_divide; assumption. Qed.

Lemma divide_mod_0 : forall a b : Z, (b | a) -> b <> 0 -> a mod b = 0.
Proof. intros a b H Hb. apply Z.mod_divide in H; assumption. Qed.

Lemma not_div_4_y_sq_plus_1 : forall y : Z, ~ (4 | y ^ 2 + 1).
Proof.
  intros y [k Hk].
  pose proof (Z.div_mod y 4 ltac:(lia)) as Hy.
  pose proof (Z.mod_pos_bound y 4 ltac:(lia)) as Hmod.
  set (q := y / 4) in *.
  set (r := y mod 4) in *.
  assert (Hr : r = 0 \/ r = 1 \/ r = 2 \/ r = 3) by lia.
  rewrite Hy, Z.pow_2_r in Hk.
  assert (Heq : (4 * q + r) * (4 * q + r) + 1 =
                4 * (4 * (q * q) + 2 * (q * r)) + (r * r + 1)) by ring.
  rewrite Heq in Hk.
  set (t := 4 * (q * q) + 2 * (q * r)) in Hk.
  destruct Hr as [-> | [-> | [-> | ->]]]; lia.
Qed.

Lemma exists_prime_3_mod_4 : forall n : Z,
  0 < n -> n mod 4 = 3 -> exists p : Z, prime p /\ p mod 4 = 3 /\ (p | n).
Proof.
  assert (Hgen : forall k : nat, forall n : Z,
    0 < n -> (Z.to_nat n <= k)%nat -> n mod 4 = 3 ->
    exists p : Z, prime p /\ p mod 4 = 3 /\ (p | n)).
  { induction k as [| k IH]; intros n Hpos Hle Hmod.
    - lia.
    - assert (Hn3 : 3 <= n).
      { pose proof (Z.div_mod n 4 ltac:(lia)). lia. }
      remember (existsb (fun d => n mod Z.of_nat d =? 0)
                        (seq 2 (Z.to_nat (n - 2)))) as b eqn:Hb.
      destruct b.
      + symmetry in Hb. rewrite existsb_exists in Hb.
        destruct Hb as [d [Hd Hdiv]].
        rewrite in_seq in Hd.
        apply Z.eqb_eq in Hdiv.
        set (a := Z.of_nat d) in *.
        assert (Ha_bnd : 1 < a < n) by lia.
        assert (Ha_div : (a | n)) by (apply mod_0_divide; [exact Hdiv | lia]).
        destruct Ha_div as [c Hc_eq].
        assert (Hc_bnd : 1 < c < n) by nia.
        pose proof (Z.mod_pos_bound a 4 ltac:(lia)) as Ha_mb.
        pose proof (Z.mod_pos_bound c 4 ltac:(lia)) as Hc_mb.
        assert (Hmod_ac : ((c mod 4) * (a mod 4)) mod 4 = 3).
        { rewrite <- Z.mul_mod by lia. rewrite <- Hc_eq. exact Hmod. }
        assert (Ha3_dec : a mod 4 = 3 \/ a mod 4 <> 3) by lia.
        destruct Ha3_dec as [Ha3 | Ha_not3].
        * destruct (IH a ltac:(lia) ltac:(lia) Ha3) as [p [Hp [Hpmod Hpa]]].
          exists p. split; [exact Hp | split; [exact Hpmod |]].
          apply Z.divide_trans with a; [exact Hpa | exists c; exact Hc_eq].
        * assert (Hc3_dec : c mod 4 = 3 \/ c mod 4 <> 3) by lia.
          destruct Hc3_dec as [Hc3 | Hc_not3].
          -- destruct (IH c ltac:(lia) ltac:(lia) Hc3) as [p [Hp [Hpmod Hpc]]].
             exists p. split; [exact Hp | split; [exact Hpmod |]].
             apply Z.divide_trans with c;
               [exact Hpc | exists a; rewrite Hc_eq; ring].
          -- assert (Hra : a mod 4 = 0 \/ a mod 4 = 1 \/ a mod 4 = 2) by lia.
             assert (Hrc : c mod 4 = 0 \/ c mod 4 = 1 \/ c mod 4 = 2) by lia.
             destruct Hra as [Hra | [Hra | Hra]];
               destruct Hrc as [Hrc | [Hrc | Hrc]];
               rewrite Hra, Hrc in Hmod_ac;
               vm_compute in Hmod_ac; discriminate Hmod_ac.
      + exists n. split; [| split; [exact Hmod | apply Z.divide_refl]].
        apply prime_alt. split; [lia |].
        intros m Hm Hdiv.
        assert (Hin : In (Z.to_nat m) (seq 2 (Z.to_nat (n - 2)))).
        { rewrite in_seq. lia. }
        destruct (n mod Z.of_nat (Z.to_nat m) =? 0) eqn:E.
        * assert (Htrue : existsb (fun d => n mod Z.of_nat d =? 0)
                                  (seq 2 (Z.to_nat (n - 2))) = true).
          { apply existsb_exists. exists (Z.to_nat m). split; assumption. }
          congruence.
        * replace (Z.of_nat (Z.to_nat m)) with m in E by lia.
          pose proof (divide_mod_0 _ _ Hdiv ltac:(lia)) as Hdiv0.
          rewrite Hdiv0 in E. simpl in E. discriminate E. }
  intros n Hpos Hmod. apply (Hgen (Z.to_nat n) n Hpos); [lia | exact Hmod].
Qed.

Lemma pow_mod_cong : forall a b e p : Z,
  0 <= e -> 0 < p -> a mod p = b mod p -> (a ^ e) mod p = (b ^ e) mod p.
Proof.
  intros a b e p He Hp Hcong.
  remember (Z.to_nat e) as n eqn:Hn.
  assert (Heq : e = Z.of_nat n) by lia.
  rewrite Heq. clear He Hn Heq e.
  induction n as [| n IH].
  - simpl. reflexivity.
  - rewrite Nat2Z.inj_succ.
    rewrite !Z.pow_succ_r by lia.
    rewrite Z.mul_mod by lia.
    rewrite (Z.mul_mod b (b ^ Z.of_nat n) p) by lia.
    rewrite Hcong, IH. reflexivity.
Qed.

Lemma divide_sub_mod_eq : forall a b p : Z,
  0 < p -> (p | a - b) -> a mod p = b mod p.
Proof.
  intros a b p Hp [k Hk].
  pose proof (Z.div_mod a p ltac:(lia)) as Ha.
  pose proof (Z.div_mod b p ltac:(lia)) as Hb.
  pose proof (Z.mod_pos_bound a p Hp) as Hba.
  pose proof (Z.mod_pos_bound b p Hp) as Hbb.
  set (ra := a mod p) in *. set (rb := b mod p) in *.
  set (qa := a / p) in *. set (qb := b / p) in *.
  assert (Hdiff : ra - rb = (k - qa + qb) * p).
  { replace (ra - rb) with (a - b - (qa - qb) * p).
    - rewrite Hk. ring.
    - rewrite Ha, Hb. ring. }
  assert (Hz : k - qa + qb <= -1 \/ k - qa + qb = 0 \/ 1 <= k - qa + qb) by lia.
  destruct Hz as [Hz | [Hz | Hz]]; nia.
Qed.

Lemma NoDup_map_inj_in {A B : Type} (g : A -> B) (l : list A) :
  (forall x y, In x l -> In y l -> g x = g y -> x = y) ->
  NoDup l -> NoDup (map g l).
Proof.
  intros Hinj Hnd. induction l as [| a l IH]; simpl.
  - constructor.
  - inversion Hnd; subst. constructor.
    + rewrite in_map_iff. intros [x [Heq Hinx]].
      assert (a = x).
      { apply Hinj; [left; reflexivity | right; exact Hinx | symmetry; exact Heq]. }
      subst. contradiction.
    + apply IH; auto. intros x y Hx Hy. apply Hinj; simpl; auto.
Qed.

Definition prod_Z (l : list Z) : Z := fold_right Z.mul 1 l.

Lemma prod_Z_Permutation : forall l1 l2 : list Z,
  Permutation l1 l2 -> prod_Z l1 = prod_Z l2.
Proof.
  unfold prod_Z. induction 1; simpl; try ring; congruence.
Qed.

Lemma prod_Z_map_mul_mod : forall y p : Z, 0 < p ->
  forall l : list Z,
    prod_Z (map (fun k => (y * k) mod p) l) mod p =
    (y ^ Z.of_nat (length l) * prod_Z l) mod p.
Proof.
  intros y p Hp l. induction l as [| a l IH]; unfold prod_Z in *.
  - reflexivity.
  - change (length (a :: l)) with (S (length l)).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    cbn [map fold_right].
    rewrite Z.mul_mod by lia.
    rewrite Z.mod_mod by lia.
    rewrite IH.
    rewrite <- Z.mul_mod by lia.
    f_equal. ring.
Qed.

Lemma prime_not_divide_prod_Z : forall p : Z, prime p ->
  forall l : list Z, (forall k, In k l -> ~ (p | k)) -> ~ (p | prod_Z l).
Proof.
  intros p Hp l. induction l as [| a l IH]; intros Hl; unfold prod_Z in *; simpl.
  - intros [q Hq]. pose proof (prime_ge_2 p Hp).
    assert (Hq_dec : q <= 0 \/ 1 <= q) by lia.
    destruct Hq_dec; nia.
  - intros Hdiv. destruct (prime_mult p Hp _ _ Hdiv) as [Ha | Hrest].
    + apply (Hl a); [left; reflexivity | exact Ha].
    + apply IH; [| exact Hrest].
      intros k Hk. apply Hl. right; exact Hk.
Qed.

Lemma prime_3_mod_4_no_sq_plus_one : forall p y : Z,
  prime p -> p mod 4 = 3 -> ~ (p | y ^ 2 + 1).
Proof.
  intros p y Hp Hpmod Hdiv.
  assert (Hp3 : 3 <= p).
  { pose proof (prime_ge_2 p Hp).
    pose proof (Z.div_mod p 4 ltac:(lia)). lia. }
  assert (Hny : ~ (p | y)).
  { intros [k Hk].
    destruct Hdiv as [m Hm].
    rewrite Hk, Z.pow_2_r in Hm.
    assert (H1 : (m - k * k * p) * p = 1).
    { replace ((m - k * k * p) * p) with (m * p - (k * p) * (k * p)) by ring.
      rewrite <- Hm. ring. }
    assert (Hdec : m - k * k * p <= 0 \/ 1 <= m - k * k * p) by lia.
    destruct Hdec; nia. }
  set (y' := y mod p).
  assert (Hy'_bnd : 0 < y' < p).
  { unfold y'. pose proof (Z.mod_pos_bound y p ltac:(lia)).
    assert (y mod p <> 0).
    { intro Hz. apply Hny. exact (mod_0_divide _ _ Hz ltac:(lia)). }
    lia. }
  assert (Hny' : ~ (p | y')).
  { intros Hdiv'. pose proof (divide_mod_0 _ _ Hdiv' ltac:(lia)) as Hdiv0.
    rewrite Z.mod_small in Hdiv0 by lia. lia. }
  assert (Hy'_div : (p | y' ^ 2 + 1)).
  { destruct Hdiv as [m Hm].
    pose proof (Z.div_mod y p ltac:(lia)) as Hy_dm.
    fold y' in Hy_dm.
    exists (m - p * (y / p) ^ 2 - 2 * (y / p) * y').
    rewrite Hy_dm in Hm.
    rewrite Z.pow_2_r in *.
    transitivity ((p * (y / p) + y') * (p * (y / p) + y') + 1 -
                  (p * ((y / p) * (y / p)) + 2 * (y / p) * y') * p).
    - ring.
    - rewrite Hm. ring. }
  set (m := Z.to_nat (p - 1)).
  set (L := map Z.of_nat (seq 1 m)).
  set (f := fun k : Z => (y' * k) mod p).
  assert (HL_in : forall k, In k L <-> 1 <= k < p).
  { intro k. unfold L. rewrite in_map_iff. split.
    - intros [n [Hn Hin]]. rewrite in_seq in Hin. unfold m in Hin. lia.
    - intro Hk. exists (Z.to_nat k). split; [lia |].
      rewrite in_seq. unfold m. lia. }
  assert (HL_nd : NoDup L).
  { unfold L. apply NoDup_map_inj_in.
    - intros a b _ _ Hab. lia.
    - apply seq_NoDup. }
  assert (Hf_incl : incl (map f L) L).
  { intros z Hz. rewrite in_map_iff in Hz. destruct Hz as [k [Hk Hink]].
    rewrite HL_in in Hink.
    rewrite HL_in. unfold f in Hk. subst z.
    pose proof (Z.mod_pos_bound (y' * k) p ltac:(lia)) as Hbnd.
    assert ((y' * k) mod p <> 0).
    { intro Hz. pose proof (mod_0_divide _ _ Hz ltac:(lia)) as Hz_div.
      destruct (prime_mult p Hp _ _ Hz_div) as [Hpy' | Hpk].
      - contradiction.
      - pose proof (divide_mod_0 _ _ Hpk ltac:(lia)) as Hpk0.
        rewrite Z.mod_small in Hpk0 by lia. lia. }
    lia. }
  assert (Hf_nd : NoDup (map f L)).
  { apply NoDup_map_inj_in; [| exact HL_nd].
    intros a b Ha Hb Hab.
    rewrite HL_in in Ha, Hb.
    unfold f in Hab.
    assert (Hdiv_diff : (p | y' * (a - b))).
    { pose proof (Z.div_mod (y' * a) p ltac:(lia)) as Ha_dm.
      pose proof (Z.div_mod (y' * b) p ltac:(lia)) as Hb_dm.
      exists ((y' * a) / p - (y' * b) / p).
      transitivity ((p * ((y' * a) / p) + (y' * a) mod p) -
                    (p * ((y' * b) / p) + (y' * b) mod p)).
      - rewrite <- Ha_dm, <- Hb_dm. ring.
      - rewrite Hab. ring. }
    destruct (prime_mult p Hp _ _ Hdiv_diff) as [Hpy' | [q Hq]];
      [contradiction |].
    assert (Hq_dec : q <= -1 \/ q = 0 \/ 1 <= q) by lia.
    destruct Hq_dec as [Hq_dec | [Hq_dec | Hq_dec]]; nia. }
  assert (Hperm : Permutation (map f L) L).
  { apply Permutation_map_same_l; assumption. }
  assert (Hprod_eq : (y' ^ (p - 1) * prod_Z L) mod p = (prod_Z L) mod p).
  { pose proof (prod_Z_Permutation _ _ Hperm) as Hpeq.
    pose proof (prod_Z_map_mul_mod y' p ltac:(lia) L) as Hpm.
    unfold f in Hpeq.
    rewrite Hpeq in Hpm.
    replace (Z.of_nat (length L)) with (p - 1) in Hpm.
    - symmetry. exact Hpm.
    - unfold L. rewrite length_map, length_seq. unfold m. lia. }
  assert (Hflt : (p | y' ^ (p - 1) - 1)).
  { assert (Hprod_div : (p | (y' ^ (p - 1) - 1) * prod_Z L)).
    { pose proof (Z.div_mod (y' ^ (p - 1) * prod_Z L) p ltac:(lia)) as H1.
      pose proof (Z.div_mod (prod_Z L) p ltac:(lia)) as H2.
      exists ((y' ^ (p - 1) * prod_Z L) / p - (prod_Z L) / p).
      transitivity ((p * ((y' ^ (p - 1) * prod_Z L) / p) +
                     (y' ^ (p - 1) * prod_Z L) mod p) -
                    (p * ((prod_Z L) / p) + (prod_Z L) mod p)).
      - rewrite <- H1, <- H2. ring.
      - rewrite Hprod_eq. ring. }
    destruct (prime_mult p Hp _ _ Hprod_div) as [Hres | Hbad]; [exact Hres |].
    exfalso. revert Hbad. apply prime_not_divide_prod_Z; [exact Hp |].
    intros k Hk. rewrite HL_in in Hk.
    intro Hpk. pose proof (divide_mod_0 _ _ Hpk ltac:(lia)) as Hpk0.
    rewrite Z.mod_small in Hpk0 by lia. lia. }
  pose proof (Z.div_mod p 4 ltac:(lia)) as Hp_dm.
  rewrite Hpmod in Hp_dm.
  set (q := p / 4) in *.
  assert (Hq : 0 <= q) by lia.
  assert (Hp1 : p - 1 = 2 * (2 * q + 1)) by lia.
  assert (Hy'_pow : (y' ^ (p - 1)) mod p = (-1) mod p).
  { rewrite Hp1.
    rewrite Z.pow_mul_r by lia.
    rewrite (pow_mod_cong (y' ^ 2) (-1) (2 * q + 1) p ltac:(lia) ltac:(lia)).
    - replace ((-1) ^ (2 * q + 1)) with (-1).
      + reflexivity.
      + rewrite Z.pow_add_r by lia.
        rewrite Z.pow_mul_r by lia.
        replace ((-1) ^ 2) with 1 by reflexivity.
        rewrite Z.pow_1_l by lia.
        rewrite Z.pow_1_r. ring.
    - apply divide_sub_mod_eq; [lia |].
      replace (y' ^ 2 - -1) with (y' ^ 2 + 1) by ring.
      exact Hy'_div. }
  apply divide_sub_mod_eq in Hflt; [| lia].
  rewrite Hy'_pow in Hflt.
  pose proof (Z.div_mod 1 p ltac:(lia)) as H1.
  pose proof (Z.div_mod (-1) p ltac:(lia)) as Hm1.
  assert (H2 : 1 - (-1) = (1 / p - (-1) / p) * p).
  { transitivity ((p * (1 / p) + 1 mod p) - (p * ((-1) / p) + (-1) mod p)).
    - rewrite <- H1, <- Hm1. reflexivity.
    - rewrite Hflt. ring. }
  assert (Hdec : 1 / p - (-1) / p <= 0 \/ 1 <= 1 / p - (-1) / p) by lia.
  destruct Hdec; nia.
Qed.

Theorem no_x_sq_plus_two_x_dvd_y_sq_plus_one (x y : Z) (hx : 0 < x)
    (hy : 0 < y) : ~ (x ^ 2 + 2 * x | y ^ 2 + 1).
Proof.
  intro Hdiv.
  pose proof (Z.div_mod x 4 ltac:(lia)) as Hx.
  pose proof (Z.mod_pos_bound x 4 ltac:(lia)) as Hx_bnd.
  set (qx := x / 4) in *.
  set (rx := x mod 4) in *.
  assert (Hrx : rx = 0 \/ rx = 1 \/ rx = 2 \/ rx = 3) by lia.
  destruct Hrx as [Hrx | [Hrx | [Hrx | Hrx]]].
  - apply (not_div_4_y_sq_plus_1 y).
    apply Z.divide_trans with (x ^ 2 + 2 * x); [| exact Hdiv].
    exists (4 * qx * qx + 2 * qx).
    rewrite Z.pow_2_r, Hx, Hrx. ring.
  - assert (Hx2_div : (x + 2 | y ^ 2 + 1)).
    { apply Z.divide_trans with (x ^ 2 + 2 * x); [| exact Hdiv].
      exists x. rewrite Z.pow_2_r. ring. }
    assert (Hx2_mod : (x + 2) mod 4 = 3).
    { rewrite <- (Z.mod_small 3 4 ltac:(lia)).
      apply divide_sub_mod_eq; [lia |].
      exists qx. rewrite Hx, Hrx. ring. }
    destruct (exists_prime_3_mod_4 (x + 2) ltac:(lia) Hx2_mod)
      as [p [Hp [Hpmod Hpx]]].
    apply (prime_3_mod_4_no_sq_plus_one p y Hp Hpmod).
    apply Z.divide_trans with (x + 2); assumption.
  - apply (not_div_4_y_sq_plus_1 y).
    apply Z.divide_trans with (x ^ 2 + 2 * x); [| exact Hdiv].
    exists (4 * qx * qx + 6 * qx + 2).
    rewrite Z.pow_2_r, Hx, Hrx. ring.
  - assert (Hx_div : (x | y ^ 2 + 1)).
    { apply Z.divide_trans with (x ^ 2 + 2 * x); [| exact Hdiv].
      exists (x + 2). rewrite Z.pow_2_r. ring. }
    assert (Hx_mod : x mod 4 = 3) by exact Hrx.
    destruct (exists_prime_3_mod_4 x hx Hx_mod) as [p [Hp [Hpmod Hpx]]].
    apply (prime_3_mod_4_no_sq_plus_one p y Hp Hpmod).
    apply Z.divide_trans with x; assumption.
Qed.
```
