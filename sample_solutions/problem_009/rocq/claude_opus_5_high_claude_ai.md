# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `26 November 2026`\
Line count: `355`\
Turn count: `2`

## Solution

```rocq
From Stdlib Require Import ZArith.
Open Scope Z_scope.

From Stdlib Require Import Znumtheory Lia List Permutation.

(* ================ generic divisibility / power helpers ================ *)

Lemma pow_congr (d a b : Z) :
  (d | a - b) -> forall k, 0 <= k -> (d | a ^ k - b ^ k).
Proof.
  intros [e He] k Hk.
  pattern k; apply natlike_ind; [| | exact Hk].
  - rewrite !Z.pow_0_r. exists 0; ring.
  - intros x Hx [c Hc]. rewrite !Z.pow_succ_r by exact Hx.
    exists (a * c + b ^ x * e).
    replace (a * a ^ x - b * b ^ x)
      with (a * (a ^ x - b ^ x) + b ^ x * (a - b)) by ring.
    rewrite Hc, He. ring.
Qed.

Lemma pow_m1 : forall k, 0 <= k -> (-1) ^ k = 1 \/ (-1) ^ k = -1.
Proof.
  intros k Hk. pattern k; apply natlike_ind; [| | exact Hk].
  - left. now rewrite Z.pow_0_r.
  - intros x Hx [H | H]; rewrite Z.pow_succ_r by exact Hx; rewrite H;
      [right | left]; ring.
Qed.

Lemma mod_divide_diff : forall z m, m <> 0 -> (m | z mod m - z).
Proof.
  intros z m Hm. exists (- (z / m)).
  assert (H := Z.div_mod z m Hm). lia.
Qed.

(* ================ least prime divisor ================ *)

Lemma least_div_aux :
  forall s, 0 <= s -> forall n k, 1 < n -> 1 < k -> k <= n -> n - k = s ->
    (forall e, 1 < e -> e < k -> ~ (e | n)) ->
    exists d, 1 < d /\ (d | n) /\ (forall e, 1 < e -> (e | n) -> d <= e).
Proof.
  intros s Hs; pattern s; apply Z_lt_induction; [| exact Hs].
  clear s Hs; intros s IH n k Hn Hk Hkn Hsk Hlow.
  assert (Hk0 : k <> 0) by lia.
  destruct (Z.eq_dec (n mod k) 0) as [Hz | Hz].
  - assert (Hd : (k | n)) by (apply (proj1 (Z.mod_divide n k Hk0)); exact Hz).
    exists k; split; [exact Hk | split; [exact Hd |]].
    intros e He1 He2.
    destruct (Z_lt_le_dec e k) as [Hlt | Hge].
    + exfalso; apply (Hlow e He1 Hlt He2).
    + exact Hge.
  - assert (Hnd : ~ (k | n)) by
      (intros Hd; apply Hz; apply (proj2 (Z.mod_divide n k Hk0)); exact Hd).
    assert (Hlt : k < n).
    { assert (k <> n) by (intros Heq; apply Hnd; exists 1; lia). lia. }
    assert (Hs' : 0 <= n - (k + 1) < s) by lia.
    assert (Hk' : 1 < k + 1) by lia.
    assert (Hkn' : k + 1 <= n) by lia.
    assert (Hsk' : n - (k + 1) = n - (k + 1)) by reflexivity.
    apply (IH _ Hs' n (k + 1) Hn Hk' Hkn' Hsk').
    intros e He1 He2.
    destruct (Z.eq_dec e k) as [Heq | Hne]; [rewrite Heq; exact Hnd | apply Hlow; lia].
Qed.

Lemma least_prime_div : forall n, 1 < n ->
  exists p, prime p /\ (p | n) /\ (forall e, 1 < e -> (e | n) -> p <= e).
Proof.
  intros n Hn.
  assert (H0 : 0 <= n - 2) by lia.
  assert (H2 : 1 < 2) by lia.
  assert (Hle : 2 <= n) by lia.
  assert (Hr : n - 2 = n - 2) by reflexivity.
  assert (Hv : forall e, 1 < e -> e < 2 -> ~ (e | n)) by (intros e He1 He2; lia).
  destruct (least_div_aux (n - 2) H0 n 2 Hn H2 Hle Hr Hv) as [d [Hd1 [Hd2 Hd3]]].
  exists d; split; [| split; [exact Hd2 | exact Hd3]].
  (* the least divisor > 1 is prime *)
  apply (proj1 (prime_alt d)). split; [exact Hd1 |].
  intros e [He1 He2] Hed.
  assert (He : (e | n)) by (apply (Z.divide_trans e d n Hed Hd2)).
  specialize (Hd3 e He1 He). lia.
Qed.

(* ================ lists [n; n-1; ...; 1] and their products ================ *)

Fixpoint zl (n : nat) : list Z :=
  match n with
  | O => nil
  | S k => Z.of_nat (S k) :: zl k
  end.

Fixpoint prodl (l : list Z) : Z :=
  match l with
  | nil => 1
  | x :: r => x * prodl r
  end.

Lemma zl_len : forall n, length (zl n) = n.
Proof. induction n as [|k IH]; simpl; auto. Qed.

Lemma map_len : forall (f : Z -> Z) (l : list Z), length (map f l) = length l.
Proof. intros f; induction l as [|x r IH]; simpl; auto. Qed.

Lemma zl_in : forall n x, In x (zl n) <-> 1 <= x <= Z.of_nat n.
Proof.
  induction n as [|k IH]; intros x.
  - cbn [zl]. split; [intros H; destruct H | intros H; exfalso; lia].
  - cbn [zl]. rewrite Nat2Z.inj_succ. split.
    + intros [He | Hin]; [lia | apply (proj1 (IH x)) in Hin; lia].
    + intros Hx. destruct (Z.eq_dec x (Z.succ (Z.of_nat k))) as [He | Hne].
      * left; lia.
      * right; apply (proj2 (IH x)); lia.
Qed.

Lemma zl_nodup : forall n, NoDup (zl n).
Proof.
  induction n as [|k IH]; cbn [zl].
  - constructor.
  - constructor; [| exact IH].
    intros Hin. apply (proj1 (zl_in k _)) in Hin.
    rewrite Nat2Z.inj_succ in Hin. lia.
Qed.

Lemma NoDup_map_inj : forall (f : Z -> Z) (l : list Z),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l -> NoDup (map f l).
Proof.
  intros f; induction l as [|x r IH]; intros Hinj Hnd; simpl.
  - constructor.
  - inversion Hnd as [| x' r' Hnotin Hndr]; subst.
    constructor.
    + intros Hin. apply in_map_iff in Hin. destruct Hin as [y [Hfy Hiny]].
      assert (Hxy : x = y).
      { apply Hinj; [left; reflexivity | right; exact Hiny | symmetry; exact Hfy]. }
      rewrite Hxy in Hnotin. apply Hnotin; exact Hiny.
    + apply IH; [| exact Hndr].
      intros u v Hu Hv Hfuv. apply Hinj; [right; exact Hu | right; exact Hv | exact Hfuv].
Qed.

Lemma prodl_perm : forall l1 l2, Permutation l1 l2 -> prodl l1 = prodl l2.
Proof.
  intros l1 l2 H.
  induction H as [| x l l' Hp IH | x y l | l l' l'' H1 IH1 H2 IH2].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. ring.
  - rewrite IH1; exact IH2.
Qed.

Lemma prodl_congr : forall (d : Z) (f g : Z -> Z) (l : list Z),
  (forall x, In x l -> (d | f x - g x)) ->
  (d | prodl (map f l) - prodl (map g l)).
Proof.
  intros d f g; induction l as [|x r IH]; intros H; simpl.
  - exists 0; ring.
  - destruct (IH (fun y Hy => H y (or_intror Hy))) as [c Hc].
    destruct (H x (or_introl eq_refl)) as [e He].
    exists (f x * c + prodl (map g r) * e).
    replace (f x * prodl (map f r) - g x * prodl (map g r))
      with (f x * (prodl (map f r) - prodl (map g r))
            + prodl (map g r) * (f x - g x)) by ring.
    rewrite Hc, He. ring.
Qed.

Lemma prodl_scal : forall (a : Z) (l : list Z),
  prodl (map (fun x => a * x) l) = a ^ (Z.of_nat (length l)) * prodl l.
Proof.
  intros a; induction l as [|x r IH]; cbn [prodl map length].
  - replace (Z.of_nat 0%nat) with 0 by reflexivity. rewrite Z.pow_0_r. ring.
  - rewrite IH. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia. ring.
Qed.

Lemma prodl_not_div : forall (p : Z), prime p -> forall l,
  (forall x, In x l -> ~ (p | x)) -> ~ (p | prodl l).
Proof.
  intros p Hp; induction l as [|x r IH]; simpl; intros H Hdiv.
  - assert (Hp2 : 2 <= p) by (apply prime_ge_2; exact Hp).
    apply Z.divide_1_r in Hdiv. lia.
  - destruct (prime_mult p Hp x (prodl r) Hdiv) as [H1 | H2].
    + apply (H x (or_introl eq_refl) H1).
    + apply IH; [intros y Hy; apply (H y (or_intror Hy)) | exact H2].
Qed.

(* ================ Fermat's little theorem ================ *)

Lemma fermat_little : forall p a, prime p -> ~ (p | a) -> (p | a ^ (p - 1) - 1).
Proof.
  intros p a Hp Ha.
  assert (Hp2 : 2 <= p) by (apply prime_ge_2; exact Hp).
  assert (Hpne : p <> 0) by lia.
  (* L is the list of the nonzero residues 1, ..., p-1 *)
  pose (L := zl (Z.to_nat (p - 1))).
  assert (HLin : forall x, In x L -> 1 <= x <= p - 1).
  { intros x Hx. apply (proj1 (zl_in _ x)) in Hx.
    rewrite Z2Nat.id in Hx by lia. exact Hx. }
  assert (HLin2 : forall x, 1 <= x <= p - 1 -> In x L).
  { intros x Hx. apply (proj2 (zl_in _ x)). rewrite Z2Nat.id by lia. exact Hx. }
  assert (Hnd : forall x, 1 <= x <= p - 1 -> ~ (p | x)).
  { intros x Hx Hdx.
    assert (p <= x) by (apply Z.divide_pos_le; [lia | exact Hdx]). lia. }
  assert (Hrp : rel_prime p a) by (apply prime_rel_prime; assumption).
  (* multiplication by a permutes those residues *)
  pose (f := fun x => (a * x) mod p).
  assert (HfL : forall x, In x L -> In (f x) L).
  { intros x Hx. apply HLin in Hx. apply HLin2.
    assert (Hb : 0 <= (a * x) mod p < p) by (apply Z.mod_pos_bound; lia).
    unfold f. split; [| lia].
    destruct (Z.eq_dec ((a * x) mod p) 0) as [Hz | Hz]; [| lia].
    exfalso. apply (proj1 (Z.mod_divide (a * x) p Hpne)) in Hz.
    apply Ha. apply (Gauss p x a).
    - rewrite Z.mul_comm. exact Hz.
    - apply prime_rel_prime; [exact Hp | apply Hnd; exact Hx]. }
  assert (Hinj : forall x y, In x L -> In y L -> f x = f y -> x = y).
  { intros x y Hx Hy Hf. apply HLin in Hx; apply HLin in Hy.
    assert (Hd : (p | a * x - a * y)).
    { destruct (mod_divide_diff (a * x) p Hpne) as [c1 Hc1].
      destruct (mod_divide_diff (a * y) p Hpne) as [c2 Hc2].
      unfold f in Hf. exists (c2 - c1). lia. }
    assert (Hd2 : (p | x - y)).
    { apply (Gauss p a (x - y)); [| exact Hrp].
      replace (a * (x - y)) with (a * x - a * y) by ring. exact Hd. }
    destruct (Z.lt_trichotomy x y) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
    - exfalso. assert (p <= y - x).
      { apply Z.divide_pos_le; [lia |].
        destruct Hd2 as [c Hc]; exists (- c); lia. }
      lia.
    - exfalso.
      assert (p <= x - y) by (apply Z.divide_pos_le; [lia | exact Hd2]). lia. }
  assert (Hperm : Permutation (map f L) L).
  { apply NoDup_Permutation_bis.
    - apply NoDup_map_inj; [exact Hinj | apply zl_nodup].
    - rewrite map_len. lia.
    - intros x Hx. apply in_map_iff in Hx. destruct Hx as [y [Hy Hiny]].
      rewrite <- Hy. apply HfL; exact Hiny. }
  (* so the two products agree, which gives a^(p-1) = 1 after cancellation *)
  assert (HL1 : prodl (map f L) = prodl L) by (apply prodl_perm; exact Hperm).
  assert (HL2 : (p | prodl (map f L) - prodl (map (fun x => a * x) L))).
  { apply prodl_congr. intros x Hx. unfold f. apply mod_divide_diff; exact Hpne. }
  assert (HL3 : prodl (map (fun x => a * x) L) = a ^ (p - 1) * prodl L).
  { rewrite prodl_scal.
    replace (Z.of_nat (length L)) with (p - 1); [reflexivity |].
    unfold L. rewrite zl_len. rewrite Z2Nat.id by lia. reflexivity. }
  assert (Hnotdiv : ~ (p | prodl L)).
  { apply prodl_not_div; [exact Hp |].
    intros x Hx. apply Hnd. apply HLin; exact Hx. }
  assert (Hfin : (p | prodl L * (1 - a ^ (p - 1)))).
  { destruct HL2 as [c Hc]. rewrite HL1, HL3 in Hc. exists c. lia. }
  assert (Hdiv1 : (p | 1 - a ^ (p - 1))).
  { apply (Gauss p (prodl L) (1 - a ^ (p - 1))); [exact Hfin |].
    apply prime_rel_prime; assumption. }
  destruct Hdiv1 as [c Hc]. exists (- c). lia.
Qed.

(* ================ main theorem ================ *)

Theorem eq_one_of_dvd_pow_add_one (n : Z) (hn : 0 < n)
    (h2 : (n | 2 ^ n + 1)) (h3 : (n | 3 ^ n + 1)) : n = 1.
Proof.
  destruct (Z.eq_dec n 1) as [Heq | Hne]; [exact Heq |].
  exfalso.
  assert (Hn1 : 1 < n) by lia.
  (* n is odd, since 2^n + 1 is odd *)
  assert (Hodd : ~ (2 | n)).
  { intros H2n.
    assert (Ha : (2 | 2 ^ n + 1)) by (apply (Z.divide_trans 2 n (2 ^ n + 1) H2n h2)).
    assert (Hb : (2 | 2 ^ n)).
    { exists (2 ^ (n - 1)). replace n with (n - 1 + 1) at 1 by lia.
      rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. reflexivity. }
    destruct Ha as [c Hc]; destruct Hb as [e He]. lia. }
  (* n divides 6^n - 1, because 6^n - 1 = (2^n+1)(3^n+1) - (2^n+1) - (3^n+1) *)
  assert (H6 : (n | 6 ^ n - 1)).
  { destruct h2 as [c Hc]; destruct h3 as [e He].
    exists (c * e * n - c - e).
    assert (Hmul : 6 ^ n = 2 ^ n * 3 ^ n).
    { replace (6:Z) with (2 * 3) by reflexivity. apply Z.pow_mul_l. }
    rewrite Hmul.
    assert (H2' : 2 ^ n = c * n - 1) by lia.
    assert (H3' : 3 ^ n = e * n - 1) by lia.
    rewrite H2', H3'. ring. }
  (* let p be the least prime divisor of n *)
  destruct (least_prime_div n Hn1) as [p [Hp [Hpn Hmin]]].
  assert (Hp2 : 2 <= p) by (apply prime_ge_2; exact Hp).
  assert (Hp6 : (p | 6 ^ n - 1)) by (apply (Z.divide_trans p n (6 ^ n - 1) Hpn H6)).
  assert (Hnd6 : ~ (p | 6)).
  { intros Hd6.
    assert (Hd6n : (p | 6 ^ n)).
    { apply (Z.divide_trans p 6 (6 ^ n) Hd6). exists (6 ^ (n - 1)).
      replace n with (n - 1 + 1) at 1 by lia.
      rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. reflexivity. }
    destruct Hp6 as [c Hc]; destruct Hd6n as [e He].
    assert (Hp1 : (p | 1)) by (exists (e - c); lia).
    apply Z.divide_1_r in Hp1. lia. }
  assert (Hferm : (p | 6 ^ (p - 1) - 1)) by (apply fermat_little; assumption).
  (* n and p-1 are coprime: a common divisor > 1 would be a divisor of n
     smaller than p *)
  assert (Hgcd : Z.gcd n (p - 1) = 1).
  { assert (G1 : (Z.gcd n (p - 1) | n)) by apply Z.gcd_divide_l.
    assert (G2 : (Z.gcd n (p - 1) | p - 1)) by apply Z.gcd_divide_r.
    assert (G0 : 0 <= Z.gcd n (p - 1)) by apply Z.gcd_nonneg.
    destruct (Z.eq_dec (Z.gcd n (p - 1)) 0) as [Hz | Hz].
    - exfalso. apply Z.gcd_eq_0_l in Hz. lia.
    - destruct (Z.eq_dec (Z.gcd n (p - 1)) 1) as [H1 | H1]; [exact H1 |].
      exfalso.
      assert (Hgt : 1 < Z.gcd n (p - 1)) by lia.
      assert (p <= Z.gcd n (p - 1)) by (apply Hmin; assumption).
      assert (Z.gcd n (p - 1) <= p - 1) by (apply Z.divide_pos_le; [lia | exact G2]).
      lia. }
  (* hence n*u = 1 + (p-1)*k for some u, k >= 0 *)
  assert (Hex : exists u k, 0 <= u /\ 0 <= k /\ n * u = 1 + (p - 1) * k).
  { assert (Hrel : rel_prime n (p - 1)) by (apply Zgcd_1_rel_prime; exact Hgcd).
    destruct (rel_prime_bezout n (p - 1) Hrel) as [u0 v0 Hb].
    pose (t := Z.abs u0 + Z.abs v0 + 1).
    assert (Ht : 1 <= t) by (unfold t; lia).
    exists (u0 + t * (p - 1)), (t * n - v0). repeat split.
    - assert (t * 1 <= t * (p - 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
      unfold t in *; lia.
    - assert (t * 1 <= t * n) by (apply Z.mul_le_mono_nonneg_l; lia).
      unfold t in *; lia.
    - lia. }
  destruct Hex as [u [k [Hu [Hk Hun]]]].
  (* 6^(n*u) is congruent to 1 (as 6^n is) and to 6 (by Fermat), so p | 5 *)
  assert (HA : (p | 6 ^ (n * u) - 1)).
  { rewrite Z.pow_mul_r by lia.
    assert (H1u : (1:Z) ^ u = 1) by (apply Z.pow_1_l; lia).
    destruct (pow_congr p (6 ^ n) 1 Hp6 u Hu) as [c Hc].
    rewrite H1u in Hc. exists c. lia. }
  assert (HB : (p | 6 ^ (n * u) - 6)).
  { assert (Hk1 : 0 <= (p - 1) * k) by (apply Z.mul_nonneg_nonneg; lia).
    rewrite Hun. rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r.
    rewrite Z.pow_mul_r by lia.
    destruct (pow_congr p (6 ^ (p - 1)) 1 Hferm k Hk) as [c Hc].
    rewrite Z.pow_1_l in Hc by lia.
    exists (6 * c). lia. }
  assert (Hp5 : (p | 5)).
  { destruct HA as [c1 Hc1]; destruct HB as [c2 Hc2]. exists (c1 - c2). lia. }
  assert (Hpeq : p = 5).
  { assert (Hle : p <= 5) by (apply Z.divide_pos_le; [lia | exact Hp5]).
    destruct Hp5 as [c Hc].
    assert (Hcase : p = 2 \/ p = 3 \/ p = 4 \/ p = 5) by lia.
    destruct Hcase as [H | [H | [H | H]]]; rewrite H in Hc; lia. }
  (* but 5 | n and n odd contradict 5 | 2^n + 1 *)
  rewrite Hpeq in Hpn.
  assert (H52 : (5 | 2 ^ n + 1)) by (apply (Z.divide_trans 5 n (2 ^ n + 1) Hpn h2)).
  destruct (Z.Even_or_Odd n) as [[m Hm] | [m Hm]].
  - apply Hodd. exists m. lia.
  - assert (Hm0 : 0 <= m) by lia.
    assert (Hpow : 2 ^ n = 2 * 4 ^ m).
    { replace n with (1 + 2 * m) by lia. rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r. rewrite Z.pow_mul_r by lia.
      replace (2 ^ 2) with 4 by reflexivity. reflexivity. }
    assert (H4 : (5 | 4 ^ m - (-1) ^ m)).
    { apply pow_congr; [exists 1; lia | exact Hm0]. }
    destruct (pow_m1 m Hm0) as [He | He]; rewrite He in H4;
      destruct H52 as [c1 Hc1]; destruct H4 as [c2 Hc2];
      rewrite Hpow in Hc1; lia.
Qed.
```
