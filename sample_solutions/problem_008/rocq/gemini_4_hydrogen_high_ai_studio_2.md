# Gemini 4 Hydrogen High (AI Studio)

Model: `Gemini 4 Hydrogen High` (via AI Studio)\
Date: `21 November 2026`\
Line count: `511`\
Turn count: `13`

## Solution

```rocq
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Theorem no_x_sq_plus_two_x_dvd_y_sq_plus_one (x y : Z) (hx : 0 < x)
    (hy : 0 < y) : ~ (x ^ 2 + 2 * x | y ^ 2 + 1).
Proof.
  intro Hdiv.
  assert (Hmod4_cases : forall r, 0 <= r < 4 -> r = 0 \/ r = 1 \/ r = 2 \/ r = 3).
  {
    intros r [Hr0 Hr4].
    change 4 with (Z.succ 3) in Hr4; rewrite Z.lt_succ_r, Z.le_lteq in Hr4.
    destruct Hr4 as [Hr3 | ->]; [| right; right; right; reflexivity].
    change 3 with (Z.succ 2) in Hr3; rewrite Z.lt_succ_r, Z.le_lteq in Hr3.
    destruct Hr3 as [Hr2 | ->]; [| right; right; left; reflexivity].
    change 2 with (Z.succ 1) in Hr2; rewrite Z.lt_succ_r, Z.le_lteq in Hr2.
    destruct Hr2 as [Hr1 | ->]; [| right; left; reflexivity].
    change 1 with (Z.succ 0) in Hr1; rewrite Z.lt_succ_r in Hr1.
    left; apply Z.le_antisymm; assumption.
  }
  assert (Hdvd_mod : forall a b, b <> 0 -> (b | a) -> a mod b = 0).
  { intros a b Hb [q ->]. apply Z.mod_mul; assumption. }

  (* Reduce to finding a positive divisor n of y^2 + 1 with n mod 4 = 3 *)
  assert (Hex_n : exists n, 0 < n /\ n mod 4 = 3 /\ (n | y ^ 2 + 1)).
  {
    destruct (Hmod4_cases (x mod 4) (Z.mod_pos_bound x 4 ltac:(reflexivity)))
      as [Hx4 | [Hx4 | [Hx4 | Hx4]]].
    - assert (Hx4_0 : (x ^ 2 + 2 * x) mod 4 = 0).
      { rewrite Z.pow_2_r, Z.add_mod, (Z.mul_mod x x 4), (Z.mul_mod 2 x 4), Hx4 by discriminate.
        reflexivity. }
      assert (H4_y : (4 | y ^ 2 + 1)).
      { apply (Z.divide_trans 4 (x ^ 2 + 2 * x) (y ^ 2 + 1)); [| exact Hdiv].
        exists ((x ^ 2 + 2 * x) / 4).
        rewrite (Z.div_mod (x ^ 2 + 2 * x) 4) at 1 by discriminate.
        rewrite Hx4_0; ring. }
      assert (Hy4_0 : (y ^ 2 + 1) mod 4 = 0) by (apply Hdvd_mod; [discriminate | exact H4_y]).
      rewrite Z.pow_2_r, Z.add_mod, (Z.mul_mod y y 4) in Hy4_0 by discriminate.
      destruct (Hmod4_cases (y mod 4) (Z.mod_pos_bound y 4 ltac:(reflexivity)))
        as [Hy4 | [Hy4 | [Hy4 | Hy4]]];
        rewrite Hy4 in Hy4_0; compute in Hy4_0; discriminate.
    - exists (x + 2); split; [| split].
      + apply (Z.lt_trans 0 x (x + 2) hx (Z.lt_add_pos_r 2 x ltac:(reflexivity))).
      + rewrite Z.add_mod, Hx4 by discriminate; reflexivity.
      + apply (Z.divide_trans (x + 2) (x ^ 2 + 2 * x) (y ^ 2 + 1));
          [exists x; rewrite Z.pow_2_r; ring | exact Hdiv].
    - assert (Hx4_0 : (x ^ 2 + 2 * x) mod 4 = 0).
      { rewrite Z.pow_2_r, Z.add_mod, (Z.mul_mod x x 4), (Z.mul_mod 2 x 4), Hx4 by discriminate.
        reflexivity. }
      assert (H4_y : (4 | y ^ 2 + 1)).
      { apply (Z.divide_trans 4 (x ^ 2 + 2 * x) (y ^ 2 + 1)); [| exact Hdiv].
        exists ((x ^ 2 + 2 * x) / 4).
        rewrite (Z.div_mod (x ^ 2 + 2 * x) 4) at 1 by discriminate.
        rewrite Hx4_0; ring. }
      assert (Hy4_0 : (y ^ 2 + 1) mod 4 = 0) by (apply Hdvd_mod; [discriminate | exact H4_y]).
      rewrite Z.pow_2_r, Z.add_mod, (Z.mul_mod y y 4) in Hy4_0 by discriminate.
      destruct (Hmod4_cases (y mod 4) (Z.mod_pos_bound y 4 ltac:(reflexivity)))
        as [Hy4 | [Hy4 | [Hy4 | Hy4]]];
        rewrite Hy4 in Hy4_0; compute in Hy4_0; discriminate.
    - exists x; split; [| split].
      + exact hx.
      + exact Hx4.
      + apply (Z.divide_trans x (x ^ 2 + 2 * x) (y ^ 2 + 1));
          [exists (x + 2); rewrite Z.pow_2_r; ring | exact Hdiv].
  }
  destruct Hex_n as [n [Hn_pos [Hn_mod4 Hn_div]]].

  (* Any positive integer = 3 (mod 4) has a prime factor = 3 (mod 4) *)
  assert (Hprime_ex : forall m, 0 <= m -> 0 < m -> m mod 4 = 3 ->
    exists p, Znumtheory.prime p /\ p mod 4 = 3 /\ (p | m)).
  {
    refine (Z_lt_induction (fun m => 0 < m -> m mod 4 = 3 ->
      exists p, Znumtheory.prime p /\ p mod 4 = 3 /\ (p | m)) _).
    intros m IH Hm_pos Hm_mod4.
    assert (Hm_gt1 : 1 < m).
    {
      assert (Hm_ge1 : 1 <= m) by (change 1 with (Z.succ 0); rewrite Z.le_succ_l; exact Hm_pos).
      rewrite Z.le_lteq in Hm_ge1.
      destruct Hm_ge1 as [Hgt | Heq]; [exact Hgt |].
      subst m; compute in Hm_mod4; discriminate.
    }
    destruct (Znumtheory.prime_dec m) as [Hpm | Hnpm].
    - exists m; split; [exact Hpm | split; [exact Hm_mod4 | exists 1; ring]].
    - destruct (Znumtheory.not_prime_divide m Hm_gt1 Hnpm) as [d [[Hd1 Hdm] [q Hq]]].
      assert (Hd_pos : 0 < d) by (apply (Z.lt_trans 0 1 d ltac:(reflexivity) Hd1)).
      assert (Hq_pos : 0 < q).
      {
        destruct q; [rewrite Z.mul_0_l in Hq; subst; discriminate | reflexivity |].
        destruct d; [discriminate | rewrite Hq in Hm_pos; discriminate | discriminate].
      }
      assert (Hqm : q < m).
      {
        rewrite Hq; rewrite <- (Z.mul_1_r q) at 1.
        apply Z.mul_lt_mono_pos_l; assumption.
      }
      rewrite Hq, Z.mul_mod in Hm_mod4 by discriminate.
      destruct (Hmod4_cases (q mod 4) (Z.mod_pos_bound q 4 ltac:(reflexivity)))
        as [Hq4 | [Hq4 | [Hq4 | Hq4]]].
      + rewrite Hq4, Z.mul_0_l in Hm_mod4; compute in Hm_mod4; discriminate.
      + destruct (Hmod4_cases (d mod 4) (Z.mod_pos_bound d 4 ltac:(reflexivity)))
          as [Hd4 | [Hd4 | [Hd4 | Hd4]]];
          try (rewrite Hq4, Hd4 in Hm_mod4; compute in Hm_mod4; discriminate).
        destruct (IH d (conj (Z.lt_le_incl 0 d Hd_pos) Hdm) Hd_pos Hd4)
          as [p [Hp1 [Hp2 [k Hk]]]].
        exists p; split; [exact Hp1 | split; [exact Hp2 | exists (q * k); rewrite Hq, Hk; ring]].
      + destruct (Hmod4_cases (d mod 4) (Z.mod_pos_bound d 4 ltac:(reflexivity)))
          as [Hd4 | [Hd4 | [Hd4 | Hd4]]];
          rewrite Hq4, Hd4 in Hm_mod4; compute in Hm_mod4; discriminate.
      + destruct (IH q (conj (Z.lt_le_incl 0 q Hq_pos) Hqm) Hq_pos Hq4)
          as [p [Hp1 [Hp2 [k Hk]]]].
        exists p; split; [exact Hp1 | split; [exact Hp2 | exists (k * d); rewrite Hq, Hk; ring]].
  }

  destruct (Hprime_ex n (Z.lt_le_incl 0 n Hn_pos) Hn_pos Hn_mod4)
    as [p [Hp_prime [Hp_mod4 Hp_n]]].
  assert (Hp_div : (p | y ^ 2 + 1)) by exact (Z.divide_trans p n (y ^ 2 + 1) Hp_n Hn_div).

  assert (Hp_gt2 : 2 < p).
  {
    assert (Hp_ge2 : 2 <= p) by (apply Znumtheory.prime_ge_2; exact Hp_prime).
    rewrite Z.le_lteq in Hp_ge2; destruct Hp_ge2 as [Hgt | Heq]; [exact Hgt |].
    subst p; compute in Hp_mod4; discriminate.
  }
  assert (Hp_pos : 0 < p) by (apply (Z.lt_trans 0 2 p ltac:(reflexivity) Hp_gt2)).
  assert (Hp_gt1 : 1 < p) by (apply (Z.lt_trans 1 2 p ltac:(reflexivity) Hp_gt2)).
  assert (Hp_nz : p <> 0) by (intro E; subst p; discriminate Hp_pos).

  assert (Hpy_ndiv : ~ (p | y)).
  {
    intros [k1 Hk1].
    destruct Hp_div as [k2 Hk2].
    assert (H1 : 1 = (k2 - k1 * y) * p).
    { transitivity ((y ^ 2 + 1) - y * y); [rewrite Z.pow_2_r; ring | rewrite Hk2; rewrite Hk1 at 1; ring]. }
    destruct (k2 - k1 * y) as [| kp | kn].
    - rewrite Z.mul_0_l in H1; discriminate.
    - destruct p as [| pp | pn]; [discriminate | | discriminate].
      destruct kp; destruct pp; simpl in H1; discriminate.
    - destruct p as [| pp | pn]; [discriminate | | discriminate].
      discriminate H1.
  }

  destruct Hp_div as [q Hq].

  (* Action of f(a) = (y * a) mod p on {1, ..., p - 1} *)
  pose (f := fun a => (y * a) mod p).

  assert (Hopp_range : forall a, 1 <= a < p -> 1 <= p - a < p).
  {
    intros a [Ha1 Ha2]. split.
    - change 1 with (Z.succ 0); rewrite Z.le_succ_l.
      rewrite (Z.add_lt_mono_r 0 (p - a) a), Z.add_0_l.
      replace (p - a + a) with p by ring; exact Ha2.
    - rewrite (Z.add_lt_mono_r (p - a) p a).
      replace (p - a + a) with p by ring.
      rewrite <- (Z.add_0_r p) at 1; apply Z.add_lt_mono_l.
      apply (Z.lt_le_trans 0 1 a ltac:(reflexivity) Ha1).
  }

  assert (Hf_range : forall a, 1 <= a < p -> 1 <= f a < p).
  {
    intros a Ha.
    destruct (Z.mod_pos_bound (y * a) p Hp_pos) as [H0 Hlt].
    assert (Hnz : f a <> 0).
    {
      intro Hfa0.
      assert (Hpya : (p | y * a)).
      { exists ((y * a) / p).
        rewrite (Z.div_mod (y * a) p) at 1 by exact Hp_nz.
        unfold f in Hfa0; rewrite Hfa0; ring. }
      destruct (Znumtheory.prime_mult p Hp_prime y a Hpya) as [Hpy | Hpa].
      - exact (Hpy_ndiv Hpy).
      - destruct Hpa as [k Hk].
        destruct k as [| kp | kn].
        + rewrite Z.mul_0_l in Hk; subst a; destruct Ha as [Ha1 _]; apply Ha1; reflexivity.
        + assert (Hk1 : 1 <= Z.pos kp) by (change 1 with (Z.succ 0); rewrite Z.le_succ_l; reflexivity).
          assert (Hpa_le : p <= a).
          { rewrite Hk; rewrite <- (Z.mul_1_l p) at 1.
            apply Z.mul_le_mono_nonneg_r; [apply Z.lt_le_incl; exact Hp_pos | exact Hk1]. }
          destruct Ha as [_ Ha2]; exact (Z.lt_irrefl p (Z.le_lt_trans p a p Hpa_le Ha2)).
        + destruct p; [discriminate | | discriminate].
          rewrite Hk in Ha; destruct Ha as [Ha1 _]; apply Ha1; reflexivity.
    }
    split; [| exact Hlt].
    rewrite Z.le_lteq in H0; destruct H0 as [Hpos | Heq].
    - change 1 with (Z.succ 0); rewrite Z.le_succ_l; exact Hpos.
    - exfalso; apply Hnz; symmetry; exact Heq.
  }

  assert (Hf_twice : forall a, 1 <= a < p -> f (f a) = p - a).
  {
    intros a Ha.
    destruct (Hopp_range a Ha) as [Hpa1 Hpa2].
    unfold f.
    rewrite Z.mul_mod_idemp_r by exact Hp_nz.
    assert (Hrew : y * (y * a) = (p - a) + (q * a - 1) * p).
    { transitivity ((p - a) + ((y * y + 1) * a - p)); [ring | rewrite <- Z.pow_2_r, Hq; ring]. }
    rewrite Hrew; rewrite Z.mod_add by exact Hp_nz.
    apply Z.mod_small; split; [| exact Hpa2].
    apply (Z.le_trans 0 1 (p - a) ltac:(intro E; discriminate E) Hpa1).
  }

  assert (Hf_opp : forall a, 1 <= a < p -> f (p - a) = p - f a).
  {
    intros a Ha.
    destruct (Hopp_range (f a) (Hf_range a Ha)) as [Hpf1 Hpf2].
    unfold f at 1.
    assert (Hrew : y * (p - a) = (p - f a) + (y - (y * a) / p - 1) * p).
    { transitivity (y * p - y * a); [ring |].
      rewrite (Z.div_mod (y * a) p Hp_nz) at 1.
      unfold f; ring. }
    rewrite Hrew; rewrite Z.mod_add by exact Hp_nz.
    apply Z.mod_small; split; [| exact Hpf2].
    apply (Z.le_trans 0 1 (p - f a) ltac:(intro E; discriminate E) Hpf1).
  }

  assert (Hodd_no_half : forall u, u <> p - u).
  {
    intros u Hu.
    assert (Hp2 : p = u * 2).
    { transitivity (u + u); [rewrite Hu at 2; ring | ring]. }
    assert (Hp_mod2_0 : p mod 2 = 0) by (rewrite Hp2, Z.mod_mul by discriminate; reflexivity).
    assert (Hp_mod2_1 : p mod 2 = 1).
    {
      rewrite (Z.div_mod p 4 ltac:(discriminate)), Hp_mod4.
      replace (4 * (p / 4) + 3) with (1 + (2 * (p / 4) + 1) * 2) by ring.
      rewrite Z.mod_add by discriminate; reflexivity.
    }
    rewrite Hp_mod2_0 in Hp_mod2_1; discriminate.
  }

  assert (Hf_distinct : forall a, 1 <= a < p ->
    a <> f a /\ a <> p - a /\ a <> p - f a /\
    f a <> p - a /\ f a <> p - f a /\ p - a <> p - f a).
  {
    intros a Ha.
    assert (H13 : a <> p - a) by apply Hodd_no_half.
    assert (H24 : f a <> p - f a) by apply Hodd_no_half.
    assert (H12 : a <> f a).
    { intro E. apply H13. rewrite <- (Hf_twice a Ha), <- E. exact E. }
    assert (H23 : f a <> p - a).
    { intro E. apply H13.
      assert (E2 : f (f a) = f (p - a)) by (f_equal; exact E).
      rewrite (Hf_twice a Ha), (Hf_opp a Ha), E in E2.
      transitivity (p - (p - a)); [ring | symmetry; exact E2]. }
    assert (H14 : a <> p - f a).
    { intro E. apply H23. rewrite E at 2; ring. }
    assert (H34 : p - a <> p - f a).
    { intro E. apply H12. transitivity (p - (p - a)); [ring | rewrite E; ring]. }
    repeat split; assumption.
  }

  assert (Hf_pow4 : forall u, 1 <= u < p -> f (f (f (f u))) = u).
  {
    intros u Hu.
    rewrite (Hf_twice u Hu), (Hf_twice (p - u) (Hopp_range u Hu)); ring.
  }

  (* Partitioning any f-closed duplicate-free list in {1, ..., p - 1} into 4-cycles *)
  pose (mem_z := fix F (z : Z) (l : list Z) : bool :=
    match l with nil => false | cons h t => orb (z =? h) (F z t) end).
  assert (Hmem_nil : forall z, mem_z z nil = false) by (intro; reflexivity).
  assert (Hmem_cons : forall z h t, mem_z z (cons h t) = orb (z =? h) (mem_z z t)) by (intros; reflexivity).

  pose (nodup_z := fix F (l : list Z) : bool :=
    match l with nil => true | cons h t => andb (negb (mem_z h t)) (F t) end).
  assert (Hnd_nil : nodup_z nil = true) by reflexivity.
  assert (Hnd_cons : forall h t, nodup_z (cons h t) = andb (negb (mem_z h t)) (nodup_z t)) by (intros; reflexivity).

  pose (remove_z := fix F (z : Z) (l : list Z) : list Z :=
    match l with nil => nil | cons h t => if z =? h then t else cons h (F z t) end).
  assert (Hrem_nil : forall z, remove_z z nil = nil) by (intro; reflexivity).
  assert (Hrem_cons : forall z h t, remove_z z (cons h t) = (if z =? h then t else cons h (remove_z z t))) by (intros; reflexivity).

  pose (len_z := fix F (l : list Z) : nat :=
    match l with nil => O | cons _ t => S (F t) end).
  assert (Hlen_nil : len_z nil = O) by reflexivity.
  assert (Hlen_cons : forall h t, len_z (cons h t) = S (len_z t)) by (intros; reflexivity).

  assert (Hmem_rem : forall l, nodup_z l = true -> forall z u,
    mem_z u (remove_z z l) = andb (negb (u =? z)) (mem_z u l)).
  {
    induction l as [| h t IH]; intros Hnd z u.
    - rewrite Hrem_nil, !Hmem_nil. destruct (u =? z); reflexivity.
    - rewrite Hnd_cons in Hnd.
      destruct (mem_z h t) eqn:Em; simpl in Hnd; [discriminate |].
      rewrite Hrem_cons.
      destruct (z =? h) eqn:Ezh.
      + apply Z.eqb_eq in Ezh; subst h.
        rewrite Hmem_cons.
        destruct (u =? z) eqn:Euz; simpl; [apply Z.eqb_eq in Euz; subst u; exact Em | reflexivity].
      + rewrite !Hmem_cons, (IH Hnd z u).
        destruct (u =? h) eqn:Euh; destruct (u =? z) eqn:Euz; simpl; try reflexivity.
        apply Z.eqb_eq in Euh; apply Z.eqb_eq in Euz; subst.
        rewrite Z.eqb_refl in Ezh; discriminate.
  }

  assert (Hnd_rem : forall l, nodup_z l = true -> forall z, nodup_z (remove_z z l) = true).
  {
    induction l as [| h t IH]; intros Hnd z.
    - rewrite Hrem_nil; exact Hnd_nil.
    - rewrite Hnd_cons in Hnd.
      destruct (mem_z h t) eqn:Em; simpl in Hnd; [discriminate |].
      rewrite Hrem_cons.
      destruct (z =? h) eqn:Ezh.
      + exact Hnd.
      + rewrite Hnd_cons, (Hmem_rem t Hnd z h), Em.
        destruct (h =? z); simpl; apply (IH Hnd z).
  }

  assert (Hlen_rem : forall l z, mem_z z l = true -> len_z l = S (len_z (remove_z z l))).
  {
    induction l as [| h t IH]; intros z Hz.
    - rewrite Hmem_nil in Hz; discriminate.
    - rewrite Hmem_cons in Hz; rewrite Hrem_cons.
      destruct (z =? h) eqn:Ezh; [rewrite Hlen_cons; reflexivity |].
      simpl in Hz; rewrite !Hlen_cons; f_equal; apply (IH z Hz).
  }

  assert (Hle_pred : forall a b : nat, (S a <= b)%nat -> (a <= b)%nat).
  { intros a b Hab; induction Hab; [apply le_S; apply le_n | apply le_S; exact IHHab]. }

  assert (Hle_Sn : forall a b : nat, (S a <= S b)%nat -> (a <= b)%nat).
  { intros a b Hab; inversion Hab; subst; [apply le_n | apply Hle_pred; assumption]. }

  assert (Hcount4 : forall m (l : list Z), (len_z l <= m)%nat ->
    nodup_z l = true ->
    (forall u, mem_z u l = true -> 1 <= u < p) ->
    (forall u, mem_z u l = true -> mem_z (f u) l = true) ->
    exists k : Z, Z.of_nat (len_z l) = 4 * k).
  {
    induction m as [| m IH]; intros l Hlen Hnd Hrng Hcls.
    - destruct l; [exists 0; reflexivity | rewrite Hlen_cons in Hlen; inversion Hlen].
    - destruct l as [| a t]; [exists 0; reflexivity |].
      assert (Ha_mem : mem_z a (cons a t) = true) by (rewrite Hmem_cons, Z.eqb_refl; reflexivity).
      assert (Ha : 1 <= a < p) by (apply Hrng; exact Ha_mem).
      set (l := cons a t) in *.
      set (a1 := a).
      set (a2 := f a).
      set (a3 := p - a).
      set (a4 := p - f a).
      assert (fa1 : f a1 = a2) by reflexivity.
      assert (fa2 : f a2 = a3) by (apply Hf_twice; exact Ha).
      assert (fa3 : f a3 = a4) by (apply Hf_opp; exact Ha).
      assert (fa4 : f a4 = a1).
      { unfold a4, a1; rewrite (Hf_opp (f a) (Hf_range a Ha)), (Hf_twice a Ha); ring. }
      destruct (Hf_distinct a Ha) as [D12 [D13 [D14 [D23 [D24 D34]]]]].
      assert (Hm1 : mem_z a1 l = true) by exact Ha_mem.
      assert (Hm2 : mem_z a2 l = true) by (rewrite <- fa1; apply Hcls; exact Hm1).
      assert (Hm3 : mem_z a3 l = true) by (rewrite <- fa2; apply Hcls; exact Hm2).
      assert (Hm4 : mem_z a4 l = true) by (rewrite <- fa3; apply Hcls; exact Hm3).
      set (l1 := remove_z a1 l).
      set (l2 := remove_z a2 l1).
      set (l3 := remove_z a3 l2).
      set (l4 := remove_z a4 l3).
      assert (Hnd1 : nodup_z l1 = true) by (apply Hnd_rem; exact Hnd).
      assert (Hnd2 : nodup_z l2 = true) by (apply Hnd_rem; exact Hnd1).
      assert (Hnd3 : nodup_z l3 = true) by (apply Hnd_rem; exact Hnd2).
      assert (Hnd4 : nodup_z l4 = true) by (apply Hnd_rem; exact Hnd3).
      assert (Hmem_l4 : forall u, mem_z u l4 =
        andb (negb (u =? a4)) (andb (negb (u =? a3)) (andb (negb (u =? a2)) (andb (negb (u =? a1)) (mem_z u l))))).
      {
        intro u.
        unfold l4 at 1; rewrite (Hmem_rem _ Hnd3).
        unfold l3 at 1; rewrite (Hmem_rem _ Hnd2).
        unfold l2 at 1; rewrite (Hmem_rem _ Hnd1).
        unfold l1 at 1; rewrite (Hmem_rem _ Hnd).
        reflexivity.
      }
      assert (Hm2_1 : mem_z a2 l1 = true).
      { unfold l1; rewrite (Hmem_rem _ Hnd), Hm2.
        destruct (a2 =? a1) eqn:E; [apply Z.eqb_eq in E; exfalso; apply D12; symmetry; exact E | reflexivity]. }
      assert (Hm3_2 : mem_z a3 l2 = true).
      { unfold l2; rewrite (Hmem_rem _ Hnd1); unfold l1; rewrite (Hmem_rem _ Hnd), Hm3.
        destruct (a3 =? a2) eqn:E; [apply Z.eqb_eq in E; exfalso; apply D23; symmetry; exact E |].
        destruct (a3 =? a1) eqn:E2; [apply Z.eqb_eq in E2; exfalso; apply D13; symmetry; exact E2 | reflexivity]. }
      assert (Hm4_3 : mem_z a4 l3 = true).
      { unfold l3; rewrite (Hmem_rem _ Hnd2); unfold l2; rewrite (Hmem_rem _ Hnd1);
          unfold l1; rewrite (Hmem_rem _ Hnd), Hm4.
        destruct (a4 =? a3) eqn:E; [apply Z.eqb_eq in E; exfalso; apply D34; symmetry; exact E |].
        destruct (a4 =? a2) eqn:E2; [apply Z.eqb_eq in E2; exfalso; apply D24; symmetry; exact E2 |].
        destruct (a4 =? a1) eqn:E3; [apply Z.eqb_eq in E3; exfalso; apply D14; symmetry; exact E3 | reflexivity]. }
      assert (Hlen4 : len_z l = S (S (S (S (len_z l4))))).
      {
        rewrite (Hlen_rem l a1 Hm1); fold l1.
        rewrite (Hlen_rem l1 a2 Hm2_1); fold l2.
        rewrite (Hlen_rem l2 a3 Hm3_2); fold l3.
        rewrite (Hlen_rem l3 a4 Hm4_3); fold l4.
        reflexivity.
      }
      assert (Hlen_le : (len_z l4 <= m)%nat).
      { rewrite Hlen4 in Hlen. apply Hle_Sn in Hlen. apply Hle_pred, Hle_pred, Hle_pred in Hlen. exact Hlen. }
      assert (Hrng4 : forall u, mem_z u l4 = true -> 1 <= u < p).
      {
        intros u Hu; apply Hrng; rewrite Hmem_l4 in Hu.
        destruct (u =? a4); destruct (u =? a3); destruct (u =? a2); destruct (u =? a1);
          simpl in Hu; try discriminate; exact Hu.
      }
      assert (Hcls4 : forall u, mem_z u l4 = true -> mem_z (f u) l4 = true).
      {
        intros u Hu.
        assert (Hu_rng : 1 <= u < p) by (apply Hrng4; exact Hu).
        assert (Hu_l : mem_z u l = true).
        { rewrite Hmem_l4 in Hu.
          destruct (u =? a4); destruct (u =? a3); destruct (u =? a2); destruct (u =? a1);
            simpl in Hu; try discriminate; exact Hu. }
        assert (Hfu_l : mem_z (f u) l = true) by (apply Hcls; exact Hu_l).
        rewrite Hmem_l4, Hfu_l.
        rewrite Hmem_l4 in Hu.
        destruct (u =? a4) eqn:Eu4; [simpl in Hu; discriminate |].
        destruct (u =? a3) eqn:Eu3; [simpl in Hu; discriminate |].
        destruct (u =? a2) eqn:Eu2; [simpl in Hu; discriminate |].
        destruct (u =? a1) eqn:Eu1; [simpl in Hu; discriminate |].
        apply Z.eqb_neq in Eu4; apply Z.eqb_neq in Eu3; apply Z.eqb_neq in Eu2; apply Z.eqb_neq in Eu1.
        destruct (f u =? a4) eqn:E4.
        { apply Z.eqb_eq in E4; exfalso; apply Eu3.
          rewrite <- (Hf_pow4 u Hu_rng), E4, fa4, fa1, fa2; reflexivity. }
        destruct (f u =? a3) eqn:E3.
        { apply Z.eqb_eq in E3; exfalso; apply Eu2.
          rewrite <- (Hf_pow4 u Hu_rng), E3, fa3, fa4, fa1; reflexivity. }
        destruct (f u =? a2) eqn:E2.
        { apply Z.eqb_eq in E2; exfalso; apply Eu1.
          rewrite <- (Hf_pow4 u Hu_rng), E2, fa2, fa3, fa4; reflexivity. }
        destruct (f u =? a1) eqn:E1.
        { apply Z.eqb_eq in E1; exfalso; apply Eu4.
          rewrite <- (Hf_pow4 u Hu_rng), E1, fa1, fa2, fa3; reflexivity. }
        reflexivity.
      }
      destruct (IH l4 Hlen_le Hnd4 Hrng4 Hcls4) as [k Hk].
      exists (k + 1).
      rewrite Hlen4, !Nat2Z.inj_succ, <- !Z.add_1_r, Hk; ring.
  }

  (* Build [1; ...; p - 1] and conclude 4 | p - 1, contradicting p mod 4 = 3 *)
  pose (seq_z := fix F (s : Z) (k : nat) : list Z :=
    match k with O => nil | S k' => cons s (F (s + 1) k') end).
  assert (Hseq_nil : forall s, seq_z s O = nil) by (intro; reflexivity).
  assert (Hseq_S : forall s k, seq_z s (S k) = cons s (seq_z (s + 1) k)) by (intros; reflexivity).
  assert (Hseq_len : forall k s, len_z (seq_z s k) = k).
  { induction k as [| k IH]; intro s; [reflexivity | rewrite Hseq_S, Hlen_cons; f_equal; apply IH]. }
  assert (Hseq_mem : forall k s u, mem_z u (seq_z s k) = true <-> s <= u < s + Z.of_nat k).
  {
    induction k as [| k IH]; intros s u.
    - rewrite Hseq_nil, Hmem_nil.
      split; [discriminate |].
      intros [H1 H2]; rewrite Z.add_0_r in H2.
      exfalso; apply (Z.lt_irrefl s (Z.le_lt_trans s u s H1 H2)).
    - rewrite Hseq_S, Hmem_cons, Nat2Z.inj_succ.
      split.
      + intro H. destruct (u =? s) eqn:E.
        * apply Z.eqb_eq in E; subst u.
          split; [apply Z.le_refl |].
          rewrite <- (Z.add_0_r s) at 1; apply Z.add_lt_mono_l.
          rewrite Z.lt_succ_r; apply Nat2Z.is_nonneg.
        * simpl in H. apply IH in H as [H1 H2].
          split.
          -- transitivity (s + 1); [| exact H1].
             rewrite <- (Z.add_0_r s) at 1; apply Z.add_le_mono_l; intro E2; discriminate E2.
          -- replace (s + Z.succ (Z.of_nat k)) with (s + 1 + Z.of_nat k) by (rewrite <- Z.add_1_r; ring).
             exact H2.
      + intros [H1 H2].
        destruct (u =? s) eqn:E; [reflexivity |].
        simpl; apply IH; apply Z.eqb_neq in E.
        split.
        * rewrite Z.le_lteq in H1; destruct H1 as [Hlt | Heq]; [| exfalso; apply E; symmetry; exact Heq].
          rewrite Z.add_1_r; rewrite Z.le_succ_l; exact Hlt.
        * replace (s + 1 + Z.of_nat k) with (s + Z.succ (Z.of_nat k)) by (rewrite <- Z.add_1_r; ring).
          exact H2.
  }
  assert (Hseq_nd : forall k s, nodup_z (seq_z s k) = true).
  {
    induction k as [| k IH]; intro s; [exact Hnd_nil |].
    rewrite Hseq_S, Hnd_cons.
    destruct (mem_z s (seq_z (s + 1) k)) eqn:Em.
    - apply Hseq_mem in Em as [H1 _].
      exfalso; apply (Z.lt_irrefl s (Z.lt_le_trans s (s + 1) s (Z.lt_add_pos_r 1 s ltac:(reflexivity)) H1)).
    - simpl; apply IH.
  }

  set (L := seq_z 1 (Z.to_nat (p - 1))).
  assert (Hp1_nonneg : 0 <= p - 1).
  {
    rewrite (Z.add_le_mono_r 0 (p - 1) 1), Z.add_0_l.
    replace (p - 1 + 1) with p by ring.
    apply Z.lt_le_incl; exact Hp_gt1.
  }
  assert (Hlen_L : Z.of_nat (len_z L) = p - 1).
  { unfold L; rewrite Hseq_len, Z2Nat.id; [reflexivity | exact Hp1_nonneg]. }
  assert (HL_count : exists k : Z, Z.of_nat (len_z L) = 4 * k).
  {
    apply (Hcount4 (len_z L) L (le_n (len_z L))).
    - unfold L; apply Hseq_nd.
    - intros u Hu; unfold L in Hu; apply Hseq_mem in Hu.
      rewrite Z2Nat.id in Hu by exact Hp1_nonneg.
      replace (1 + (p - 1)) with p in Hu by ring.
      exact Hu.
    - intros u Hu.
      assert (Hu_rng : 1 <= u < p).
      { unfold L in Hu; apply Hseq_mem in Hu.
        rewrite Z2Nat.id in Hu by exact Hp1_nonneg.
        replace (1 + (p - 1)) with p in Hu by ring.
        exact Hu. }
      unfold L; apply Hseq_mem.
      rewrite Z2Nat.id by exact Hp1_nonneg.
      replace (1 + (p - 1)) with p by ring.
      apply Hf_range; exact Hu_rng.
  }
  destruct HL_count as [k Hk].
  rewrite Hlen_L in Hk.
  assert (Hp_eq : p = 1 + k * 4) by (transitivity (1 + 4 * k); [rewrite <- Hk; ring | ring]).
  assert (Hp_mod4_1 : p mod 4 = 1) by (rewrite Hp_eq, Z.mod_add by discriminate; reflexivity).
  rewrite Hp_mod4 in Hp_mod4_1; discriminate.
Qed.
```
