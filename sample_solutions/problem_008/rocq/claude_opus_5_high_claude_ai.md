# Claude Opus 5 High (Claude AI)

Model: `Claude Opus 5 High` (via Claude AI)\
Date: `20 November 2026`\
Line count: `133`\
Turn count: `1`

## Solution

```rocq
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Theorem no_x_sq_plus_two_x_dvd_y_sq_plus_one (x y : Z) (hx : 0 < x)
    (hy : 0 < y) : ~ (x ^ 2 + 2 * x | y ^ 2 + 1).
Proof.
  (* [lia] is written out as [Stdlib.micromega.Lia.lia] so that the file
     compiles with the preamble above unchanged: ZArith loads the Lia module
     transitively but does not import it.  Adding
     [From Stdlib Require Import Lia.] lets you write plain [lia] instead. *)
  (* Key fact, by Fermat-style descent: an integer congruent to 3 modulo 4
     never divides a number of the form z^2 + 1. *)
  assert (key : forall m, 0 <= m -> (exists j, m = 4 * j + 3) ->
                          forall z, ~ (m | z ^ 2 + 1)).
  { apply (Zlt_0_ind
             (fun m => (exists j, m = 4 * j + 3) ->
                       forall z, ~ (m | z ^ 2 + 1))).
    intros m IH Hm0 Hm4 z Hdvd.
    destruct Hm4 as [j Hj].
    assert (Hm3 : 3 <= m) by Stdlib.micromega.Lia.lia.
    assert (Hdm : z = m * (z / m) + z mod m)
      by (apply Z.div_mod; Stdlib.micromega.Lia.lia).
    assert (Hsb : 0 <= z mod m < m)
      by (apply Z.mod_pos_bound; Stdlib.micromega.Lia.lia).
    destruct Hdvd as [c Hc].
    (* the residue of z modulo m is again a square root of -1 *)
    assert (Hs : (m | (z mod m) ^ 2 + 1)).
    { exists (c - 2 * (z / m) * z + m * (z / m) ^ 2).
      replace (z mod m) with (z - m * (z / m)) by Stdlib.micromega.Lia.lia.
      replace ((z - m * (z / m)) ^ 2 + 1)
        with (z ^ 2 + 1 - 2 * m * (z / m) * z + m ^ 2 * (z / m) ^ 2) by ring.
      rewrite Hc. ring. }
    (* m is odd, so exactly one of the residues r, m - r is even;
       pick the even one, and write it as 2 * a *)
    assert (Hex : exists a, 0 <= 2 * a < m /\ (m | (2 * a) ^ 2 + 1)).
    { assert (Hd2 : z mod m = 2 * ((z mod m) / 2) + (z mod m) mod 2)
        by (apply Z.div_mod; Stdlib.micromega.Lia.lia).
      assert (Hb2 : 0 <= (z mod m) mod 2 < 2)
        by (apply Z.mod_pos_bound; Stdlib.micromega.Lia.lia).
      assert (Hp : (z mod m) mod 2 = 0 \/ (z mod m) mod 2 = 1)
        by Stdlib.micromega.Lia.lia.
      destruct Hp as [Hev | Hod].
      - exists ((z mod m) / 2).
        assert (Heq : 2 * ((z mod m) / 2) = z mod m)
          by Stdlib.micromega.Lia.lia.
        rewrite Heq. split; [ Stdlib.micromega.Lia.lia | exact Hs ].
      - destruct Hs as [d Hd].
        exists (2 * j + 1 - (z mod m) / 2).
        assert (Heq : 2 * (2 * j + 1 - (z mod m) / 2) = m - z mod m)
          by Stdlib.micromega.Lia.lia.
        rewrite Heq. split; [ Stdlib.micromega.Lia.lia | ].
        exists (m - 2 * (z mod m) + d).
        replace ((m - z mod m) ^ 2 + 1)
          with ((z mod m) ^ 2 + 1 + m * (m - 2 * (z mod m))) by ring.
        rewrite Hd. ring. }
    destruct Hex as [a [Hab [k Hk]]].
    (* the cofactor k satisfies 0 < k < m *)
    assert (Hnn : 0 <= a * a) by (apply Z.square_nonneg).
    assert (Hub : (2 * a) * (2 * a) <= (m - 1) * (m - 1))
      by (apply Z.mul_le_mono_nonneg; Stdlib.micromega.Lia.lia).
    assert (Hk0 : 0 < k).
    { assert (Hd0 : 0 < k \/ k <= 0) by Stdlib.micromega.Lia.lia.
      destruct Hd0 as [HH | HH]; [ exact HH | ].
      assert (Hle : k * m <= 0 * m)
        by (apply Z.mul_le_mono_nonneg_r; Stdlib.micromega.Lia.lia).
      Stdlib.micromega.Lia.lia. }
    assert (Hkm : k * m < m * m) by Stdlib.micromega.Lia.lia.
    assert (Hk1 : k < m).
    { assert (Hd1 : k < m \/ m <= k) by Stdlib.micromega.Lia.lia.
      destruct Hd1 as [HH | HH]; [ exact HH | ].
      assert (Hle : m * m <= k * m)
        by (apply Z.mul_le_mono_nonneg_r; Stdlib.micromega.Lia.lia).
      Stdlib.micromega.Lia.lia. }
    (* and k is again congruent to 3 modulo 4 *)
    assert (Hkd : exists q r, k = 4 * q + r /\ 0 <= r < 4).
    { exists (k / 4), (k mod 4).
      split; [ apply Z.div_mod | apply Z.mod_pos_bound ];
        Stdlib.micromega.Lia.lia. }
    destruct Hkd as [q [r [Hkqr Hrb]]].
    assert (Hprod : 4 * (4 * q * j + 3 * q + r * j) + 3 * r = 4 * (a * a) + 1).
    { replace (4 * (4 * q * j + 3 * q + r * j) + 3 * r)
        with ((4 * q + r) * (4 * j + 3)) by ring.
      rewrite <- Hkqr, <- Hj, <- Hk. ring. }
    assert (Hk3 : exists jj, k = 4 * jj + 3).
    { exists q.
      assert (Hrc : r = 0 \/ r = 1 \/ r = 2 \/ r = 3)
        by Stdlib.micromega.Lia.lia.
      destruct Hrc as [E | [E | [E | E]]]; subst r;
        Stdlib.micromega.Lia.lia. }
    assert (Hbk : 0 <= k < m) by Stdlib.micromega.Lia.lia.
    apply (IH k Hbk Hk3 (2 * a)).
    exists m. rewrite Hk. ring. }
  (* Now the theorem itself. *)
  intros Hdvd.
  destruct Hdvd as [c Hc].
  (* x cannot be even, else 4 would divide y^2 + 1 *)
  assert (Heven : forall b, x = 2 * b -> False).
  { intros b Hb.
    assert (H4 : y ^ 2 + 1 = c * (b * b + b) * 4) by (rewrite Hc, Hb; ring).
    assert (Hyd : exists d e, y = 2 * d + e /\ 0 <= e < 2).
    { exists (y / 2), (y mod 2).
      split; [ apply Z.div_mod | apply Z.mod_pos_bound ];
        Stdlib.micromega.Lia.lia. }
    destruct Hyd as [d [e [Hye Heb]]].
    assert (Hec : e = 0 \/ e = 1) by Stdlib.micromega.Lia.lia.
    destruct Hec as [E | E]; subst e.
    - assert (Hexp : y ^ 2 + 1 = 4 * (d * d) + 1) by (rewrite Hye; ring).
      Stdlib.micromega.Lia.lia.
    - assert (Hexp : y ^ 2 + 1 = 4 * (d * d) + 4 * d + 2)
        by (rewrite Hye; ring).
      Stdlib.micromega.Lia.lia. }
  (* so x is odd; according to x mod 4, either x or x + 2 is 3 modulo 4,
     and both divide x^2 + 2x = x * (x + 2), hence divide y^2 + 1 *)
  assert (Hxd : exists q r, x = 4 * q + r /\ 0 <= r < 4).
  { exists (x / 4), (x mod 4).
    split; [ apply Z.div_mod | apply Z.mod_pos_bound ];
      Stdlib.micromega.Lia.lia. }
  destruct Hxd as [q [r [Hxqr Hrb]]].
  assert (Hrc : r = 0 \/ r = 1 \/ r = 2 \/ r = 3) by Stdlib.micromega.Lia.lia.
  destruct Hrc as [E | [E | [E | E]]]; subst r.
  - apply (Heven (2 * q)). Stdlib.micromega.Lia.lia.
  - assert (H0 : 0 <= x + 2) by Stdlib.micromega.Lia.lia.
    assert (H3 : exists j, x + 2 = 4 * j + 3)
      by (exists q; Stdlib.micromega.Lia.lia).
    apply (key (x + 2) H0 H3 y).
    exists (c * x). rewrite Hc. ring.
  - apply (Heven (2 * q + 1)). Stdlib.micromega.Lia.lia.
  - assert (H0 : 0 <= x) by Stdlib.micromega.Lia.lia.
    assert (H3 : exists j, x = 4 * j + 3)
      by (exists q; Stdlib.micromega.Lia.lia).
    apply (key x H0 H3 y).
    exists (c * (x + 2)). rewrite Hc. ring.
Qed.
```
