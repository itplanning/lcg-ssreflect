Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.choice Ssreflect.fintype
  MathComp.div MathComp.path MathComp.bigop MathComp.prime MathComp.binomial.
Require Import LCG.seq_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma leqpp m n : m <= n -> m.-1 <= n.-1.
Proof. by case: m => //=; case: n. Qed.

Lemma leq_expnl n m : (n <= n ^ m) = ((n < 2) || (0 < m)).
Proof.
  case: n m => // n [| m] /=.
  - by rewrite ltnn orbF expn0.
  - by rewrite ltn0Sn orbT expnS -{1}(muln1 (n.+1)) leq_mul // expn_gt0.
Qed.

Lemma dvdn_lmull d1 d2 m : d1 * d2 %| m -> d1 %| m.
Proof.
  case/dvdnP => k ->.
  by rewrite mulnCA dvdn_mulr.
Qed.

Lemma dvdn_lmulr d1 d2 m : d1 * d2 %| m -> d2 %| m.
Proof.
  by rewrite mulnC; apply dvdn_lmull.
Qed.

Lemma Pascal' a b n :
  (a + b) ^ n.+1 = a ^ n.+1 + b ^ n.+1 +
                   \sum_(1 <= i < n.+1) 'C(n.+1, i) * (a ^ (n.+1 - i) * b ^ i).
Proof.
  by rewrite
    Pascal -(big_mkord xpredT (fun i => 'C(_, i) * (a ^ (_ - i) * b ^ i)))
    /index_iota subn0 subn1 -(addn1 n.+1) iota_add add0n big_cat /= !big_cons
    big_nil bin0 binn subnn !subn0 addn0 !expn0 !mul1n muln1 addnC addnCA addnA.
Qed.

Lemma expSS a n :
  a.+1 ^ n.+1 = (a ^ n.+1).+1 + \sum_(1 <= i < n.+1) 'C(n.+1, i) * a ^ i.
Proof.
  rewrite -add1n Pascal' exp1n add1n.
  by f_equal; apply eq_bigr => i _; rewrite exp1n mul1n.
Qed.

Lemma Fermat p x n : prime p -> x ^ p ^ n = x %[mod p].
Proof.
  move: p => [] // [] // p H; elim: n x.
  - by move => x; rewrite expn0 expn1.
  - move => n IH x; rewrite expnS expnM {}IH.
    elim: x {n} => // x IH.
    apply/eqP.
    rewrite expSS /= addSn (eqn_modDl 1) -IH.
    rewrite -{2}(addn0 (x ^ _)) eqn_modDl mod0n big_nat.
    apply big_ind => //.
    + apply dvdn_add.
    + by move => i H0; apply dvdn_mulr, prime_dvd_bin.
Qed.

Lemma LemmaP p e :
  prime p -> 2 < p ^ logn p e -> logn p (e.+1 ^ p).-1 = (logn p e).+1.
Proof.
  move: p e => [] // [] // p [| []]; rewrite ?logn0 ?logn1 ?expn0 // => e H H0.
  rewrite expSS addSn /= /index_iota subn1 /= !expnS /=
          big_cons bin1 expn1 (mulnC p.+2) (iota_addl 2 0) big_map.
  have/(eq_bigr _) -> i: true ->
      'C(p.+2, i.+2) * e.+2 ^ i.+2 = e.+2 * (e.+2 * ('C(p.+2, i.+2) * e.+2 ^ i))
    by rewrite !expnS 2!(mulnCA e.+2).
  rewrite -!big_distrr /= addnCA -!mulnDr lognM //= -[X in _ = X]addn1; f_equal.
  move: H0; rewrite lognE H /=; case: ifP => //.
  rewrite dvdn_eq expnS; move/eqP/esym => H0 H1.
  rewrite {1}H0 mulnAC -mulSn lognM // (pfactorK 1 H) addn1.
  f_equal; rewrite lognE H /= (dvdn_addl 1) //.
  case: p H H0 H1 => [_ _ | p H H0 _].
  - by rewrite big_nil expn0 muln1 lognE divn_gt0 //=; case: ifP.
  - apply dvdn_mull, dvdn_add.
    + by rewrite expnS {1}H0; apply dvdn_mulr, dvdn_mull.
    + rewrite (big_nat _ _ 0 p.+1).
      by apply big_rec => // n m H1 H2;
        apply dvdn_add => //; apply dvdn_mulr, prime_dvd_bin.
Qed.

Lemma LemmaR p a e l :
  prime p -> 1 < a < p ^ e ->
  (forall l', p ^ e %| \sum_(k < l') a ^ k <-> l %| l') ->
  (l == p ^ e) = ((if p == 2 then 4 else p) %| a.-1).
Proof.
  move: p a e => [] // [] // p [] // [] // a [] // e H;
    case/andP; rewrite !ltnS => _ H0 H1.
  have H2 m: 0 < (a.+2 ^ p.+2 ^ m).-1.
    apply (@leqpp 2), (@leq_trans a.+2) => //.
    by rewrite -{1}(expn1 a.+2) leq_exp2l // expn_gt0.
  have H3 m: 0 < \sum_(k < p.+2 ^ m) a.+2 ^ k by rewrite
    -(andTb (_ < _)) (erefl : true = (0 < a.+2.-1)) -muln_gt0 -predn_exp.
  apply/esym/idP; case: ifP; move/eqP.
  - move => ?; subst l.
    suff {H0 H2 H3}: p.+2 %| a.+1.
      case: ifP => //; case/eqP => ?; subst p => /= {H}.
      rewrite /dvdn -![a.+1 %% _](modnDmr 1) -(@modn_dvdm 4 a 2) // modnDmr.
      suff: a %% 4 <> 1
        by move: (a %% 4) (@ltn_pmod a 4 erefl); do 4 case => //.
      case: e H0 H1; first by rewrite expn1.
      move => e _ H H0.
      have/(contra (proj1 (H _)))/negP: ~~ (2 ^ e.+2 %| 2 ^ e.+1)
        by rewrite expnS -{2}(mul1n (_ ^ _)) dvdn_pmul2r // expn_gt0.
      apply.
      rewrite pfactor_dvdn // -ltnS -[X in _ < X]add1n.
      have {1}->: 1 = logn 2 a.+2.-1 by rewrite
        (divn_eq a 4) H0 -addnS /= {2}(erefl : 4 = 2 * 2) mulnA -mulSnr
        lognM // lognE /= -{1}(addn1 (_ * _)) dvdn_addr //= dvdn_mull.
      rewrite -lognM // -predn_exp.
      elim: e {H H2 H3}.
      + rewrite -pfactor_dvdn // expn1 (divn_eq a 4) H0 -!addnS
                sqrnD addnAC (erefl : 3 ^ 2 = 9) addnS /=.
        do 2 apply dvdn_add => //.
        * by rewrite expnMn (erefl : 4 ^ 2 = 2 * 8) mulnA dvdn_mull.
        * by rewrite (@dvdn_pmul2l 2 4) // mulnAC dvdn_mull.
      + move => e IH.
        rewrite expnS mulnC expnM -(@prednK (_ ^ _ ^ _)) ?expn_gt0 // LemmaP //.
        move: (logn _ _) IH => [| []] // n _; rewrite !expnS mulnA.
        by apply (@leq_mul 3 1) => //; rewrite expn_gt0.
    apply/negP; move/negP => H0.
    move: (proj2 (H1 (p.+2 ^ e.+1)) (dvdnn _)).
    rewrite -(@Gauss_dvdr (p.+2 ^ e.+1) a.+2.-1).
    + rewrite -predn_exp {1}expnS; move/dvdn_lmull.
      move => H2; move: H2 H0.
      by rewrite /dvdn -{1}(mod0n p.+2) -(eqn_modDl 1) !add1n
                 prednK ?expn_gt0 // Fermat // (eqn_modDl 1) mod0n => ->.
    + by rewrite coprime_pexpl //= prime_coprime.
  - move => {H0 H2} /= H2 H0; apply: H2.
    have {H0} H0 m: logn p.+2 (\sum_(k < p.+2 ^ m) a.+2 ^ k) = m.
      move => {H1}.
      apply (@addnI (logn p.+2 a.+2.-1)).
      rewrite -lognM // -predn_exp /=.
      elim: m => // m IH.
      rewrite expnS mulnC expnM -(@prednK (_ ^ _ ^ _))
              ?expn_gt0 // LemmaP // {}IH //.
      move: p a H H0 {H3} => [[] | p] //= a H H0.
      + by rewrite
          2!lognE /= dvdn_divRL ?H2 (@dvdn_lmulr 2 2) // divn_gt0 //= H0
          !addSn !expnS (@ltn_pmul2l 2 1) // (@leq_pmul2l 2 1) // expn_gt0.
      + rewrite lognE H H0 /= addSn expnS.
        by apply (@leq_mul 3 1) => //; rewrite expn_gt0.
    move: (proj1 (H1 (p.+2 ^ e.+1))).
    rewrite pfactor_dvdn // (H0 e.+1) leqnn => H2; move: {H2} (H2 erefl).
    case/(dvdn_pfactor _ _ H) => y H2 ?; subst l; f_equal; apply/eqP.
    by rewrite eqn_leq H2 /= -(H0 y) -pfactor_dvdn //; apply H1, dvdnn.
Qed.
