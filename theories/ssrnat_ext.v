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

Lemma ndvdn_logn p m : ~~ (p %| m) -> logn p m = 0.
Proof.
  by rewrite lognE; case: ifP => //; case/and3P => _ _ ->.
Qed.

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

Lemma poly1_eq1 a n :
  iter n (fun x => (x * a).+1) 0 = \sum_(n' < n) a ^ n'.
Proof.
  rewrite -(big_mkord xpredT (expn a)).
  elim: n => /=.
  - by rewrite big_nil.
  - move => n ->.
    rewrite big_distrl /= index_iota_0s big_cons big_map expn0 add1n.
    by apply f_equal, eq_bigr => i _; rewrite expnS mulnC.
Qed.

Lemma poly1_eq2 a n :
  iter n (fun x => (x * a).+1) 0 * a.-1 = (a ^ n).-1.
Proof.
  case: a => //= [| a].
  - by rewrite muln0; case: n => //= n; rewrite exp0n.
  - rewrite (pred_Sn (_ * _)); f_equal.
    elim: n => //= n.
    move: (iter _ _ _) => x.
    rewrite expnS => <-.
    by rewrite mulnS -addnS mulnDl -addSn -mulnS mulnC.
Qed.

Lemma poly1_eq3 a n m :
  iter n (fun x => (x * a).+1) m = m * (a ^ n) + iter n (fun x => (x * a).+1) 0.
Proof.
  elim: n m => //= [| n IH] m.
  - by rewrite expn0 muln1 addn0.
  - by rewrite addnS expnS mulnCA (mulnC a) -mulnDl -IH.
Qed.

Lemma poly1_leq a n m :
  n <= m ->
  iter n (fun x => (x * a).+1) 0 <= iter m (fun x => (x * a).+1) 0.
Proof.
  elim: n m => //=.
  move => n IH [] //= m; rewrite !ltnS.
  by rewrite leq_mul2r; move/IH => ->; rewrite orbT.
Qed.

Lemma poly1_sub a n m :
  m <= n ->
  iter n (fun x => (x * a).+1) 0 - iter m (fun x => (x * a).+1) 0 =
  a ^ m * iter (n - m) (fun x => (x * a).+1) 0.
Proof.
  elim: m n => /=.
  - by move => n _; rewrite !subn0 expn0 mul1n.
  - move => n IH [] //= m.
    by rewrite ltnS !subSS -mulnBl mulnC expnS -mulnA => H; f_equal; apply IH.
Qed.

Lemma poly1_add a n n' m :
  iter (n + n') (fun x => (x * a).+1) 0 =
  iter n (fun x => (x * a).+1) (iter n' (fun x => (x * a).+1) 0 %% m) %[mod m].
Proof.
  apply/eqP; elim: n.
  - by rewrite add0n /= modn_mod.
  - move => n IH.
    rewrite addSn /= (eqn_modDl 1) -!(modnMml (iter _ _ _)).
    by move/eqP: IH => ->.
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

Lemma Fermat' p x : prime p -> (x ^ p) = x %[mod p].
Proof.
  move: p => [] // [] // p H; elim: x => [| x IH].
  - by rewrite exp0n.
  - apply/eqP.
    rewrite expSS /= addSn (eqn_modDl 1) -IH
            -{2}(addn0 (x ^ _)) eqn_modDl mod0n -/(dvdn _ _) big_nat.
    apply big_ind => //.
    + apply dvdn_add.
    + by move => i H0; apply dvdn_mulr, prime_dvd_bin.
Qed.

Lemma Fermat'' p x n : prime p -> x ^ p ^ n = x %[mod p].
Proof.
  move: p => [] // [] // p H; elim: n x.
  - by move => x; rewrite expn0 expn1.
  - by move => n IH x; rewrite expnS expnM -(Fermat' x H).
Qed.

Lemma Fermat p x : prime p -> coprime p x -> p %| (x ^ p.-1).-1.
Proof.
  move: p => [] // [] //= p H H0.
  rewrite -(Gauss_dvdr _ H0) -subn1 mulnBr muln1 -expnS -eqn_mod_dvd.
  - by apply/eqP/Fermat'.
  - by rewrite leq_expnl orbT.
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
  f_equal; apply ndvdn_logn.
  rewrite (dvdn_addl 1) //.
  case: p H H0 H1 => [_ _ | p H H0 _].
  - by rewrite big_nil expn0 muln1 lognE divn_gt0 //=; case: ifP.
  - apply dvdn_mull, dvdn_add.
    + by rewrite expnS {1}H0; apply dvdn_mulr, dvdn_mull.
    + rewrite (big_nat _ _ 0 p.+1).
      by apply big_rec => // n m H1 H2;
        apply dvdn_add => //; apply dvdn_mulr, prime_dvd_bin.
Qed.

Lemma LemmaR p a e l :
  let zero i := p ^ e %| iter i (fun x => (x * a).+1) 0 in
  prime p -> 1 < a < p ^ e ->
  0 < l -> (forall l', 0 < l' < l -> ~~ zero l') -> zero l ->
  (l == p ^ e) = ((if p == 2 then 4 else p) %| a.-1).
Proof.
  move: p a e l => [] // [] // p [] // [] // a [] // e [] // l zero H;
    case/andP => _ H0 _ H1 H2.
  have H3 i: zero i -> l.+1 %| i.
    rewrite {1}(divn_eq i l.+1).
    elim: (i %/ l.+1).
    - rewrite mul0n add0n /dvdn.
      case: (i %% l.+1) (@ltn_pmod i l.+1 erefl) (H1 (i %% l.+1)) =>
        //= i' H3 H4 H5.
      by case: (negP (H4 H3) H5).
    - move => i' IH H3; apply: IH.
      subst zero; move/eqP: {H1} H2 H3.
      by rewrite mulSn -addnA addnC /dvdn poly1_add => ->.
  have H4 m: 0 < (a.+2 ^ p.+2 ^ m).-1.
    apply (@leqpp 2), (@leq_trans a.+2) => //.
    by rewrite -{1}(expn1 a.+2) leq_exp2l // expn_gt0.
  have H5 m: 0 < iter (p.+2 ^ m) (fun x => (x * a.+2).+1) 0
    by rewrite -(@ltn_pmul2r a.+1) // mul0n poly1_eq2.
  apply/esym/idP; case: ifP; move/eqP.
  - move => {H3} H3; move: H3 H1 H2 => -> {l} H1 H2.
    have {H0 H1 H4 H5} H0: p = 0 -> a %% 4 <> 1.
      move => ? {H H2}; move: H1; subst zero p => H H1.
      case: e H H0; first by rewrite expn1 //.
      move => e H _.
      have/H/negP: 0 < 2 ^ e.+1 < 2 ^ e.+2 by rewrite expn_gt0 //= ltn_exp2l.
      apply.
      rewrite pfactor_dvdn // -ltnS -[X in _ < X]addn1.
      have {3}->: 1 = logn 2 a.+1 by rewrite
        (divn_eq a 4) H1 -addnS /= {2}(erefl : 4 = 2 * 2) mulnA -mulSnr
        lognM // lognE /= -{1}(addn1 (_ * _)) dvdn_addr //= dvdn_mull.
      rewrite -lognM // poly1_eq2 -pfactor_dvdn //.
      elim: e {H}.
      + rewrite expn1 (divn_eq a 4) H1 -!addnS
                sqrnD addnAC (erefl : 3 ^ 2 = 9) addnS /=.
        do 2 apply dvdn_add => //.
        * by rewrite expnMn (erefl : 4 ^ 2 = 2 * 8) mulnA dvdn_mull.
        * by rewrite (@dvdn_pmul2l 2 4) // mulnAC dvdn_mull.
      + move => e IH.
        rewrite (expnS 2 e.+1) mulnC expnM -(@prednK (_ ^ _ ^ _)) ?expn_gt0 //
                -(addn1 _.-1) sqrnD muln1 addn1 addSn /= expnS.
        apply dvdn_add; rewrite dvdn_mul //.
        by move: IH; rewrite expnS; apply dvdn_lmull.
    suff {H0}: p.+2 %| a.+1.
      move => {zero H2}.
      case: ifP => //; move/eqP.
      case => ?; subst.
      rewrite (divn_eq a 4) -!addnS /dvdn
              {2}(erefl : 4 = 2 * 2) {1}mulnA !addnS /= -!addnS !modnMDl.
      move: (a %% 4) (@ltn_pmod a 4 erefl) (H0 erefl).
      do 4 case => //.
    subst zero.
    apply/negP; move/negP => H0; move: H2.
    rewrite -(@Gauss_dvdl (p.+2 ^ e.+1) _ a.+1) ?poly1_eq2.
    + move => H1; move/negP: H0; apply; move: H1.
      rewrite {1}expnS; move/dvdn_lmull.
      by rewrite /dvdn -(mod0n p.+2) -(eqn_modDl 1) !add1n
                 prednK ?expn_gt0 // Fermat'' // (eqn_modDl 1) mod0n.
    + by rewrite coprime_pexpl // prime_coprime.
  - move => /= H7 H6; apply: H7.
    have {H0 H1 H4 H6} H0 m:
        logn p.+2 (iter (p.+2 ^ m) (fun x => (x * a.+2).+1) 0) = m.
      apply (@addIn (logn p.+2 a.+1)).
      rewrite -lognM // poly1_eq2.
      elim: m {H0 H1 H2 H3 H4} => // g IH.
      rewrite expnS mulnC expnM -(@prednK (_ ^ _ ^ _))
              ?expn_gt0 // LemmaP // {}IH //.
      subst zero; move: p a H H5 H6 => [[] // | p] /= a H H0 H1.
      + by rewrite
          2!lognE /= dvdn_divRL ?H0 (@dvdn_lmulr 2 2) // divn_gt0 //= H1
          !addnS !expnS (@ltn_pmul2l 2 1) // (@leq_pmul2l 2 1) // expn_gt0.
      + rewrite lognE H /= H1 addnS expnS.
        by apply (@leq_mul 3 1) => //; rewrite expn_gt0.
    subst zero; move: H0 H2 H3 H5 => H0 H1 H2 H3.
    move: (H2 (p.+2 ^ e.+1)).
    rewrite pfactor_dvdn // (H0 e.+1) leqnn => H4; move: {H4} (H4 erefl).
    case/(dvdn_pfactor _ _ H) => y H4 H5.
    rewrite pfactor_dvdn // H5 (H0 y) in H1.
    by rewrite H5; f_equal; apply/eqP; rewrite eqn_leq H4.
Qed.
