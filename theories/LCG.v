Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.choice Ssreflect.fintype
  MathComp.div MathComp.path MathComp.bigop MathComp.prime MathComp.binomial
  MathComp.ssralg MathComp.zmodp.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma leqpp m n : m <= n -> m.-1 <= n.-1.
Proof. by case: m => //=; case: n. Qed.

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

Lemma sum_expn_gt0 m a : (0 < \sum_(k < m) a ^ k) = (0 < m).
Proof.
  case: m => [| m].
  - by rewrite big_ord0.
  - by rewrite (big_ord_recl m) /= expn0 add1n.
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
  prime p -> (p == 2) < logn p e -> logn p (e.+1 ^ p).-1 = (logn p e).+1.
Proof.
  move: p e => [] // [] // p [| []]; rewrite ?logn0 ?logn1 // => e H H0.
  rewrite expSS addSn /= /index_iota subn1 /= !expnS /=
          big_cons bin1 expn1 (mulnC p.+2) (iota_addl 2 0) big_map.
  have/(eq_bigr _) -> i: true ->
      'C(p.+2, i.+2) * e.+2 ^ i.+2 = e.+2 * (e.+2 * ('C(p.+2, i.+2) * e.+2 ^ i))
    by rewrite !expnS 2!(mulnCA e.+2).
  rewrite -!big_distrr /= addnCA -!mulnDr lognM //= -[X in _ = X]addn1; f_equal.
  move: H0; rewrite lognE H /=; case: ifP => //.
  rewrite dvdn_eq; move/eqP/esym => H0 H1.
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

Lemma LemmaP' p e n :
  prime p -> (p == 2) < logn p e -> logn p (e.+1 ^ p ^ n).-1 = logn p e + n.
Proof.
  move => H H0.
  elim: n => // n IH.
  rewrite expnSr expnM -(@prednK (e.+1 ^ _)) ?expn_gt0 // LemmaP // {}IH //.
  by apply ltn_addr.
Qed.

(*
Lemma LemmaP'' p e n :
  0 < e -> prime p -> p %| e.-1 ->
  logn p (\sum_(k < p ^ n) e ^ k) =
  (if (1 < e) && (0 < n) && (p == 2) then n.-1 + logn 2 e.+1 else n).
Proof.
  move: p e => [| []] // p [| [| e]] //= _ H H0.
  - by rewrite -(big_mkord xpredT) (eq_bigr _ (fun n _ => exp1n n))
               sum_nat_const_nat subn0 muln1 pfactorK.
  - apply (@addnI (logn p.+2 e.+2.-1)).
    rewrite -lognM ?sum_expn_gt0 ?expn_gt0 // -predn_exp.
    case: p H H0 => [_ H | p H H0].
    + case: n => //= n.
      rewrite expnS expnM (sqrnD 1) add1n addSn mul1n
              expnS expn1 -mulnDl addn2 LemmaP' //= lognM //.
      * by rewrite (addnC n) (addnC (logn _ _)) addnA.
      * by rewrite lognE addnC lognE (dvdn_addr _ (dvdnn 2)) H addnS.
    + by rewrite andbF LemmaP' //= lognE H H0.
Qed.
*)

Lemma LemmaQ m a l :
  (forall l', all
    (fun t => (t.1 ^ t.2 %| \sum_(k < l') a ^ k) == (t.1 ^ t.2 %| l'))
    (prime_decomp m)) ->
  (m %| \sum_(k < l) a ^ k) = (m %| l).
Proof.
  case: m => [_ | m] /=.
  - by rewrite !dvd0n eqn0Ngt sum_expn_gt0; case: l.
  - rewrite {2 3}(@prod_prime_decomp m.+1 erefl) prime_decompE big_map /= => H.
    have {H} H p l': prime p -> p %| m.+1 ->
      (p ^ logn p m.+1 %| \sum_(k < l') a ^ k) = (p ^ logn p m.+1 %| l').
      by move => H0 H1; apply (fun H2 => eqP (allP (H l') (p, logn p m.+1) H2));
         apply (map_f (fun p => (p, logn p m.+1))); rewrite mem_primes H0.
    have /=: forall p, p \in primes m.+1 -> prime p && (p %| m.+1)
      by move => p; rewrite mem_primes /=.
    elim: (primes m.+1) (primes_uniq m.+1) => /=.
    + by rewrite big_nil !dvd1n.
    + move => p ps IH; case/andP => H0 H1 H2.
      case/andP: (H2 p (mem_head _ _)) => H3 H4.
      have H5: coprime (p ^ logn p m.+1) (\prod_(j <- ps) j ^ logn j m.+1).
        rewrite big_seq; apply big_ind => /=.
        * apply coprimen1.
        * by move => x y; rewrite coprime_mulr => ->.
        * move => i H5.
          apply coprime_expl, coprime_expr.
          move: (H2 i); rewrite inE H5 orbT => H2';
            case/andP: {H2'} (H2' erefl) => H6 H7.
          rewrite prime_coprime // dvdn_prime2 //.
          by apply/eqP => ?; subst i; rewrite H5 in H0.
      rewrite big_cons !Gauss_dvd // H // IH // => p' H8; apply H2.
      by rewrite inE H8 orbT.
Qed.

(*
Lemma LemmaR' p a e l :
  prime p -> 0 < a -> 0 < e ->
  (forall l', p ^ e %| \sum_(k < l') a ^ k <-> l %| l') ->
  (l == p ^ e) = ((if (1 < e) && (p == 2) then 4 else p) %| a.-1).
Proof.
  move: p a e => [| []] // p [] // a [] //= e H _ _ H0.
  apply/esym/idP; case: ifP; move/eqP.
  - move => ?; subst l; rewrite ltnS.
    have: p.+2 %| a.
      apply/negP; move/negP => H2.
      move: (proj2 (H0 (p.+2 ^ e.+1)) (dvdnn _)).
      rewrite -(@Gauss_dvdr (p.+2 ^ e.+1) a.+1.-1).
      + rewrite -predn_exp {1}expnS; move/dvdn_lmull.
        move => H3; move: H3 H2.
        by rewrite /dvdn -{1}(mod0n p.+2) -(eqn_modDl 1) !add1n
                   prednK ?expn_gt0 // Fermat // (eqn_modDl 1) mod0n => ->.
      + by rewrite coprime_pexpl //= prime_coprime.
    move: a e p H H0 => [| []] // a [] // e [] //= _ H.
    suff: ~ (4 %| a).
      rewrite /dvdn -![a.+2 %% _](modnDmr 2) -(@modn_dvdm 4 a 2) // modnDmr.
      by move: (a %% 4) (@ltn_pmod a 4 erefl); do 4 case => //.
    have/(contra (proj1 (H _)))/negP: ~~ (2 ^ e.+2 %| 2 ^ e.+1)
      by rewrite expnS -{2}(mul1n (_ ^ _)) dvdn_pmul2r // expn_gt0.
    move => {H} H1 H; apply: H1.
    rewrite pfactor_dvdn ?sum_expn_gt0 ?expn_gt0 // LemmaP'' //=.
    + by rewrite addnC (ltn_add2r e 1) -pfactor_dvdn.
    + by rewrite (dvdn_addl 2) //; apply (@dvdn_lmulr 2 2).
  - rewrite ltnS; move => /= H3 H2; apply: H3.
    admit.
Abort.
*)

Lemma LemmaR p a e l :
  prime p -> 1 < a -> 2 < p ^ e ->
  (forall l', (p ^ e %| \sum_(k < l') a ^ k) = (l %| l')) ->
  (l == p ^ e) = ((if p == 2 then 4 else p) %| a.-1).
Proof.
  move: p a e => [| []] // p [| []] // a [] // e H _ H0 H1.
  apply/esym/idP; case: ifP; move/eqP.
  - move => ?; subst l.
    have: p.+2 %| a.+1.
      apply/negP; move/negP => {H0} H0.
      move: (H1 (p.+2 ^ e.+1)).
      rewrite dvdnn -(@Gauss_dvdr (p.+2 ^ e.+1) a.+2.-1).
      + move => H2; apply/(negP H0); move: H2.
        rewrite -predn_exp {1}expnS; move/dvdn_lmull.
        by rewrite /dvdn -{1}(mod0n p.+2) -(eqn_modDl 1) !add1n
                   prednK ?expn_gt0 // Fermat // (eqn_modDl 1) mod0n.
      + by rewrite coprime_pexpl //= prime_coprime.
    case: ifP => //; case/eqP => ?; subst p => /= {H}.
    case: a e H0 H1 => // a []; rewrite ?expn1 // => e _ H.
    suff: ~~ (4 %| a).
      rewrite /dvdn -![a.+2 %% _](modnDmr 2) -(@modn_dvdm 4 a 2) // modnDmr.
      by move: (a %% 4) (@ltn_pmod a 4 erefl); do 4 case => //.
    have: ~~ (2 ^ e.+2 %| 2 ^ e.+1)
      by rewrite expnS -{2}(mul1n (_ ^ _)) dvdn_pmul2r // expn_gt0.
    rewrite -H; apply contra => {H} H.
    by rewrite
      pfactor_dvdn -1?(ltn_add2l (logn 2 a.+3.-1) e.+1) -?lognM ?sum_expn_gt0
      ?expn_gt0 // -predn_exp expnS expnM -(@prednK (a.+3 ^ _)) ?expn_gt0 //
      LemmaP' // (sqrnD 1) add1n addSn /= mul1n expnS expn1 -mulnDl lognM //=
      addn2 ?addnS -?addnA ?(ltn_add2r _ 1) 2!lognE /= divn_gt0 //= dvdn_divRL
      ?(dvdn_addr _ (dvdnn 4)) (@dvdn_addr 4 2 _) // (@dvdn_lmulr 2 2 a H) // H.
  - move => /= {H0} H3 H0; apply: H3.
    have {H0} H3 m: logn p.+2 (\sum_(k < p.+2 ^ m) a.+2 ^ k) = m.
      apply (@addnI (logn p.+2 a.+2.-1)) => {H1}.
      rewrite -lognM ?sum_expn_gt0 ?expn_gt0 //
              -predn_exp /= LemmaP' // -pfactor_dvdn //.
      by case: p H0 {H}.
    move: (H1 (p.+2 ^ e.+1)).
    rewrite pfactor_dvdn ?sum_expn_gt0 ?expn_gt0 // (H3 e.+1) leqnn.
    case/esym/(dvdn_pfactor _ _ H) => y H0 ?; subst l; f_equal; apply/eqP.
    by rewrite eqn_leq H0 -(H3 y) -pfactor_dvdn ?sum_expn_gt0 ?expn_gt0 //= H1.
Qed.

Lemma contains_zero p a e :
  prime p -> a %% p = 1 -> p ^ e %| \sum_(k < p ^ e) a ^ k.
Proof.
  move: p a => [| []] // p [| [| a]] // H H0.
  - by rewrite -(big_mkord xpredT) (eq_bigr _ (fun n _ => exp1n n))
               sum_nat_const_nat subn0 muln1.
  - have: 0 < \sum_(k < p.+2 ^ e) a.+2 ^ k.
      apply (@proj2 (0 < a.+2.-1)); apply/andP; rewrite -muln_gt0 -predn_exp.
      apply (@leqpp 2), (@leq_trans a.+2) => //.
      by rewrite -{1}(expn1 a.+2) leq_exp2l // expn_gt0.
    move/eqP: H0.
    rewrite -{1}(@modn_small 1 p.+2) // (eqn_modDl 1) mod0n -/(_ %| _) => H0 H1.
    rewrite pfactor_dvdn // -(leq_add2l (logn p.+2 a.+2.-1)) -lognM //
            -predn_exp /=.
    case: p e H H0 {H1} => [[| e] _ H | p e H H0].
    + by rewrite expn0 expn1 addn0.
    + rewrite
        expnS expnM (sqrnD 1) add1n addSn mul1n expnS expn1 -mulnDl LemmaP' //=.
      * by rewrite addnS lognM // -addnA (leq_add2r _ 1) lognE dvdn_addr.
      * by rewrite lognM // lognE dvdn_addr //= addSn addnC lognE H.
    + by rewrite LemmaP' //= lognE H H0.
Qed.

Lemma leq_cardI (T : finType) (x y : pred T) :
  #|x| + #|y| - #|T| <= #|predI x y|.
Proof.
  rewrite -cardUI -addnC -subnBA.
  - apply leq_subr.
  - apply max_card.
Qed.

Section LCG.

(* cM is LCG's modulus constant, 1 < cM *)
Variable (cM' : nat).
Definition cM := cM'.+2.

(*
cA is LCG's multiplier constant,
cC is LCG's increment constant,
cA, cC < cM (m : 'I_n means 0 <= m < n)
*)
Variable (cA cC : 'Z_cM).
(*
nextr x == (cA * x + cC) %% cM
           next random number of x
*)
Definition nextr (x : 'Z_cM) : 'Z_cM := (cA * x + cC)%R.

(*
rseq n x == [:: x; nextr x; nextr (nextr x); ...; iter n.-1 nextr x]
            random number sequence from x
*)
Notation rseq n x := (traject nextr x n).

(*
(forall x, full_period x) <=> LCG (cM, cA, cC) have a full period.
*)
Definition full_period n := uniq (rseq cM n) && (iter cM nextr n == n).

(*
full_period': equivalent proposition of (forall x, full_period x)
see: http://en.wikipedia.org/wiki/Linear_congruential_generator#Period_length
*)
Definition full_period' :=
  [&& coprime cM cC,
      all (fun p => cA %% p == 1) (primes cM) &
      if 4 %| cM then cA %% 4 == 1 else true].

Lemma general_term_0 n :
  (iter n nextr 0%R) = (cC * \sum_(k < n) cA ^+ k)%R.
Proof.
  rewrite /nextr; elim: n => /= [| n ->].
  - by rewrite big_ord0 mulr0.
  - rewrite big_ord_recl /= expr0 mulrDr mulr1 addrC mulrCA big_distrr /=.
    do 2 f_equal; apply eq_bigr => i _.
    by rewrite /bump leq0n add1n exprS.
Qed.

Lemma fp_contains_all (n x : 'Z_cM) : full_period n -> x \in rseq cM n.
Proof.
  rewrite /full_period; case/andP; move/card_uniqP => H _.
  move: (leq_cardI (mem (rseq cM n)) (pred1 x)).
  rewrite card_ord [X in _ - X]Zp_cast // {}H size_traject card1 addKn.
  case/card_gt0P => x'; rewrite inE /=.
  by case/andP => H; move/eqP => ?; subst x'.
Qed.

Lemma fp_equiv1 x : (forall y, full_period y) <-> full_period x.
Proof.
  split; first by apply.
  move => H y.
  case/andP: H (fp_contains_all y H) => H; move/eqP => H0.
  case/trajectP => i H1 H2.
  rewrite /full_period {3}H2 -H0 -iter_add addnC iter_add -H2 eqxx andbT.
  move: H; rewrite !looping_uniq /looping; apply contra.
  case/trajectP => j H3 H4.
  apply/trajectP; exists j => //; move: H4.
  by rewrite -H0 H2 -!iter_add !(addnC cM'.+1) !(addnC j)
    -{6 8}(subnK (ltnW H1)) -!(addnA (cM - i)) !(iter_add (cM - i)) => ->.
Qed.

Lemma fp_equiv2 :
  full_period 0%R <->
  forall m n, (m == n %[mod cM]) = (iter m nextr 0%R == iter n nextr 0%R).
Proof.
  rewrite /full_period; split;
    [ case/andP => H H0 m n | move => H; apply/andP; split ].
  - rewrite (divn_eq m cM) (divn_eq n cM) !modnMDl !modn_mod.
    elim: (m %/ cM) => [| md ->]; [elim: (n %/ cM) => [| nd ->] | ];
      try by rewrite mulSnr addnAC (iter_add _ cM) (eqP H0).
    by rewrite -!(nth_traject nextr (@ltn_pmod _ cM (ltn0Sn cM')))
               nth_uniq // size_traject ltn_pmod.
  - rewrite looping_uniq; apply/negP => H0.
    case/trajectP: {H0} (loopingP H0 cM.-1) => i H0.
    move/eqP; rewrite -H !modn_small //.
    - by rewrite eq_sym ltn_eqF.
    - by rewrite ltnW // ltnS.
  - by move: (H cM 0); rewrite modnn mod0n eqxx; move/esym/eqP => ->.
Qed.

Lemma fp_equiv3 :
  (forall m n, (m == n %[mod cM]) = (iter m nextr 0%R == iter n nextr 0%R)) <->
  (coprime cM cC /\
   forall m n, (m == n %[mod cM]) =
               (\sum_(k < m) cA ^ k == \sum_(k < n) cA ^ k %[mod cM])).
Proof.

Abort.

End LCG.

Notation rseq cM' cA cC n x := (traject (@nextr cM' cA cC) x n).

Definition lcg_rseq m a b :=
  if m is m'.+1
    then map (fun (x : 'Z_(cM m')) => x : nat) (rseq m' (inZp a) (inZp b) m Zp0)
    else [::].

Eval compute in (lcg_rseq 36 13 7).
Eval compute in (lcg_rseq 8 1 3).
Eval compute in (lcg_rseq 9 1 4).
Eval compute in (lcg_rseq 10 1 3).
