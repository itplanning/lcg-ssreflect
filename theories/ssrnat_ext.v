Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.choice Ssreflect.fintype.
Require Import
  MathComp.div MathComp.path MathComp.bigop MathComp.prime MathComp.binomial.
Require Import Coq.Program.Wf LCG.seq_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Theorem well_founded_lt : well_founded (fun x y => x < y).
Proof.
  move => x.
  move: {2}x (leqnn x) => n.
  elim: n x => [ | n IHn ] x H; constructor => y H0.
  - apply False_ind, notF.
    rewrite -(ltn0 y).
    apply (leq_trans H0 H).
  - apply IHn.
    rewrite -ltnS.
    apply (leq_trans H0 H).
Defined.

Lemma leqpp m n : m <= n -> m.-1 <= n.-1.
Proof. by case: m => //=; case: n. Qed.

Lemma mulnr_inj n : 0 < n -> injective (muln n).
Proof.
  case: n => //= n _ x y.
  by move/(f_equal (divn^~ n.+1)); rewrite !mulKn.
Qed.

Lemma mulnl_inj n : 0 < n -> injective (muln^~ n).
Proof.
  case: n => //= n _ x y.
  by move/(f_equal (divn^~ n.+1)); rewrite !mulnK.
Qed.

Lemma expn_sub x m n : m <= n -> x ^ n - x ^ m = (x ^ m) * (x ^ (n - m)).-1.
Proof.
  by move/subnK => {1}<-; rewrite expnD -{2}(mul1n (x ^ m)) -mulnBl subn1 mulnC.
Qed.

Lemma divn_eq0 m n : (m %/ n == 0) = (n == 0) || (m < n).
Proof.
  case: (ltnP m n).
  - by move => H; rewrite orbT divn_small.
  - move => H; move/subnKC: (H) => <-.
    rewrite orbF -{1}(mul1n n).
    case: n H.
    + by move => _; rewrite divn0.
    + by move => n; rewrite divnMDl.
Qed.

Lemma ndvdn_logn p m : ~~ (p %| m) -> logn p m = 0.
Proof.
  by rewrite lognE; case: ifP => //; case/and3P => _ _ ->.
Qed.

Lemma leq_expnl n m : (n <= n ^ m) = ((n < 2) || (0 < m)).
Proof.
  case: n m => // n [] /=.
  - by rewrite ltnn orbF expn0.
  - move => m.
    by rewrite ltn0Sn orbT expnS -{1}(muln1 (n.+1)) leq_mul // expn_gt0.
Qed.

Lemma dvdn_lmull d1 d2 m : d1 * d2 %| m -> d1 %| m.
Proof.
  case/dvdnP => k => ->.
  by rewrite mulnCA dvdn_mulr.
Qed.

Lemma dvdn_lmulr d1 d2 m : d1 * d2 %| m -> d2 %| m.
Proof.
  by rewrite mulnC; apply dvdn_lmull.
Qed.

Lemma poly1_eq1 x n :
  iter n (fun a => (a * x).+1) 0 = \sum_(n' < n) x ^ n'.
Proof.
  rewrite -(big_mkord xpredT (expn x)).
  elim: n => /=.
  - by rewrite big_nil.
  - move => n ->.
    rewrite big_distrl /= index_iota_0s big_cons big_map expn0 add1n.
    by apply f_equal, eq_bigr => i _; rewrite expnS mulnC.
Qed.

Lemma poly1_eq2 x n :
  iter n (fun a => (a * x).+1) 0 * x.-1 = (x ^ n).-1.
Proof.
  case: x => //=.
  - by rewrite muln0; case: n => //= n; rewrite exp0n.
  - move => x.
    elim: n => /=.
    + by rewrite mul0n.
    + move => n.
      have ->: (x.+1 ^ n.+1).-1 = x + (x.+1 ^ n).-1 * x.+1.
        rewrite expnS mulnC.
        move: (erefl : (0 < x.+1) || (n == 0)).
        by rewrite -expn_gt0; case: (x.+1 ^ n).
      by move => <-; rewrite mulSn mulnAC.
Qed.

Lemma poly1_eq3 x n m :
  iter n (fun a => (a * x).+1) m = m * (x ^ n) + iter n (fun a => (a * x).+1) 0.
Proof.
  elim: n m => //= [| n IH] m.
  - by rewrite expn0 muln1 addn0.
  - by rewrite addnS expnS mulnCA (mulnC x) -mulnDl -IH.
Qed.

Lemma poly1_leq x n m :
  n <= m ->
  iter n (fun a => (a * x).+1) 0 <= iter m (fun a => (a * x).+1) 0.
Proof.
  elim: n m => //=.
  move => n IH [] //= m; rewrite !ltnS.
  by rewrite leq_mul2r; move/IH => ->; rewrite orbT.
Qed.

Lemma poly1_sub x n m :
  m <= n ->
  iter n (fun a => (a * x).+1) 0 - iter m (fun a => (a * x).+1) 0 =
  x ^ m * iter (n - m) (fun a => (a * x).+1) 0.
Proof.
  elim: m n => /=.
  - by move => n _; rewrite !subn0 expn0 mul1n.
  - move => n IH [] //= m.
    by rewrite ltnS !subSS -mulnBl mulnC expnS -mulnA => H; f_equal; apply IH.
Qed.

Lemma poly1_add x y z m :
  iter (y + z) (fun a => (a * x).+1) 0 =
  iter y (fun a => (a * x).+1) (iter z (fun a => (a * x).+1) 0 %% m) %[mod m].
Proof.
  apply/eqP; elim: y.
  - by rewrite add0n /= modn_mod.
  - move => y IH.
    rewrite addSn /= -!(addn1 (_ * _)) eqn_modDr -!(modnMml (iter _ _ _)).
    by move/eqP: IH => ->.
Qed.

Lemma eqn_modDmull m n x y :
  coprime m n -> (n * x == n * y %[mod m]) = (x == y %[mod m]).
Proof.
  move => H; move: x y.
  have H0: forall x y,
             y <= x -> (n * x == n * y %[mod m]) = (x == y %[mod m]) => x y.
    move => H0.
    rewrite !eqn_mod_dvd //; last rewrite leq_mul2l H0 orbT //.
    by rewrite -mulnBr Gauss_dvdr.
  case/orP: (leq_total x y);
    first rewrite [X in X = _]eq_sym [X in _ = X]eq_sym; apply H0.
Qed.

Lemma eqn_modDmulr m n x y :
  coprime m n -> (x * n == y * n %[mod m]) = (x == y %[mod m]).
Proof.
  by rewrite -!(mulnC n); apply eqn_modDmull.
Qed.

Lemma coprime_ppS m n : 0 < m -> coprime m (n * \prod_(p <- primes m) p).+1.
Proof.
  rewrite /primes => H.
  case: (prime_decomp_correct H).
  rewrite /pfactor => H0.
  move: (prime_decomp m) H0 H => xs -> H _ _;
    elim: xs n H; last case => /=.
  - by move => n _; rewrite big_nil coprime1n.
  - move => x1 x2 xs IH n.
    rewrite !big_cons /= mulnA muln_gt0 expn_gt0.
    case/andP => H H0.
    rewrite coprime_mull (IH (n * x1) H0) andbT {IH H0}.
    apply coprime_expl.
    by rewrite /coprime -addn1 mulnAC gcdnMDl gcdn1.
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

Lemma expSn a n : a.+1 ^ n = \sum_(i < n.+1) 'C(n, i) * a ^ i.
Proof.
  rewrite -add1n Pascal.
  by apply eq_bigr => i _; rewrite exp1n mul1n.
Qed.

Lemma expSS a n :
  a.+1 ^ n.+1 = (a ^ n.+1).+1 + \sum_(1 <= i < n.+1) 'C(n.+1, i) * a ^ i.
Proof.
  rewrite -add1n Pascal' exp1n add1n.
  by f_equal; apply eq_bigr => i _; rewrite exp1n mul1n.
Qed.

Lemma binomial_sum m n : \sum_(n <= k < m) 'C(k, n) = 'C(m, n.+1).
Proof.
  elim: m n.
  - by move => n; rewrite big_nil bin0n.
  - move => m IH [].
    + by rewrite bin1 (eq_bigr _ (fun n _ => bin0 n))
                 big_const_nat subn0 iter_addn_0 mul1n.
    + move => n; case (leqP m n) => H.
      * rewrite /index_iota subSS bin_small //.
        by move/eqP: H => ->; rewrite big_nil.
      * by rewrite
          binS -!IH {1}/index_iota subSS -{1}add1n iota_addl big_map
          -/(index_iota n m) (eq_bigr (fun j => 'C(j, n.+1) + 'C(j, n))) //
          -(add0n (\sum_(n.+1 <= _ < m) _)) -{2}(bin_small (leqnn n.+1))
          -(big_cons 0 addn n (index_iota n.+1 m) xpredT) /index_iota
          -/(iota n (m - n.+1).+1) subnSK // -big_split /=.
Qed.

Lemma poly1_dvdn_expn p x n :
  2 < p -> prime p -> x %% p = 1 ->
  p ^ n %| iter (p ^ n) (fun a => (a * x).+1) 0.
Proof.
  move => Hp Hp0 Hx.
  case: x Hx; first by rewrite mod0n.
  move => x; move/eqP.
  rewrite -(modn_small (ltnW Hp)) eqn_mod_dvd // subn1 /=.
  case: (@eqP _ x 0).
  - move => -> _.
    by rewrite (eq_iter (fun a => eq_S _ _ (muln1 a))) iter_succn_0 dvdnn.
  - move/eqP; rewrite -lt0n => Hx Hx0.
    have: exists k m, 0 < m /\ coprime p k /\ x = (k * p ^ m).
      move: x Hx Hx0.
      refine (well_founded_ind well_founded_lt _ _) => x IH Hx0 Hx1.
      move: (IH (x %/ p) (ltn_Pdiv (ltnW Hp) Hx0)) => {IH}.
      rewrite divn_gt0; last by rewrite (ltnW (ltnW Hp)).
      rewrite (dvdn_leq Hx0 Hx1) => IH.
      case/boolP: (p %| x %/ p).
      + case/(IH erefl) => k' [m' [H [H0 H1]]].
        exists k', m'.+1; split => //; split => //.
        move: Hx1; rewrite dvdn_eq H1; move/eqP => <-.
        by rewrite mulnAC -mulnA -expnS.
      + move => H.
        exists (x %/ p), 1; split => //; split.
        * by rewrite (prime_coprime _ Hp0).
        * by apply/esym/eqP; rewrite expn1 -dvdn_eq.
    case => k [m [H [H0 ->]]] {x Hx Hx0}.
    rewrite
      poly1_eq1 (eq_bigr _ (fun (n : ordinal _) _ => expSn (k * p ^ m) n))
      (eq_bigr (fun i : 'I_(p ^ n) => _)
               (fun i _ => big_ord_widen
                             _ (fun j => 'C(i, j) * _ ^ j) (ltn_ord i)))
      (exchange_big_dep xpredT) //=.
    apply dvdn_sum => i _.
    rewrite
      -(big_mkord (fun j => i < j.+1) (fun j => 'C(j, i) * (k * p ^ m) ^ i))
      -big_filter iota_cutl max0n -big_distrl /= binomial_sum expnMn.
    case: m H => //= m _.
    rewrite -expnM mulSn expnD (mulnC (p ^ i)) (mulnA (k ^ i)) mulnCA.
    apply dvdn_mull => {m k H0}.
    case: (leqP n i).
    + by move => H; apply dvdn_mull, dvdn_exp2l.
    + move: (nat_of_ord i) => {i} i H.
      rewrite -(subnK (ltnW H)) {1}expnD dvdn_pmul2r;
        last by rewrite expn_gt0 (ltnW (ltnW Hp)).
      move: (n - i) => {n H} n.
      have H: i < p ^ (n + i).
        apply leq_trans with (p ^ i).
        * by apply ltn_expl, prime_gt1.
        * by rewrite leq_exp2l ?leq_addl // prime_gt1.
      have H0: 0 < 'C(p ^ (n + i), i.+1) by rewrite bin_gt0.
      rewrite pfactor_dvdn // -(leq_add2r (logn p (i.+1)`!)) -lognM ?fact_gt0 //
              bin_ffact ffactnS.
      rewrite lognM ?expn_gt0 ?(@prime_gt0 p) ?ffact_gt0 //.
      * rewrite pfactorK // -addnA leq_add2l logn_fact //
                -ltnS -addSn /index_iota subn1 -pred_Sn.
        apply leq_trans with i.+1; last apply leq_addr.
        elim: {n i Hp H H0} i.+1 {1 3 5 6}i.+1 (leqnn i.+1) (ltn0Sn i).
        - by move => n H H0; move: (leq_trans H0 H).
        - move => /= n IH i H H0.
          rewrite big_cons expn1 -(addn1 1) iota_addl big_map.
          have H1: forall j, i %/ p ^ (1 + j) = i %/ p %/ p ^ j
            by move => j; rewrite expnD expn1 divnMA.
          rewrite (eq_bigr _ (fun j _ => H1 j)) {H1} -ltn_subRL.
          case/boolP: (i %/ p == 0).
          + move/eqP => ->.
            by rewrite (eq_bigr _ (fun j _ => div0n (p ^ j))) subn0
                       -(addnK 1 n) -/(index_iota 1 (n + 1)) addn1 big_const_nat
                       iter_addn mul0n add0n.
          + move => H1; apply leq_trans with (i %/ p).
            * apply IH.
              - rewrite -ltnS; apply leq_trans with i => //.
                by apply ltn_Pdiv => //; apply prime_gt1.
              - by case: (i %/ p) H1.
            * rewrite -(leq_add2r (i %/ p)) subnK; last apply leq_div.
              rewrite addnn -muln2 -leq_divRL //.
              by apply leq_div2l => //; apply prime_gt1.
      * by rewrite -ltnS prednK ?expn_gt0 ?prime_gt0.
Qed.

Lemma Fermat' p x : prime p -> p %| (x ^ p) - x.
Proof.
  move => H.
  have H0: (0 < p) by apply prime_gt0.
  elim: x.
  - by rewrite exp0n.
  - move => x IH.
    rewrite -{2}(prednK H0) expSS prednK //= addnC -addnBA.
    + rewrite dvdn_addr // big_nat.
      apply big_ind => //.
      * apply dvdn_add.
      * by move => i H2; apply dvdn_mulr, prime_dvd_bin.
    + case: x {IH} => [| x].
      * by rewrite exp0n.
      * rewrite ltnS -{1}(expn1 x.+1).
        by apply leq_pexp2l.
Qed.

Lemma Fermat'' p x n : prime p -> p %| x ^ p ^ n - x.
Proof.
  move => H.
  have H0: (0 < p) by apply prime_gt0.
  elim: n x.
  - by move => x; rewrite expn0 expn1 subnn.
  - move => n IH x.
    rewrite expnS expnM.
    case: x; first by rewrite !exp0n // expn_gt0 H0.
    move => x.
    rewrite -(@subnK (x.+1 ^ p) ((x.+1 ^ p) ^ p ^ n)) -?addnBA ?leq_expnl.
    + by apply dvdn_add => //; apply Fermat'.
    + by rewrite (prime_gt0 H) orbT.
    + by rewrite expn_gt0 (prime_gt0 H) /= orbT.
Qed.

Lemma Fermat p x : prime p -> coprime p x -> p %| (x ^ p.-1).-1.
Proof.
  move => H H0.
  rewrite -(Gauss_dvdr _ H0) -subn1 mulnBr muln1 -expnS prednK //.
  - by apply Fermat'.
  - by apply prime_gt0.
Qed.

Lemma LemmaP p x :
  prime p -> 2 < p ^ logn p x -> logn p (x.+1 ^ p).-1 = (logn p x).+1.
Proof.
  move: p x => [] // [] // p [| []]; rewrite ?logn0 ?logn1 ?expn0 // => x H H0.
  rewrite expSS addSn /= /index_iota subn1 /= !expnS /=
          big_cons bin1 expn1 (mulnC p.+2) (iota_addl 2 0) big_map.
  have/(eq_bigr _) -> i: true ->
      'C(p.+2, i.+2) * x.+2 ^ i.+2 = x.+2 * (x.+2 * ('C(p.+2, i.+2) * x.+2 ^ i))
    by rewrite !expnS 2!(mulnCA x.+2).
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
    + rewrite -/(index_iota 0 p.+1) big_nat.
      by apply big_rec => // n m H1 H2;
        apply dvdn_add => //; apply dvdn_mulr, prime_dvd_bin.
Qed.

Lemma LemmaR p x n l :
  let zero i := p ^ n %| iter i (fun a => (a * x).+1) 0 in
  prime p -> 1 < x < p ^ n ->
  0 < l -> (forall l', 0 < l' < l -> ~~ zero l') -> zero l ->
  (l == p ^ n) = ((if p == 2 then 4 else p) %| x.-1).
Proof.
  move: p x n l => [] // [] // p [] // [] // x [] // n [] // l zero H;
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
  have H4 m: 0 < (x.+2 ^ p.+2 ^ m).-1.
    apply (@leqpp 2), (@leq_trans x.+2) => //.
    by rewrite -{1}(expn1 x.+2) leq_exp2l // expn_gt0.
  have H5 m: 0 < iter (p.+2 ^ m) (fun a : nat => (a * x.+2).+1) 0
    by rewrite -(@ltn_pmul2r x.+1) // mul0n poly1_eq2.
  apply/esym/idP; case: ifP; move/eqP.
  - move => {H3} H3; move: H3 H1 H2 => -> {l} H1 H2.
    have {H0 H1 H4 H5} H0: p = 0 -> x %% 4 <> 1.
      move => ? {H H2}; move: H1; subst zero p => H H1.
      case: n H H0; first by rewrite expn1 //.
      move => n H H0.
      have/H/negP {H0}: 0 < 2 ^ n.+1 < 2 ^ n.+2 by rewrite
        expn_gt0 //= (expnS 2 n.+1) -{1}(mul1n (2 ^ n.+1)) ltn_mul2r expn_gt0.
      apply.
      rewrite pfactor_dvdn // -ltnS -[X in _ < X]addn1.
      have {3}->: 1 = logn 2 x.+1 by rewrite
        (divn_eq x 4) H1 -addnS /= {2}(erefl : 4 = 2 * 2) mulnA -mulSnr
        lognM // lognE /= -{1}(addn1 (_ * _)) dvdn_addr //= dvdn_mull.
      rewrite -lognM // poly1_eq2 -pfactor_dvdn //.
      elim: n {H}.
      + rewrite expn1 (divn_eq x 4) H1 -!addnS
                sqrnD addnAC (erefl : 3 ^ 2 = 9) addnS /=.
        do 2 apply dvdn_add => //.
        * by rewrite expnMn (erefl : 4 ^ 2 = 2 * 8) mulnA dvdn_mull.
        * by rewrite (@dvdn_pmul2l 2 4) // mulnAC dvdn_mull.
      + move => e IH.
        rewrite (expnS 2 e.+1) mulnC expnM -(@prednK (_ ^ _ ^ _)) ?expn_gt0 //
                -(addn1 _.-1) sqrnD muln1 addn1 addSn /= expnS.
        apply dvdn_add; rewrite dvdn_mul //.
        by move: IH; rewrite expnS; apply dvdn_lmull.
    suff {H0}: p.+2 %| x.+1.
      move => {zero H2}.
      case: ifP => //; move/eqP.
      case => ?; subst.
      rewrite (divn_eq x 4) -!addnS /dvdn
              {2}(erefl : 4 = 2 * 2) {1}mulnA !addnS /= -!addnS !modnMDl.
      move: (x %% 4) (@ltn_pmod x 4 erefl) (H0 erefl).
      do 4 case => //.
    subst zero.
    apply/negP; move/negP => H0; move: H2.
    rewrite -(@Gauss_dvdl (p.+2 ^ n.+1) _ x.+1) ?poly1_eq2.
    + rewrite {1}expnS.
      move/dvdn_lmull/(fun h => dvdn_sub h (Fermat'' x.+2 n.+1 H)).
      apply/negP.
      by rewrite -subn1 subnAC subnBA ?addKn ?subn1 //
         -{1}(expn1 x.+2) leq_exp2l // expn_gt0.
    + by rewrite coprime_pexpl // prime_coprime.
  - move => /= H7 H6; apply: H7.
    have {H6} H6 m:
        logn p.+2 (iter (p.+2 ^ m) (fun a : nat => (a * x.+2).+1) 0) = m.
      apply (@addIn (logn p.+2 x.+1)).
      rewrite -lognM // poly1_eq2.
      elim: m {H0 H1 H2 H3 H4} => // g IH.
      rewrite expnS mulnC expnM -(@prednK (_ ^ _ ^ _))
              ?expn_gt0 // LemmaP // {}IH //.
      subst zero; move: p x H H5 H6 => [[] // | p] /= x H H0 H1.
      + by rewrite
          2!lognE /= dvdn_divRL ?H0 (@dvdn_lmulr 2 2) // divn_gt0 //= H1
          !addnS !expnS (@ltn_pmul2l 2 1) // (@leq_pmul2l 2 1) // expn_gt0.
      + rewrite lognE H /= H1 addnS expnS.
        by apply (@leq_mul 3 1) => //; rewrite expn_gt0.
    subst zero; move: H H0 H1 H2 H3 H4 H5 H6 => H H0 H1 H2 H3 H4 H5 H6.
    move: (H3 (p.+2 ^ n.+1)).
    rewrite pfactor_dvdn // (H6 n.+1) leqnn => H7; move: {H7} (H7 erefl).
    case/(dvdn_pfactor _ _ H) => y H7 H8.
    rewrite pfactor_dvdn // H8 (H6 y) in H2.
    by rewrite H8; f_equal; apply/eqP; rewrite eqn_leq H7 H2.
Qed.
