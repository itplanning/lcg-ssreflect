Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.div Ssreflect.choice
  Ssreflect.fintype Ssreflect.path Ssreflect.bigop Ssreflect.prime
  Ssreflect.finset Ssreflect.binomial.
Require Import Coq.Program.Wf.

Set Implicit Arguments.

Section seq_ext.

Variable (T : Type).

(* iterseq n f x == [:: x; f x; f (f x); ... ; iter n f x] *)
Fixpoint iterseq n f (x : T) :=
  match n with
    | 0 => [::]
    | n.+1 => x :: iterseq n f (f x)
  end.

Lemma size_iterseq n f x : size (iterseq n f x) = n.
Proof.
  by elim: n x => //= n H x; rewrite H.
Qed.

Lemma iterseq_eq n f x : iterseq n f x = [seq iter m f x | m <- iota 0 n].
Proof.
  rewrite -{1}/(iter 0 f x).
  by elim: n 0 x => //= n IH m x; rewrite (IH m.+1).
Qed.

Lemma iterseq_cat n m f x :
  m <= n -> iterseq n f x = iterseq m f x ++ iterseq (n - m) f (iter m f x).
Proof.
  elim: n m x => /=; first by case.
  move => n IH [] // m x.
  rewrite ltnS subSS => H.
  by rewrite (IH m (f x) H) iterSr.
Qed.

End seq_ext.

Section seq_ext_eqtype.

Variable (T : eqType).

Lemma in_iterseq n f (x y : T) :
  y \in iterseq n f x -> exists m, m < n /\ y = iter m f x.
Proof.
  rewrite /in_mem /mem /=.
  elim: n x => //= n IH x.
  case/orP.
  - move/eqP => ->.
    by exists 0.
  - case/(IH (f x)) => m [H H0].
    exists m.+1.
    by rewrite ltnS H iterSr.
Qed.

Lemma in_loop_iterseq n f (x y : T) :
  y \in iterseq n f x -> x = iter n f x ->
  exists m, [/\ m < n, y = iter m f x & iterseq n f y = rot m (iterseq n f x)].
Proof.
  case/in_iterseq => m [H H0] H1; exists m.
  move: (ltnW H) => H2.
  by rewrite H -H0 (iterseq_cat n (n - m) f y) ?leq_subr // subKn //
             (iterseq_cat n m f x (ltnW H)) -{4}(size_iterseq m f x)
             rot_size_cat -H0 {4}H0 -iter_add subnK // -H1.
Qed.

End seq_ext_eqtype.

Theorem well_founded_lt : well_founded (fun n m => n < m).
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

Lemma leq_cardI (T : finType) (x y : pred T) :
  #|x| + #|y| - #|T| <= #|predI x y|.
Proof.
  rewrite -cardUI -addnC -subnBA.
  - apply leq_subr.
  - apply max_card.
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

(*
Lemma divmod_mul (a b c : nat) :
  0 < b -> 0 < c -> (a %/ b %% c == 0) = (a %% (b * c) < b).
Proof.
  move => /= H H0.
  rewrite (divn_eq a b).
  move: {a} (a %/ b) (a %% b) (ltn_pmod a H) => e f H1.
  rewrite (divn_eq e c).
  move: {e} (e %/ c) (e %% c) (ltn_pmod e H0) => g h H2.
  elim: g => [| g].
  - rewrite mul0n add0n divnMDl //.
    rewrite (divn_small H1) addn0 (modn_small H2) modn_small.
    - case: h H2 => //= h.
      by rewrite mulSn -addnA -ltn_subRL subnn ltn0 /eq_op.
    - case: c H0 H2 => // c _; rewrite ltnS mulnS addnC => H0.
      apply leq_ltn_trans with (f + c * b).
      - by rewrite leq_add2l leq_mul2r H0 orbC.
      - by rewrite mulnC ltn_add2r.
  - move => H3.
    by rewrite mulSn -addnA mulnDl -addnA divnMDl // addnC -(modnDmr _ c c)
               modnn addn0 H3 -(mul1n (c * b)) (mulnC c b) modnMDl.
Qed.
*)

Lemma leqpp m n : m <= n -> m.-1 <= n.-1.
Proof.
  by case: m => //=; case: n.
Qed.

Lemma subpp m n : (0 < m) == (0 < n) -> m.-1 - n.-1 = m - n.
Proof.
  by case: m => // m; case: n.
Qed.

Lemma mulnp m n : 0 < m -> 0 < n -> (m * n).-1 = n.-1 + (m.-1 * n).
Proof.
  by case: m => // m; case: n.
Qed.

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

Lemma expn_sub : forall x m n, m <= n -> x ^ n - x ^ m = (x ^ m) * (x ^ (n - m)).-1.
Proof.
  move => x; elim => //=.
  - by move => n H; rewrite expn0 subn1 mul1n subn0.
  - move => n IH [| m] //=; rewrite ltnS => H.
    by rewrite subSS !expnS -mulnBr (IH m H) mulnA.
Qed.

Lemma poly1_eq1 x n :
  iter n (fun a => (a * x).+1) 0 = \sum_(n' < n) x ^ n'.
Proof.
  rewrite -(big_mkord xpredT (expn x)).
  elim: n => /=.
  - by rewrite big_nil.
  - move => n ->.
    rewrite /index_iota !subn0 /= big_cons
      expn0 -(add1n 0) iota_addl big_map big_distrl /= !add1n.
    by f_equal; apply eq_bigr => i _; rewrite add1n mulnC -expnS.
Qed.

Lemma poly1_eq2 x n :
  iter n (fun a => (a * x).+1) 0 * x.-1 = (x ^ n).-1.
Proof.
  case: x => //=.
  - by rewrite muln0; case: n => //= n; rewrite exp0n.
  - move => x.
    elim: n => /=.
    - by rewrite mul0n.
    - move => n.
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

Lemma coprime_dvd_expn m n e : coprime m n -> (m %| n ^ e) = (m %| 1).
Proof.
  move => H; elim: e => //= e.
  by rewrite expnS Gauss_dvdr.
Qed.

Lemma expSn a n : a.+1 ^ n = \sum_(i < n.+1) 'C(n, i) * a ^ i.
Proof.
  rewrite -add1n Pascal.
  by apply eq_bigr => i _; rewrite exp1n mul1n.
Qed.

Goal forall m n, \sum_(n <= k < m) 'C(k, n) = 'C(m, n.+1).
Proof.
  elim.
  - by move => n; rewrite big_nil bin0n.
  - move => m IH [].
    - by rewrite bin1 (eq_bigr _ (fun n _ => bin0 n))
                 big_const_nat subn0 iter_addn_0 mul1n.
    - move => n.
      case (eqVneq (m <= n) true) => H.
      - rewrite /index_iota subSS bin_small //.
        by move/eqP: H => ->; rewrite big_nil.
      - rewrite binS -!IH.
        move/eqP/negP: H; rewrite -ltnNge => H.
        rewrite {1}/index_iota subSS -{1}add1n
                iota_addl big_map -/(index_iota n m).
        rewrite (@eq_bigr _ _ _ _ _ _ (fun j => 'C(1 + j, n.+1))
                          (fun j => 'C(j, n.+1) + 'C(j, n))) //.
        Search _ bigop eq.


Module LCG.
Section LCG'.

(* cM is LCG's modulus constant, 0 < cM *)
Variable (cM : nat) (cM_cond : 0 < cM).

(*
cA is LCG's multiplier constant,
cC is LCG's increment constant,
cA, cC < cM (m : 'I_n means 0 <= m < n)
*)
Variable (cA cC : 'I_cM).

(*
nextr x == (cA * x + cC) %% cM
           next random number of x
*)
Definition nextr (x : ordinal cM) : ordinal cM :=
  @Ordinal cM ((cA * x + cC) %% cM) (ltn_pmod (cA * x + cC) cM_cond).

(*
rseq n x == [:: x; nextr x; nextr (nextr x); ...; iter n nextr x]
            random number sequence from x
*)
Notation rseq n x := (iterseq n nextr x).

(*
(forall x, full_period x) <=> LCG (cM, cA, cC) have a full period.
*)
Definition full_period n := uniq (rseq cM n) && (iter cM nextr n == n).

(*
full_period': equivalent proposition of (forall x, full_period x)s
tee: http://en.wikipedia.org/wiki/Linear_congruential_generator#Period_length
*)
Definition full_period' :=
  [&& 0 < cA, coprime cM cC &
  ((if 4 %| cM then 2 else 1) * \prod_(p <- primes cM) p) %| cA.-1].

Lemma general_term_0 n :
  iter n nextr (@Ordinal cM 0 cM_cond) =
  @Ordinal cM (iter n (fun a => (a * cA).+1) 0 * cC %% cM) (ltn_pmod _ cM_cond).
Proof.
  apply/eqP; rewrite /eq_op /=.
  elim: n => /=.
  - by rewrite mul0n mod0n.
  - move => n; move/eqP => /= ->.
    by rewrite mulSn (addnC cC) eqn_modDr modnMmr mulnC mulnAC.
Qed.

Lemma fp_contains_all (n x : 'I_cM) : full_period n -> x \in rseq cM n.
Proof.
  rewrite /full_period; case/andP; move/card_uniqP => H _.
  move: (leq_cardI _ (mem (rseq cM n)) (pred1 x)) => /=.
  rewrite card_ord {}H size_iterseq addKn card1.
  move: (rseq cM n) => {n} xs.
  case: (eqVneq (x \in xs) true) => //; rewrite /in_mem => H.
  have H0: predI (mem xs) (pred1 x) =i pred0.
    move: H.
    rewrite /eq_mem /mem; do 2 rewrite /in_mem /=; move => H x'.
    case: (eqVneq x' x).
    - by move => ->; move: H; rewrite negb_eqb addbT; move/negbTE => ->.
    - by move/negbTE => ->; apply andbF.
  by rewrite (eq_card H0) card0.
Qed.

Lemma fp_equiv1 x : (forall y, full_period y) <-> full_period x.
Proof.
  split; first by apply.
  move => H y.
  case/andP: H (fp_contains_all _ y H) => H; move/eqP => H0 H1.
  rewrite /full_period.
  case: (in_loop_iterseq _ _ _ _ H1 (esym H0)) => n [H2 H3 H4].
  apply/andP; split.
  - by rewrite H4 rot_uniq.
  - by rewrite H3 -{2}H0 -!iter_add addnC.
Qed.

Lemma fp'_to_uniq n m :
  full_period' -> m <= n ->
  (n == m %[mod cM]) =
  (iter n (fun a : nat => (a * cA).+1) 0 * cC ==
   iter m (fun a : nat => (a * cA).+1) 0 * cC %[mod cM]).
Proof.
  case/andP => H; case/andP => H0 H1 H2.
  rewrite !eqn_mod_dvd //; last by rewrite leq_mul2r poly1_leq // orbT.
  rewrite -mulnBl Gauss_dvdl // poly1_sub //.
  case: (eqVneq 1 cA).
  - move => <-.
    by rewrite exp1n mul1n (eq_iter (fun x => eq_S _ _ (muln1 x))) iter_succn_0.
  - move => H3.
    have {H H3} H: 1 < cA by case: (nat_of_ord cA) H H3 => //; case.
    have H3: coprime cM cA.
      case: (nat_of_ord cA) H H1 => //= cA' _ H1.
      by case/dvdnP: H1 => x ->; rewrite mulnA; apply coprime_ppS.
    rewrite Gauss_dvdr ?coprime_expr //.
    move: {n H2} (n - m) => n.
    admit.
(*
    rewrite {2}/dvdn -(inj_eq (mulnl_inj _ (leqpp _ _ H))) mul0n
            !(muln_modl (leqpp _ _ H)) -mulnA poly1_eq2 -/(dvdn _ _) Gauss_dvdr.
    - move: {n H2} (n - m) => n.
      rewrite -poly1_eq2 (dvdn_pmul2r (leqpp _ _ H)) poly1_eq1.
      admit.
    - apply coprime_expr.
      by rewrite coprime_mull (coprimePn (ltnW H)) andbT.
*)
Qed.

End LCG'.

Notation rseq cM cMc cA cC n x := (iterseq n (@nextr cM cMc cA cC) x).

End LCG.


Definition lcg_rseq m a b :=
  match m with
    | m'.+1 =>
      let H : 0 < m'.+1 := erefl in
      map (@nat_of_ord m'.+1)
          (LCG.rseq m'.+1 H
                    (@Ordinal m'.+1 (a %% m'.+1) (ltn_pmod a H))
                    (@Ordinal m'.+1 (b %% m'.+1) (ltn_pmod b H))
                    m
                    (@Ordinal m'.+1 0 H))
    | _ => [::]
  end.

Eval compute in (lcg_rseq 36 13 7).
Eval compute in (lcg_rseq 8 1 3).
Eval compute in (lcg_rseq 9 1 4).
Eval compute in (lcg_rseq 10 1 3).

Eval compute in (lcg_rseq 4 1 1).
Eval compute in (lcg_rseq 8 1 1).
Eval compute in (lcg_rseq 8 5 1).
Eval compute in (lcg_rseq 16 1 1).
Eval compute in (lcg_rseq 16 5 1).
Eval compute in (lcg_rseq 16 9 1).
Eval compute in (lcg_rseq 16 13 1).
Eval compute in (lcg_rseq 9 1 1).
Eval compute in (lcg_rseq 9 4 1).
Eval compute in (lcg_rseq 9 7 1).
Eval compute in (lcg_rseq 25 1 1).
Eval compute in (lcg_rseq 25 6 1).
Eval compute in (lcg_rseq 25 11 1).
Eval compute in (lcg_rseq 25 16 1).
Eval compute in (lcg_rseq 25 21 1).
Eval compute in (lcg_rseq 27 1 1).
Eval compute in (lcg_rseq 27 4 1).
Eval compute in (lcg_rseq 27 7 1).
Eval compute in (lcg_rseq 27 10 1).
Eval compute in (lcg_rseq 27 13 1).
Eval compute in (lcg_rseq 27 16 1).
Eval compute in (lcg_rseq 27 19 1).

Goal
  forall p x n, 2 < p -> prime p -> x %% p = 1 ->
  p ^ n %| iter (p ^ n) (fun a => (a * x).+1) 0.
Proof.
  move => p x n Hp Hp0 Hx.
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
      case: (eqVneq (p %| x %/ p) true).
      - case/(IH erefl) => k' [m' [H [H0 H1]]].
        exists k', m'.+1; split => //; split => //.
        move: Hx1; rewrite dvdn_eq H1; move/eqP => <-.
        by rewrite mulnAC -mulnA -expnS.
      - rewrite negb_eqb addbT => H.
        exists (x %/ p), 1; split => //; split.
        - by rewrite (prime_coprime _ Hp0).
        - by apply/esym/eqP; rewrite expn1 -dvdn_eq.
    case => k [m [H [H0 ->]]] {x Hx Hx0}.
    rewrite poly1_eq1 (eq_bigr _ (fun (n : ordinal _) _ => expSn (k * p ^ m) n)).
    replace (\sum_(_ < p ^ n) _) with
      (\sum_(i < p ^ n) (k * p ^ m) ^ i * \sum_(i <= j < p ^ n) 'C(j, i)).
    - apply dvdn_sum => i _.
      rewrite expnMn -expnM.
      admit.
    - move: {k m H H0} (k * p ^ m) => m.
      elim: {p n Hp Hp0} (p ^ n); first by rewrite !big_ord0.
      move => n IH.
      rewrite big_ord_recl /= /bump.
Abort.

Goal
  forall p x m n, 2 < p -> prime p -> x %% p = 1 ->
  iter (m * p ^ n) (fun a => (a * x).+1) 0 %% (p ^ n.+1) = m %% p * p ^ n.
Proof.
  move => p x m n H H0 H1.
  elim: n m => //=.
  - move => m; apply/eqP; rewrite expn0 expn1 !muln1; elim: m => //= n IH.
    by rewrite -addn1 -(addn1 n) eqn_modDr -modnMmr H1 muln1.
  - move => n IH; elim => //=.
    - by rewrite !mod0n mul0n.
    - move => m IH'.
      rewrite mulSn iter_add poly1_eq3 -modnDm -modnMml {}IH'
              {1}(expnS p n.+1) mulnAC -muln_modl;
        last by rewrite expn_gt0 (ltnW (ltnW H)).
      rewrite -modnMmr -modnXm H1 exp1n modnMm muln1.
      replace (iter _ _ _ %% p ^ n.+2) with (p ^ n.+1).
      - rewrite addnC -mulSn (expnS p n.+1) -muln_modl;
          last by rewrite expn_gt0 (ltnW (ltnW H)).
        by rewrite -addn1 modnDml addn1.
      - 


