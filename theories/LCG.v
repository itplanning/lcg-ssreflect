Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.div Ssreflect.choice
  Ssreflect.fintype Ssreflect.path Ssreflect.bigop Ssreflect.prime
  Ssreflect.finset Ssreflect.binomial.
Require Import Coq.Program.Wf LCG.seq_ext LCG.ssrnat_ext.

Lemma leq_cardI (T : finType) (x y : pred T) :
  #|x| + #|y| - #|T| <= #|predI x y|.
Proof.
  rewrite -cardUI -addnC -subnBA.
  - apply leq_subr.
  - apply max_card.
Qed.

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
  ((4 %| cM).+1 * \prod_(p <- primes cM) p) %| cA.-1].

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
