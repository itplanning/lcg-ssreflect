Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.choice Ssreflect.fintype
  MathComp.div MathComp.path MathComp.bigop MathComp.prime MathComp.finset
  MathComp.binomial.
Require Import LCG.seq_ext LCG.ssrnat_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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
Variable (cM' : nat).
Definition cM := cM'.+1.

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
Definition nextr (x : 'I_cM) : 'I_cM :=
  @Ordinal cM ((cA * x + cC) %% cM) (ltn_pmod (cA * x + cC) (ltn0Sn cM')).

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
full_period': equivalent proposition of (forall x, full_period x)
see: http://en.wikipedia.org/wiki/Linear_congruential_generator#Period_length
*)
Definition full_period' :=
  [&& coprime cM cC,
      all (fun p => cA %% p == 1) (primes cM) &
      if 4 %| cM then cA %% 4 == 1 else true].

Lemma general_term_0 n :
  iter n nextr (inord 0) =
  @Ordinal cM (iter n (fun a => (a * cA).+1) 0 * cC %% cM)
           (ltn_pmod _ (ltn0Sn cM')).
Proof.
  apply/eqP; rewrite /eq_op /=.
  elim: n => /=.
  - by rewrite inordK.
  - move => n; move/eqP => /= ->.
    by rewrite mulSn (addnC cC) eqn_modDr modnMmr mulnC mulnAC.
Qed.

Lemma fp_contains_all (n x : 'I_cM) : full_period n -> x \in rseq cM n.
Proof.
  rewrite /full_period; case/andP; move/card_uniqP => H _.
  move: (leq_cardI (mem (rseq cM n)) (pred1 x)) => /=.
  rewrite card_ord {}H size_iterseq addKn card1.
  move: (n :: rseq cM' (nextr n)) => {n} xs.
  case/boolP: (x \in xs) => // H.
  have H0: predI (mem xs) (pred1 x) =i pred0.
    move: H.
    rewrite /eq_mem /mem /= /in_mem /= => H x'.
    case/boolP: (x' == x).
    - by move/eqP => ->; rewrite andbT; apply/negbTE.
    - by rewrite andbF.
  by rewrite (eq_card H0) card0.
Qed.

Lemma fp_equiv1 x : (forall y, full_period y) <-> full_period x.
Proof.
  split; first by apply.
  move => H y.
  case/andP: H (fp_contains_all y H) => H; move/eqP => H0 H1.
  rewrite /full_period.
  case: (in_loop_iterseq H1 (esym H0)) => n; move/and3P => [H2].
  move/eqP => ?; subst y; move/eqP => H3.
  apply/andP; split.
  - by rewrite H3 rot_uniq.
  - by rewrite -{2}H0 -!iter_add addnC.
Qed.

End LCG'.

Notation rseq cM' cA cC n x := (iterseq n (@nextr cM' cA cC) x).

End LCG.

Definition lcg_rseq m a b :=
  match m with
    | m'.+1 =>
      map (@nat_of_ord m'.+1)
          (LCG.rseq m'
                    (@Ordinal m'.+1 (a %% m'.+1) (ltn_pmod a (ltn0Sn m')))
                    (@Ordinal m'.+1 (b %% m'.+1) (ltn_pmod b (ltn0Sn m')))
                    m
                    (@Ordinal m'.+1 0 (ltn0Sn m')))
    | _ => [::]
  end.

Eval compute in (lcg_rseq 36 13 7).
Eval compute in (lcg_rseq 8 1 3).
Eval compute in (lcg_rseq 9 1 4).
Eval compute in (lcg_rseq 10 1 3).
