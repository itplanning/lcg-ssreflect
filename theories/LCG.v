Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool
        Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.div
        Ssreflect.choice Ssreflect.fintype Ssreflect.path Ssreflect.bigop
        Ssreflect.prime.
Require Import Coq.Program.Wf.

Set Implicit Arguments.

Section seq_ext.

Variable (T : Type).

(* iterseq n f x == [:: x; f x; f (f x); ...; iter n f x] *)
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
  by rewrite (IH m (f x) H) -{2}addn1 iter_add.
Qed.

End seq_ext.

Section seq_ext'.

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
    by rewrite ltnS -{2}addn1 iter_add.
Qed.

Lemma in_loop_iterseq n f (x y : T) :
  y \in iterseq n f x -> x = iter n f x ->
  exists m, m < n /\ y = iter m f x /\ iterseq n f y = rot m (iterseq n f x).
Proof.
  case/in_iterseq => m [H H0] H1; exists m.
  do 2 split => //.
  rewrite (iterseq_cat n (n - m) f y) ?leq_subr //
          (iterseq_cat n m f x (ltnW H)).
  rewrite -{4}(size_iterseq m f x) rot_size_cat -H0.
  by rewrite (subKn (ltnW H)) {2}H0 -iter_add (subnK (ltnW H)) -H1.
Qed.

End seq_ext'.

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
cB is LCG's increment constant,
cA, cB < cM (m : 'I_n means 0 <= m < n)
*)
Variable (cA cB : 'I_cM).

(*
nextr x == (cA * x + cB) %% cM
           next random number of x
*)
Definition nextr (x : ordinal cM) : ordinal cM :=
  @Ordinal cM ((cA * x + cB) %% cM) (ltn_pmod (cA * x + cB) cM_cond).

(*
rseq n x == [:: x; nextr x; nextr (nextr x); ...; iter n nextr x]
            random number sequence from x
*)
Notation rseq n x := (iterseq n nextr x).

(*
(forall x, full_period x) <=> LCG (cM, cA, cB) have a full period.
*)
Definition full_period n := uniq (rseq cM n) && (iter cM nextr n == n).

(*
full_period': equivalent proposition of (forall x, full_period x)
see: http://en.wikipedia.org/wiki/Linear_congruential_generator#Period_length
*)
Definition full_period':=
  coprime cB cM &&
  (1 == cA %% \prod_(f <- prime_decomp cM)
           (if (f.1 == 2) && (2 <= f.2) then 4 else f.1)).

Lemma fp_contains_all (n x : 'I_cM) : full_period n -> x \in rseq cM n.
Proof.
  rewrite /full_period; case/andP; move/card_uniqP => H _.
  move: (leq_cardI _ (mem (rseq cM n)) (pred1 x)) => /=.
  rewrite card_ord {}H size_iterseq addKn card1.
  move: (rseq cM n) => {n} xs.
  case: (eqVneq (x \in xs) true) => //; rewrite /in_mem => H.
  have H0: predI (mem xs) (pred1 x) =i pred0.
    move: H.
    rewrite /eq_mem /mem /in_mem /= => H x'; rewrite /in_mem /=.
    case: (eqVneq x' x).
    - by move => ->; move: H; rewrite negb_eqb addbT; move/negbTE => ->.
    - by move/negbTE => ->; rewrite andbC.
  by rewrite (eq_card H0) card0.
Qed.

Lemma lcg_fp_equiv1 :
  (forall x, full_period x) <-> full_period (@Ordinal cM 0 cM_cond).
Proof.
  split; first by apply.
  move => H x.
  case/andP: H (fp_contains_all _ x H) => H; move/eqP => H0 H1.
  rewrite /full_period.
  case: (in_loop_iterseq _ _ _ _ H1 (esym H0)) => n [H2 [H3 H4]].
  apply/andP; split.
  - by rewrite H4 rot_uniq.
  - by rewrite H3 -{2}H0 -!iter_add addnC.
Qed.

End LCG'.

End LCG.
