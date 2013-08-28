Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.div Ssreflect.choice
  Ssreflect.fintype Ssreflect.path Ssreflect.bigop.
Set Implicit Arguments.

Lemma iota_cutl n n' m :
  [seq x <- index_iota n m | n' <= x] = index_iota (maxn n n') m.
Proof.
  rewrite /index_iota maxnE subnDA.
  move: {m} (m - n) => m.
  elim: m n n' => //= m IH n n'.
  rewrite {}IH; case: ifP.
  - rewrite subnS -subn_eq0; move/eqP => -> /=.
    by rewrite !addn0 subn0.
  - move/negbT; rewrite -ltnNge => H.
    rewrite (subnBA m) // (subnBA m.+1 (ltnW H)) -!maxnE addnS addSn.
    by move/maxn_idPr: (H) => ->; move/maxn_idPr: (ltnW H) => ->.
Qed.

Lemma iota_cutr n m m' :
  [seq x <- index_iota n m | x < m'] = index_iota n (minn m m').
Proof.
  rewrite /index_iota.
Abort.

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
