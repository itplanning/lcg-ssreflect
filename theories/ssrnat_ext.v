Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.div Ssreflect.choice
  Ssreflect.fintype Ssreflect.path Ssreflect.bigop Ssreflect.prime
  Ssreflect.finset Ssreflect.binomial.
Require Import Coq.Program.Wf LCG.seq_ext.

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

Fixpoint iedivn_rec (d m n : nat) : nat * nat :=
  match d with
    | 0 => (0, m)
    | d'.+1 =>
      match edivn m n with
        | (m', 0) =>
          let (x, y) := iedivn_rec d' m' n in (x.+1, y)
        | _ => (0, m)
      end
  end.

Definition iedivn m n := nosimpl (iedivn_rec m) m n.

Definition idivn m n := fst (iedivn m n).

Definition imodn m n := snd (iedivn m n).

Lemma iedivn_recdepth d d' m n :
  m < n ^ d -> m < n ^ d' -> 0 < m -> iedivn_rec d m n = iedivn_rec d' m n.
Proof.
  elim: d d' m => //=.
  - by rewrite expn0 => d' [].
  - move => d IH [].
    - by rewrite expn0 => [[]].
    - move => d' m /=.
      rewrite edivn_def !expnS.
      case: (eqVneq (m %% n) 0).
      - move => H; rewrite H.
        move/eqP/divnK: (H) => {1 2}<-; rewrite mulnC.
        rewrite !ltn_mul2l; case/andP => H0 H1; case/andP => _ H2 H3.
        rewrite (IH d') // divn_gt0 //.
        move/eqP in H; apply (dvdn_leq H3 H).
      - by rewrite -lt0n; move/prednK => <- /=.
Qed.

Lemma iedivn_recdepth' d d' m n :
  m <= d -> m <= d' -> 0 < m -> 1 < n -> iedivn_rec d m n = iedivn_rec d' m n.
Proof.
  by move => *; apply iedivn_recdepth => //;
    (apply leq_trans with (n ^ m); [ apply ltn_expl | rewrite leq_exp2l]).
Qed.

Lemma iedivnE m n : iedivn m n = (idivn m n, imodn m n).
Proof. by rewrite /idivn /imodn; case: (iedivn m n). Qed.

Lemma iedivnE' m n : m = imodn m n * n ^ idivn m n.
Proof.
  rewrite /imodn /idivn /iedivn /=.
  move: {2 4}m => d.
  elim: d m.
  - by move => m; rewrite /= expn0 muln1.
  - move => /= d IH m.
    rewrite edivn_def.
    case: (eqVneq (m %% n) 0).
    - move => H; rewrite H.
      move/eqP/divnK: H => {1}<-.
      rewrite {1}(IH (m %/ n)).
      case: (iedivn_rec _ _ _) => /= x y.
      by rewrite expnSr mulnA.
    - rewrite -lt0n.
      move/prednK => <- /=.
      by rewrite expn0 muln1.
Qed.

Lemma idiv0n n : idivn 0 n = 0.
Proof. done. Qed.

Lemma imod0n n : imodn 0 n = 0.
Proof. done. Qed.

Lemma idivn0 n : idivn n 0 = 0.
Proof. by case: n. Qed.

Lemma imodn0 n : imodn n 0 = n.
Proof. by case: n. Qed.

Lemma idiv1n n : 1 < n -> idivn 1 n = 0.
Proof. by rewrite /idivn /iedivn /= edivn_def; move: n => [] // []. Qed.

Lemma imod1n n : imodn 1 n = 1.
Proof. by rewrite /imodn /iedivn /= edivn_def; move: n => [] // []. Qed.

Lemma idivn1 n : idivn n 1 = n.
Proof.
  rewrite /idivn /iedivn.
  elim: {1 3}n => //= n'.
  rewrite edivn_def modn1 divn1 /=.
  by case: iedivn_rec => //= a _ ->.
Qed.

Lemma imodn1 n : imodn n 1 = n.
Proof.
  rewrite /imodn /iedivn.
  elim: {1}n => //= n'.
  rewrite edivn_def modn1 divn1 /=.
  by case: iedivn_rec.
Qed.

Lemma idivnn n : 0 < n -> idivn n n = 1.
Proof.
  by move: n => [] // [] // n; rewrite /idivn /iedivn /= !edivn_def modnn divnn.
Qed.

Lemma imodnn n : 0 < n -> imodn n n = 1.
Proof.
  by move: n => [] // [] // n; rewrite /imodn /iedivn /= !edivn_def modnn divnn.
Qed.

Lemma idivn_eq0 m n : 0 < m -> (idivn m n == 0) = ~~ (n %| m).
Proof.
  rewrite /idivn /iedivn /dvdn.
  case: m => //= m _.
  rewrite edivn_def.
  by case: (m.+1 %% n) => //; case: iedivn_rec.
Qed.

Lemma idivn_muln m n : 0 < m -> 1 < n -> idivn (n * m) n = (idivn m n).+1.
Proof.
  move => H H0.
  rewrite /idivn /iedivn (iedivn_recdepth (n * m) m.+1 (n * m) n) /=.
  - by rewrite edivn_def modnMr mulKn ?(ltnW H0) //; case: iedivn_rec.
  - by apply ltn_expl.
  - by rewrite expnS ltn_mul2l (ltnW H0) /=; apply ltn_expl.
  - by rewrite muln_gt0 H (ltnW H0).
Qed.

Lemma expn_idivnl m n : 1 < n -> idivn (n ^ m) n = m.
Proof.
  move => H.
  elim: m => //=.
  - by rewrite expn0 idiv1n.
  - by move => m IH; rewrite expnS idivn_muln // ?IH // expn_gt0 (ltnW H).
Qed.

Lemma expn_idivnr m n e : 1 < n -> 0 < e -> idivn m (n ^ e) = idivn m n %/ e.
Proof.
Admitted.

Lemma idivn_spec (m n r : nat) :
  0 < m -> 1 < n -> (idivn m n == r) = (n ^ r %| m) && ~~(n ^ r.+1 %| m).
Proof.
  elim: r m.
  - by move => m; rewrite expn0 expn1 dvd1n /= => H _; apply idivn_eq0.
  - move => r IH m H H0.
    rewrite 2!(expnS n).
    case: (eqVneq (n %| m) true).
    - move => H1.
      have H2: 0 < m %/ n by rewrite divn_gt0 ?(ltnW H0) // dvdn_leq.
      move/divnK: H1; rewrite mulnC => <-.
      rewrite idivn_muln // eqSS.
      do 2 rewrite dvdn_pmul2l ?(ltnW H0) //.
      by apply IH.
    - rewrite eq_sym negb_eqb /=; move => H1; apply negb_inj; move: H1.
      rewrite negb_and; do 2 rewrite -idivn_eq0 //.
      move/eqP => H1; rewrite H1 {1}/eq_op /=; apply/esym/orP; left.
      by rewrite -expnS expn_idivnr // H1 div0n.
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

Lemma binomial_sum m n : \sum_(n <= k < m) 'C(k, n) = 'C(m, n.+1).
Proof.
  elim: m n.
  - by move => n; rewrite big_nil bin0n.
  - move => m IH [].
    - by rewrite bin1 (eq_bigr _ (fun n _ => bin0 n))
                 big_const_nat subn0 iter_addn_0 mul1n.
    - move => n; case (leqP m n) => H.
      - rewrite /index_iota subSS bin_small //.
        by move/eqP: H => ->; rewrite big_nil.
      - by rewrite
          binS -!IH {1}/index_iota subSS -{1}add1n iota_addl big_map
          -/(index_iota n m) (eq_bigr (fun j => 'C(j, n.+1) + 'C(j, n))) //
          -(add0n (\sum_(n.+1 <= _ < m) _)) -{2}(bin_small (leqnn n.+1))
          -(big_cons 0 addn n (index_iota n.+1 m) xpredT) /index_iota
          -/(iota n (m - n.+1).+1) subnSK // -big_split /=.
Qed.

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
    - by move => H; apply dvdn_mull, dvdn_exp2l.
    - move: (nat_of_ord i) => {i} i H.
      rewrite -(subnK (ltnW H)) {1}expnD dvdn_pmul2r;
        last by rewrite expn_gt0 (ltnW (ltnW Hp)).
      move: (n - i) => {n H} n.
Abort.
