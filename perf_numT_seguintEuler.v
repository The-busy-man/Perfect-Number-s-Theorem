From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma prime_decomp_ind (P: nat -> Prop) (P0: P 0) (P1: P 1)
      (Pprime: forall p k, prime p -> k > 0 -> P (p^k))
      (Pmul: forall a b, P a -> P b -> coprime a b -> (P (a*b))) c: P c.
Proof.
  apply: (nat_ind (fun n => forall m, m <= n -> P m) _ _ c c (leqnn c))
       => [n | n IHn m mleqn]. by rewrite leqn0 => /eqP ->.
  case H: (m <= n). exact: (IHn _ H).
  move: H; rewrite leqNgt => /negbFE /(conj mleqn) /andP.
  rewrite -eqn_leq => /eqP ->.
  case: n m mleqn IHn => [//| n _ _ IHn].
  have ngt1: 1 < n.+2 by rewrite ltnS.
  have npos: 0 < n.+2 by [].
  have logpos: (0 < logn (pdiv n.+2) n.+2).
    rewrite logn_gt0 mem_primes; apply/andP; split; last (apply/andP; split) => //.
      by apply: pdiv_prime; rewrite ltnS.
    by rewrite pdiv_dvd.
  move: (pdiv_prime ngt1) => prdvd.
  move: (pfactor_coprime (pdiv_prime ngt1) npos) => [m cprnm npart].
  rewrite npart; apply: Pmul.
  - case H: (m > 0); last first.
      by move: H; rewrite ltnNge => /negbFE; rewrite leqn0 => /eqP ->.
    case H2: (m < n.+2).
      by rewrite ltnS in H2; apply: (IHn _ H2).
    move: H2; rewrite ltnNge /negbFE.
    rewrite npart -{2}(muln1 m) (leq_pmul2l H) -(exp1n (logn (pdiv n.+2) n.+2)).
    rewrite (leq_exp2r _ _ logpos) leqNgt.
    by move: prdvd => /prime_gt1 ->.
  - by apply: (Pprime _ _ prdvd); rewrite logn_gt0 pi_pdiv.
  by apply: coprimeXr; rewrite coprime_sym.
Qed.

Proposition gcdnM a b c: (a > 0) -> (coprime a b) -> gcdn (a*b) c = (gcdn a c)*(gcdn b c).
Proof.
  move => apos cprab.
  apply: (gcdn_def (dvdn_mul (dvdn_gcdl a c) (dvdn_gcdl b c))).
    rewrite Gauss_dvd. by rewrite (dvdn_gcdr a c) (dvdn_gcdr b c).
    by rewrite /coprime gcdnACA (eqP cprab) gcd1n.
  case cpos: (c > 0); last first.
    by move: cpos; rewrite ltnNge => /negbFE; rewrite leqn0 => /eqP ->; rewrite !gcdn0.
  apply: prime_decomp_ind => [| //| p k pprim| a' b' IHa IHb cprab' divab divc].
  - rewrite !dvd0n muln_eq0 => /orP [/eqP ->| /eqP ->] /eqP -> //.
    by rewrite mulnC.
  - case: k => [//| k kpos].
    move: (dvdn_exp2l p (ltn0Sn k)).
    rewrite expn1 => pdivp pkdivab.
    have H: forall a b, coprime a b -> p ^ k.+1 %| a * b -> p %| a -> p ^ k.+1 %| a.
      move => a' b' cprab' pkdivab' pdiva'. rewrite -(@Gauss_dvdl _ _ b') //.
      apply: coprimeXl; move: pdiva' => /dvdnP [q aisqp'].
      by move: cprab'; rewrite aisqp' coprimeMl => /andP /proj2.
    move: (Euclid_dvdM) (dvdn_trans pdivp pkdivab)
        => -> => [/orP [/(H a b cprab pkdivab) pdiva| pdivb] pdivc| //].
      by apply: dvdn_mulr; rewrite dvdn_gcd; apply/andP; split.
    apply: dvdn_mull.
    move: pdivb => /(H b a); rewrite coprime_sym mulnC => /(_ cprab pkdivab) pdivb.
    by rewrite dvdn_gcd; apply/andP; split.
  rewrite Gauss_dvd // (IHa (dvdn_trans (dvdn_mulr _ _) divab)
                            (dvdn_trans (dvdn_mulr _ _) divc)) //.
  by rewrite (IHb (dvdn_trans (dvdn_mull _ _) divab)
                  (dvdn_trans (dvdn_mull _ _) divc)).
Qed.

Lemma div_gcdnE a b c (apos: a > 0): (coprime a b) ->
                      reflect (c = (gcdn a c)*(gcdn b c)) (c %| a*b).
Proof.
  move => cprab; apply: Coq.Bool.Bool.iff_reflect.
  split. move => ->.
    exact: dvdn_mul (dvdn_gcdl a c) (dvdn_gcdl b c).
  move /gcdn_idPl => {1}<-; rewrite gcdnC.
  exact: gcdnM.
Qed.

Definition div_pair a b d:= (gcdn a d, gcdn b d).
Definition div_prod (d: nat*nat):= d.1*d.2.

Lemma div2_to_div a b (apos: a > 0) (bpos: b > 0): coprime a b ->
  map div_prod (allpairs pair (divisors a) (divisors b)) =i
  divisors (a*b).
Proof.
  rewrite map_allpairs /eq_mem => cprab x.
  case H: (x \in _).
    apply/eqP. rewrite eq_sym; apply/eqP.
    move: H => /allpairsP [z [zdiva zdivb xisc]].
    rewrite xisc /div_prod /=.
    rewrite -dvdn_divisors in zdiva => //.
    rewrite -dvdn_divisors in zdivb => //.
    rewrite -dvdn_divisors; last first.
      by rewrite -(muln0 0) (ltn_mul apos bpos).
    by rewrite dvdn_mul.
  rewrite -dvdn_divisors; last first.
    by rewrite -(muln0 0) (ltn_mul apos bpos).
  apply/eqP. rewrite eq_sym; apply/eqP.
  apply /(div_gcdnE x apos cprab)/eqP.
  case H2: (x == _) => //.
  move: H2 H => /eqP H2 /negP.
  apply: absurd.
  apply/allpairsP/(ex_intro _ (gcdn a x, gcdn b x)) => /=; split.
  - rewrite -dvdn_divisors //; exact: dvdn_gcdl.
  - rewrite -dvdn_divisors //; exact: dvdn_gcdl.
  by rewrite /div_prod /=.
Qed.

Lemma cpr_divl a b c: c%|a -> (coprime a b) -> (coprime c b).
Proof.
  move => /dvdnP [k cdiva].
  by rewrite cdiva coprimeMl => /andP [_].
Qed.

Lemma cpr_divr a b c: c%|b -> (coprime a b) -> (coprime a c).
Proof.
  move => /dvdnP [k cdivb].
  by rewrite cdivb coprimeMr => /andP [_].
Qed.

Lemma cpr_mult_projl a b c d: (coprime a d) -> (coprime b c) ->
                             a*b = c*d -> b = d.
Proof.
  move: a b c d.
  suff H: forall a b c d, (coprime a d) -> (coprime b c) ->
                          a*b = c*d -> b %| d.
    move => a b c d cprac cprbd eqmult .
    apply: eqP; rewrite eqn_dvd; apply/andP; split.
      exact: (H a b c d).
    by apply: (H c d a b); (rewrite coprime_sym)||symmetry.
  move => a b c d cprac cprbd eqmult. symmetry in eqmult.
  move/dvdnP: (ex_intro (fun k => c*d = k*b) _ eqmult).
  by rewrite Gauss_dvdr.
Qed.

Lemma cpr_mult_projr a b c d: (coprime a d) -> (coprime b c) ->
                             a*b = c*d -> a = c.
Proof.
  move => cprad cprbc.
  by rewrite mulnC [RHS]mulnC; apply: cpr_mult_projl.
Qed.

Lemma div2_to_divPerm a b (apos: a > 0) (bpos: b > 0): coprime a b -> perm_eq
  (map div_prod (allpairs pair (divisors a) (divisors b)))
  (divisors (a*b)).
Proof.
  move => cprab; apply: uniq_perm; last first.
  - exact: div2_to_div.
  - exact: divisors_uniq.
  rewrite /div_prod /allpairs map_allpairs => /=.
  apply: allpairs_uniq; repeat exact: divisors_uniq.
  move => /= x y /allpairsPdep [x0 [x1 [x0diva x1divb xx]]].
  move => /allpairsPdep [y0 [y1 [y0diva y1divb yy]]].
  rewrite xx yy => /=.
  move: (dvdn_divisors) (x0diva) => <- // x0diva'.
  move: (dvdn_divisors) (x1divb) => <- // x1divb'.
  move: (dvdn_divisors) (y0diva) => <- // y0diva'.
  move: (dvdn_divisors) (y1divb) => <- // y1divb'.
  move: (cpr_divr y1divb' (cpr_divl x0diva' cprab)) => cprx0y1.
  move: (cpr_divr x1divb' (cpr_divl y0diva' cprab)) => cpry1x0.
  move => eqmult; apply pair_equal_spec; split.
    apply (@cpr_mult_projr x0 x1 y0 y1) => //.
    by rewrite coprime_sym.
  apply (@cpr_mult_projl x0 x1 y0 y1) => //.
  by rewrite coprime_sym.
Qed.

Lemma prime_div p k (kgt0: k > 0): prime p -> prime_decomp (p^k) = [:: (p, k)].
Proof.
  rewrite prime_decompE => primp.
  rewrite (primesX _ kgt0) (primes_prime primp) /=.
  by rewrite pfactorK.
Qed.

Lemma div_primeX p k: prime p -> divisors (p^k) = [seq p^i | i <- iota 0 k.+1].
Proof.
  move => prp.
  apply: (irr_sorted_eq_in (leT := ltn)) => //.
  - move => x1 x2 x3 _ _ _; apply: ltn_trans.
  - move => x1 _; apply: ltnn.
  - apply sorted_divisors_ltn.
  - rewrite sorted_map /relpre /=; apply/(pathP 0) => i iinSk/=.
    rewrite (ltn_exp2l _ _ (prime_gt1 _)) //=.
    move: iinSk; case: i => [| i].
      rewrite /= nth0. by case: k.
    rewrite size_iota => iinSk; repeat (rewrite nth_iota //=).
    by apply (ltn_trans (ltnSn _)).
  rewrite /eq_mem => x; rewrite -dvdn_divisors; last by rewrite expn_gt0 prime_gt0.
  apply/dvdn_pfactor => //. case H: (x \in _).
    move: H => /mapP [z zinSSk xispz]; exists z => //.
    by rewrite mem_iota in zinSSk.
  move: H => /mapP H [z zleqk xispz].
  suff nH: exists2 n, n \in iota 0 k.+1 & x = p^n => //.
  by exists z => //; rewrite mem_iota.
Qed.

Definition multiplicative f := forall a b, (coprime a b) -> f (a*b) = (f a)*(f b).
Definition dirichlet_conv (f g: nat -> nat) n :=
  if n > 0 then \sum_ (d <- divisors n) (f d)*(g (n%/d)) else 0.
  (* Definit al 0 com 0 per a mantenir les propietats desitjades*)

Definition sigma := dirichlet_conv (fun n => n) (fun n => 1).
Definition perfect p := sigma p = 2 * p.
Definition mersenne p := (prime p)/\(exists k, p = 2^k - 1).

Definition divisors_n1 p := behead (divisors p).
Definition divisors_n1p p := behead (belast 0 (divisors_n1 p)).

Theorem dirichletM f g (f_cdt : multiplicative f) (g_cdt : multiplicative g) :
  (multiplicative (dirichlet_conv f g)).
Proof.
  rewrite /multiplicative /dirichlet_conv => a b cprab.
  case: a cprab => [| a cprab].
    by rewrite /coprime gcd0n mul0n /divisors => /eqP ->; rewrite mul0n.
  case: b cprab => [| b cprab].
    by rewrite /coprime gcdn0 muln0 /divisors => /eqP ->; rewrite muln0.
  rewrite (perm_big (map div_prod (allpairs pair (divisors a.+1) (divisors b.+1))));
    last (rewrite perm_sym; apply div2_to_divPerm => //=).
  rewrite muln_gt0 /=.
  rewrite map_allpairs /div_prod big_allpairs_dep /=.
  rewrite (eq_big_seq (fun i1 =>
    \sum_(i2 <- divisors b.+1) (f i1) * g (a.+1 %/ i1) * ((f i2) * (g (b.+1 %/ i2)))));
    last first. move => i; rewrite -(dvdn_divisors _ (ltn0Sn a)) => idiva.
    rewrite (eq_big_seq (fun i2 => f i * g (a.+1 %/ i) * (f i2 * g (b.+1 %/ i2)))) => //;
    last first. move => j; rewrite -(dvdn_divisors _ (ltn0Sn b)) => jdivb.
    rewrite f_cdt.
      rewrite divnMA -divn_mulAC //.
      rewrite -muln_divA //.
      rewrite g_cdt.
        by rewrite mulnA [f i * f j * g (a.+1 %/ i)]mulnC
                     mulnA [g (a.+1 %/ i) * f i]mulnC -mulnA.
      apply: (@proj1 _ (coprime i (b.+1%/j))); apply/andP; rewrite -coprimeMl divnK //.
      apply: (@proj1 _ (coprime a.+1 j)); apply/andP; rewrite -coprimeMr divnK => //.
    apply: (@proj2 (coprime (a.+1%/i) j) _); apply/andP; rewrite -coprimeMl divnK //.
    apply: (@proj2 (coprime a.+1 (b.+1%/j)) _); apply/andP; rewrite -coprimeMr divnK => //.
  by rewrite -big_distrlr.
Qed.

Theorem geoSum p n m: (p > 1) -> \sum_(i <- (iota m n)) p^i = (p^(m+n) - p^m)%/(p-1).
Proof.
  elim: n m => [m| n' IHn m pgt1].
    by rewrite unlock addn0 subnn div0n /=.
  rewrite /= big_cons IHn // -{1}(@mulnK (p^m) (p-1)).
    rewrite -divnDl; last by (apply dvdn_mull; rewrite dvdnn).
    rewrite mulnBr {1}mulnC -expnS muln1 addnBAC.
      rewrite subnKC addSnnS //.
      by rewrite leq_exp2l // -addSnnS ltn_addr.
    by rewrite leq_exp2l.
  by rewrite subn_gt0.
Qed.

Corollary sigmaM: multiplicative sigma.
Proof.
  rewrite /multiplicative /sigma => a b cprab.
  by rewrite dirichletM.
Qed.

Proposition sigmaX p n: prime p -> n > 0 -> sigma (p^n) = (p^n.+1-1)%/(p-1).
Proof.
  move => primp npos.
  rewrite /sigma /dirichlet_conv.
  have ineq: 0 < p ^ n.
    rewrite expn_gt0; apply/orP; left; exact: prime_gt0.
  rewrite ineq /= div_primeX // big_map (eq_bigr (fun i => p^i)); last first.
    by move => i; rewrite muln1.
  by rewrite geoSum // prime_gt1.
Qed.

Corollary sigmaX1 p: prime p -> sigma p = p+1.
Proof.
  move => primp.
  by rewrite -{1}[p]expn1 sigmaX // -{2}(exp1n 2) subn_sqr mulKn // subn_gt0 prime_gt1.
Qed.

Lemma remK (T: eqType) (x y: T) s: y != x -> y \in s -> y \in rem x s.
Proof.
  elim H: s => [//| z s' IHs].
  move => ynotx yins; rewrite rem_cons.
  case zisx: (z == x).
    move: yins; rewrite in_cons => /orP [yisz | //].
    by rewrite (eqP yisz) -(eqP zisx) eq_refl in ynotx *.
  move: yins; rewrite !in_cons => /orP [|] yisz; apply/orP; first by left.
  by right; apply: IHs.
Qed.

Proposition sigma_geqn N: N > 1 -> sigma N >= N+1.
  move => Ngt1.
  have Npos: N > 0. exact: (@ltn_trans 1).
  have divNp: N \in divisors N.
    by rewrite -dvdn_divisors.
  have div1p: 1 \in rem N (divisors N).
    apply: remK.
      by rewrite ltn_eqF.
    by rewrite -dvdn_divisors.
  rewrite /sigma /dirichlet_conv Npos /= (big_rem N) //= (big_rem 1) //= !muln1.
  by rewrite !addnA -{1}[N+1]addn0 leq_add2l.
Qed.

Proposition sigmapS p: sigma p = p+1 -> prime p.
Proof.
  rewrite /sigma /dirichlet_conv; move => sisp.
  case H: (prime p) => //.
  move: H => /primePn [plt2| [d dltp ddvdp]].
    case: p sisp plt2 => [sisp _| p sisp plt2].
      by rewrite unlock /= in sisp.
    case: p sisp plt2 => [sisp _| //].
    by rewrite unlock /= in sisp.
  have ppos: p > 0.
    rewrite (@ltn_trans 1) // (@ltn_trans d) //; move: dltp => /andP.
    exact: proj1. exact: proj2.
  rewrite dvdn_divisors // in ddvdp.
  move: (dvdnn p); rewrite dvdn_divisors // => pdvdp.
  move: (dvd1n p); rewrite dvdn_divisors // => _1dvdp.
  have pdvdp2: p \in rem d (divisors p).
    by apply: remK => //; move: dltp => /andP /proj2 /ltn_eqF; rewrite eq_sym => /negP /negP.
  have _1dvdp2: 1 \in rem p (rem d (divisors p)).
    apply: remK => //; move: (dltp) => /andP /(and_ind (@ltn_trans d 1 p)) /ltn_eqF;
      rewrite eq_sym => /negP /negP // _.
    by apply: remK => //; move: (dltp) => /andP /proj1 /ltn_eqF /negP /negP.
  move: sisp; rewrite (big_rem _ ddvdp) (big_rem _ pdvdp2) (big_rem _ _1dvdp2) ppos /=.
  rewrite !muln1 [p+_]addnA [(p+1)+_]addnC addnA -{2}(add0n (p+1)) => /eqP.
  rewrite (eqn_add2r (p+1)) => sum0.
  move: (leq_addr (\sum_(y <- rem 1 (rem p (rem d (divisors p)))) y * 1) d).
  by rewrite (eqP sum0) leqn0 => /eqP dis0; rewrite dis0 in dltp.
Qed.

Proposition sigma_geqdvd p k l: p > 1 -> 1!=l -> 1!=k -> l!=k ->
                                (k)*(l) = p -> sigma p >= 1+k+l+p.
Proof.
  move => pgt1; have ppos: p > 0.
    apply: (@ltn_trans 1) => //.
  move => lisn1 kisn1 kisnl klisp.
  have kdivp: k \in divisors p.
    by rewrite -dvdn_divisors //; apply/dvdnP; apply: (ex_intro _ l); rewrite mulnC.
  have ldivp: l \in rem k (divisors p).
    by apply: remK => //; rewrite -dvdn_divisors //; apply/dvdnP; apply: (ex_intro _ k).
  have pdvip: p \in rem l (rem k (divisors p)).
    apply: remK.
      case lisp: (p != l) => //; move: lisp (klisp) => /negP /negP /eqP ->.
      rewrite -{2}(mul1n l) => /eqP; rewrite eqn_pmul2r.
        by move => /eqP kis1; rewrite kis1 in kisn1.
      case H: (0 < l) => [//|].
      move: H klisp ppos => /negP /negP; rewrite -eqn0Ngt => /eqP ->.
      by rewrite muln0 => ->; rewrite ltnn.
    apply: remK.
      case kisp: (p != k) => //; move: kisp (klisp) => /negP /negP /eqP ->.
      rewrite -{2}(muln1 k) => /eqP; rewrite eqn_pmul2l.
        by move => /eqP lis1; rewrite lis1 in lisn1.
      case H: (0 < k) => [//|].
      move: H klisp ppos => /negP /negP; rewrite -eqn0Ngt => /eqP ->.
      by rewrite mul0n => ->; rewrite ltnn.
    by rewrite -dvdn_divisors //.
  have _1dvip: 1 \in rem p (rem l (rem k (divisors p))).
    apply: remK. apply/negPf; apply: ltn_eqF => //.
    apply: remK => //. apply remK => //.
    by rewrite -dvdn_divisors //.
  rewrite /sigma /dirichlet_conv ppos.
  rewrite (big_rem k) //= (big_rem l) //= (big_rem p) //= (big_rem 1) //=.
  rewrite !muln1 !addnA -[_+l]addnA -[_+p]addnA [1+_]addnC -{1}[_+_+_+_]addn0 leq_add2l //.
Qed.

Lemma arith_leqgeo x y: x > 1 -> y > 1 -> x+y <= x*y.
Proof.
  move => leq1x leq0y; rewrite -(@leq_subRL x).
    rewrite (@leq_trans (2*y-2)) //; last first.
      by rewrite -{2}(muln1 x) -{2}(muln1 2) -!mulnBr leq_pmul2r // subn_gt0.
    rewrite (@leq_subRL 2); last first.
      by rewrite (@ltn_trans y) // -{1}(mul1n y) ltn_pmul2r // (@ltn_trans 1).
    rewrite addnC -(@leq_subRL y); last first.
      by rewrite (@leq_trans y) // -{1}(mul1n y) leq_pmul2r // (@ltn_trans 1).
    by rewrite -{2}(mul1n y) -mulnBl /subn /= mul1n.
  by rewrite -{1}(muln1 x) leq_pmul2l // (@ltn_trans 1).
Qed.

Proposition cpr_primesM x y: coprime x y -> (perm_eq (primes (x*y)) ((primes x)++(primes y))).
Proof.
  case xisx: x => [|x'].
    by rewrite /coprime gcd0n => /eqP ->.
  case yisy: y => [|y'].
    by rewrite /coprime gcdn0 => /eqP ->.
  move => cprxy.
  apply: uniq_perm.
  - by rewrite primes_uniq.
  - rewrite cat_uniq ?primes_uniq; apply/andP; split => //; apply/andP; split => //.
    rewrite -coprime_has_primes //.
  by rewrite /eq_mem => n; rewrite primesM // mem_cat.
Qed.

Proposition pdecompM x y: coprime x y ->
  (perm_eq (prime_decomp (x*y)) ((prime_decomp x) ++ (prime_decomp y))).
Proof.
  move => cprxy; rewrite !prime_decompE.
  suff H: [seq (p, logn p x) | p <- primes x] = [seq (p, logn p (x*y)) | p <- primes x].
    suff H2: [seq (p, logn p y) | p <- primes y] = [seq (p, logn p (x*y)) | p <- primes y].
      by rewrite H H2 -map_cat perm_map // cpr_primesM.
    apply eq_in_map; rewrite /eqfun => n nprx; rewrite logn_Gauss // coprime_sym.
    move: nprx; rewrite mem_primes => /andP [primn /andP [ypos ndivy]].
    by rewrite (@coprime_dvdr n y x).
  apply eq_in_map; rewrite /eqfun => n npry; rewrite mulnC logn_Gauss //.
  move: npry; rewrite mem_primes => /andP [primn /andP [ypos ndivy]].
  by rewrite (@coprime_dvdl n x y).
Qed.

Lemma sigma_pdecomp1 N: N > 0 -> sigma N =
  \prod_(n <- prime_decomp N) (\sum_(i <- (iota 0 n.2.+1)) n.1^i).
Proof.
  move: N; apply: prime_decomp_ind =>
        [//| _| p m primp mpos ppos| x y IHx IHy cprxy xypos].
  - by rewrite /sigma /dirichlet_conv unlock /=.
  - rewrite sigmaX // prime_div // (lock iota) {1}unlock /= muln1; unlock locked.
    by rewrite geoSum ?prime_gt1 //.
  move: xypos; rewrite muln_gt0 => /andP [xpos ypos]; rewrite sigmaM //.
    (*Semblen haver-hi molts pocs resultats de prime_decomp a mathcomp*)
  rewrite IHx // IHy //.
  rewrite [\prod_(n <- prime_decomp (x * y)) (\sum_(i <- iota 0 n.2.+1) n.1 ^ i)]
          (perm_big ((prime_decomp x) ++ (prime_decomp y))). by rewrite big_cat /=.
  by apply pdecompM.
Qed.

Lemma sigma_sqr N: sigma (N*N) >= N*(sigma N).
Proof.
  case H: N => [| N']; first by rewrite mul0n /sigma /dirichlet_conv.
  have pdecomp2: forall n, prime_decomp (n*n) = [seq (p.1, 2*(p.2))| p <- (prime_decomp n)].
    move => n; rewrite !prime_decompE -map_comp /comp /= mulnn primesX //.
    by apply eq_in_map => [x xprimn]; rewrite lognX.
  rewrite (@sigma_pdecomp1 (N'.+1*N'.+1)) // pdecomp2 big_seq.
  rewrite (eq_bigr (fun n => (\sum_(i <- iota 0 (n.2%/2)) n.1 ^ i)+(\sum_(i <- iota (n.2%/2) (n.2%/2).+1) n.1 ^ i))); last first.
    move => n /mapP [x xprimN xisn].
    rewrite (f_equal snd xisn) mulKn // -(big_cat) -iotaD (lock iota).
    by rewrite mul2n -addnn addnS.
  apply: (@leq_trans (\prod_(i <- [seq (p.1, 2 * p.2) | p <- prime_decomp N'.+1] | i \in [seq (p.1, 2 * p.2) | p <- prime_decomp N'.+1]) (i.1^(i.2%/2)*\sum_(i0 <- iota 0 (i.2 %/ 2).+1) i.1 ^ i0))).
    rewrite big_split (lock iota) /= -!big_seq. rewrite !big_map.
    rewrite (eq_bigr (fun n => n.1^n.2)).
      rewrite [\prod_(j <- prime_decomp N'.+1) (\sum_(i0 <- locked iota 0 ((j.1, 2 * j.2).2 %/ 2).+1) (j.1, 2 * j.2).1 ^ i0)]
            (eq_bigr (fun n => \sum_(i0 <- locked iota 0 (n.2.+1)) n.1 ^ i0)). unlock locked.
      by rewrite {1}(@prod_prime_decomp N'.+1) // sigma_pdecomp1.
      by move => n _; unlock locked; apply: congr_big => //; rewrite /= mulKn.
    by move => n _; rewrite /= mulKn.
  rewrite (big_ind2 leq) //. by move => a b c d aleqb cleqd; rewrite leq_mul.
  move => n /mapP [x xprimN xisn].
  rewrite (lock iota) !xisn mulKn //= -(add0n (_ ^ _ * _)) leq_add //. unlock locked.
  rewrite -{3}(add0n x.2) addnC iotaDl big_map
              [\sum_(j <- iota 0 x.2.+1) x.1 ^ (x.2 + j)](eq_bigr (fun j => x.1^x.2*x.1^j)).
    by rewrite -big_distrr.
  by move => i _; rewrite expnD.
Qed.

Theorem EuclidT p: prime (2^p-1) -> perfect (2^(p-1)*(2^p-1)).
Proof.
  case pisp: p => [|p'].
    by rewrite expn0 subnn; move /prime_gt0.
  rewrite /perfect => primp.
  rewrite sigmaM; last first.
    rewrite coprime_sym prime_coprime // Euclid_dvdX //.
    rewrite negb_and.
    case: p' => [| p'] in primp pisp *; first by rewrite subnn.
    apply /orP; left; rewrite gtnNdvd //.
    rewrite -iter_predn expnS /= -ltnS prednK expnS mulnA.
      rewrite -(muln1 4) {3}/muln /= leq_pmul2l // expn_gt0 //.
    by rewrite -{1}(muln0 4) {3}/muln /= (ltn_mul2l 4) /= expn_gt0 //.
  rewrite (@sigmaX1 (2 ^ p'.+1 - 1)) // sigmaX //=; last first.
    rewrite subn_gt0 ltnS; case H: (0 < p') => [//| ].
    move/negP: H => /negP; rewrite -eqn0Ngt => /eqP H.
    by rewrite H expn1 subn1 /= in primp; move: (prime_gt1 primp).
  rewrite !subn1 !addn1 divn1 !prednK //=; last by rewrite expn_gt0.
  by rewrite {2}expnS mulnC mulnA.
Qed.

(*Leonard Eugene Dickson, History of the theory of numbers. Vol I page 19*)
Theorem EulerT p: perfect p -> 2%|p -> p > 0 ->
                  exists n, (p = (2^n-1)*2^n.-1)/\(prime (2^n - 1)).
Proof.
  rewrite /perfect => perp peven ppos. have: prime 2 => //.
  move /(@pfactor_coprime 2 p) /(_ ppos) => [m cpr2m pfac].
  set n := (logn 2 p).+1.
  set s := sigma m.
  have mpos: m > 0.
    case H: m => [| //].
    by rewrite pfac H mul0n in ppos.
  apply: (ex_intro _ n); move: (cpr2m) (cpr2m).
  have nPpos: 0 < n.-1.
    by rewrite /n succnK -pfactor_dvdn.
  rewrite -(@coprime_pexpl n.-1) // => cpr2nPm.
  rewrite -(@coprime_pexpl n) // => cpr2nm.
  rewrite -[logn _ _]succnK mulnC -/n in pfac.
  move: (perp); rewrite pfac sigmaM // sigmaX // => perp2.
  rewrite prednK ?subn1 //= divn1 -subn1 -/s mulnA -expnS -/n in perp2.
  have /dvdnP H: exists k, (2 ^ n - 1) * s = k * 2^n.
    by apply: (ex_intro _ m); rewrite [m*_]mulnC.
  rewrite Gauss_dvdr // in H; last first.
    rewrite coprime_pexpl // prime_coprime //; apply/negP.
    by rewrite (@dvdn_subr 2 _ 1) // ?expn_gt0 // -{1}(expn1 2) dvdn_exp2l.
  move: H => /dvdnP [q sisq].
  move: (perp2); rewrite [_*m]mulnC sisq mulnA => /eqP; rewrite eqn_pmul2r;
    last by rewrite expn_gt0.
  move => /eqP perp3.
  case qis1: (q == 1).
    rewrite (eqP qis1) muln1 in perp3.
    rewrite (eqP qis1) mul1n /s -[_^n](@subnK 1) ?expn_gt0 // perp3 in sisq.
    move: (pfac); rewrite -perp3 mulnC => pfac2; split => //.
    by apply: sigmapS => //; rewrite perp3.
  suff sgeqsum: s >= 1 + (2^n-1) + q + m.
    move: sgeqsum mpos;
    rewrite -perp3 -{1}[q]mul1n -addnA -mulnDl !addnABC ?expn_gt0 // subnn add0n.
    by rewrite mulnC -(add0n s) sisq leq_add2r leqn0 => /eqP ->; rewrite sub0n mul0n.
  rewrite /s sigma_geqdvd //.
  - case _1ltm: (1 < m) => //; move: _1ltm => /negP /negP; rewrite -leqNgt.
    rewrite leq_eqVlt => /orP [/eqP mis1|].
      by move: perp3 => /eqP; rewrite mis1 muln_eq1 => /andP /proj2; rewrite qis1.
    by rewrite ltnS leqn0 => /eqP => mis0; rewrite mis0 in mpos.
  - by move: qis1; rewrite eq_sym => /negP/negP.
  - case _1is2n: (1 == 2^n - 1) => //=; move: _1is2n.
    rewrite subn1 -eqSS prednK ?expn_gt0 // -{1}(expn1 2) eqn_exp2l // => /eqP eq1n.
    by rewrite -eq1n expn0 mul1n in pfac; rewrite -pfac prime_coprime ?peven in cpr2m.
  case qis2n: (q == 2^n-1) => //=.
         (*A la demo original l'hi faltava demostrar aquesta part*)
  move/eqP in qis2n. move: sisq; rewrite /s -perp3 !qis2n => nH.
  have lt12n: 1 < 2^n-1.
    by rewrite ltn_subRL addn1 -{1}(expn1 2) ltn_exp2l.
  move: (sigma_sqr (2 ^ n - 1)); rewrite nH leq_pmul2l; last exact: (@ltn_trans 1).
  move => nH2; case H: (n <= 1) => //; move: H.
    case H2: (n > 0) => // /(conj H2) /andP; rewrite -eqn_leq => /eqP => H.
    rewrite -H /sigma /dirichlet_conv unlock /= in nH.
    by rewrite expn1 muln1 addn0 subn1 /= mul1n in nH.
  move: (sigma_geqn lt12n) => nH3.
  move: (conj (leq_trans nH2 (leqSpred (2^n))) nH3).
  rewrite -subn1 -[(_-_).+1]addn1 => /andP; rewrite -eqn_leq => /eqP /sigmapS nH4.
  move: nH; rewrite mulnn sigmaX // -[3]addn1 -{5}(expn0 (2^n-1)) -geoSum //.
  rewrite unlock /= expnS expnS expn0 addn0 mulnBr mulnBl mul1n muln1 addnABC //.
    rewrite subnn add0n -{2}[(2 ^ n - 1) * 2 ^ n](add0n) => /eqP.
    by rewrite eqn_add2r.
  rewrite -{1}(muln1 (2^n-1)) leq_pmul2l ?expn_gt0 //; exact: (@ltn_trans 1).
Qed.
