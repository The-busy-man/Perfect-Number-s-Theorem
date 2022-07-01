(*College Thesis of Raül Espejo Boix for Universitat Autònoma de Barcelona*)

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
    rewrite logn_gt0 mem_primes; apply/andP; split.
      by apply: pdiv_prime; rewrite ltnS.
    by (apply/andP; split); rewrite // pdiv_dvd.
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

Proposition gcdnM a b c: (a > 0) -> (coprime a b) ->
    gcdn (a*b) c = (gcdn a c)*(gcdn b c).
Proof.
  move => apos cprab.
  apply: (gcdn_def (dvdn_mul (dvdn_gcdl a c) (dvdn_gcdl b c))).
    rewrite Gauss_dvd. by rewrite (dvdn_gcdr a c) (dvdn_gcdr b c).
    by rewrite /coprime gcdnACA (eqP cprab) gcd1n.
  case cpos: (c > 0); last first. move: cpos; rewrite ltnNge => /negbFE.
    by rewrite leqn0 => /eqP ->; rewrite !gcdn0.
  apply: prime_decomp_ind => [| //| p k pprim| a' b' IHa IHb cprab' divab divc].
  - rewrite !dvd0n muln_eq0 => /orP [/eqP ->| /eqP ->] /eqP -> //.
    by rewrite mulnC.
  - case: k => [//| k kpos].
    move: (dvdn_exp2l p (ltn0Sn k)).
    rewrite expn1 => pdivp pkdivab.
    have H: forall a b, coprime a b ->
        p ^ k.+1 %| a * b -> p %| a -> p ^ k.+1 %| a.
      move => a' b' cprab' pkdivab' pdiva'. rewrite -(@Gauss_dvdl _ _ b') //.
      apply: coprimeXl; move: pdiva' => /dvdnP [q aisqp'].
      by move: cprab'; rewrite aisqp' coprimeMl => /andP /proj2.
    move: (Euclid_dvdM) (dvdn_trans pdivp pkdivab)
        => -> => [/orP [/(H a b cprab pkdivab) pdiva| pdivb] pdivc| //].
      by apply: dvdn_mulr; rewrite dvdn_gcd; apply/andP; split.
    apply: dvdn_mull; move: pdivb => /(H b a).
    rewrite coprime_sym mulnC => /(_ cprab pkdivab) pdivb.
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

Lemma div2_to_divPerm a b (apos: a > 0) (bpos: b > 0): coprime a b ->
    perm_eq
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

Lemma prime_div p k (kgt0: k > 0): prime p ->
    prime_decomp (p^k) = [:: (p, k)].
Proof.
  rewrite prime_decompE => primp.
  rewrite (primesX _ kgt0) (primes_prime primp) /=.
  by rewrite pfactorK.
Qed.

Lemma div_primeX p k: prime p ->
    divisors (p^k) = [seq p^i | i <- iota 0 k.+1].
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
    by apply (ltn_trans (ltnSn _)). rewrite /eq_mem => x.
  rewrite -dvdn_divisors; last by rewrite expn_gt0 prime_gt0.
  apply/dvdn_pfactor => //. case H: (x \in _).
    move: H => /mapP [z zinSSk xispz]; exists z => //.
    by rewrite mem_iota in zinSSk.
  move: H => /mapP H [z zleqk xispz].
  suff nH: exists2 n, n \in iota 0 k.+1 & x = p^n => //.
  by exists z => //; rewrite mem_iota.
Qed.

Definition multiplicative f := forall a b, (coprime a b) ->
    f (a*b) = (f a)*(f b).
Definition dirichlet_conv (f g: nat -> nat) n :=
    if n > 0 then \sum_(d <- divisors n) (f d)*(g (n%/d)) else 0.
  (* Definit al 0 com 0 per a mantenir les propietats desitjades*)

Definition sigma := dirichlet_conv (fun n => n) (fun n => 1).
Definition perfect p := sigma p = 2 * p.
Definition mersenne p := (prime p)/\(exists k, p = 2^k - 1).

Theorem dirichletM f g (f_cdt : multiplicative f) (g_cdt : multiplicative g) :
    (multiplicative (dirichlet_conv f g)).
Proof.
  rewrite /multiplicative /dirichlet_conv => a b cprab.
  case: a cprab => [| a cprab].
    by rewrite /coprime gcd0n mul0n /divisors => /eqP ->; rewrite mul0n.
  case: b cprab => [| b cprab].
    by rewrite /coprime gcdn0 muln0 /divisors => /eqP ->; rewrite muln0.
  rewrite (perm_big
      (map div_prod (allpairs pair (divisors a.+1) (divisors b.+1))));
    last (rewrite perm_sym; apply div2_to_divPerm => //=).
  rewrite muln_gt0 /= map_allpairs /div_prod big_allpairs_dep /=.
  rewrite (eq_big_seq (fun i1 => \sum_(i2 <- divisors b.+1)
      (f i1) * g (a.+1 %/ i1) * ((f i2) * (g (b.+1 %/ i2)))));
    last first. move => i; rewrite -(dvdn_divisors _ (ltn0Sn a)) => idiva.
    rewrite (eq_big_seq
      (fun i2 => f i * g (a.+1 %/ i) * (f i2 * g (b.+1 %/ i2)))) => //.
    move => j; rewrite -(dvdn_divisors _ (ltn0Sn b)) => jdivb.
    rewrite f_cdt.
      rewrite divnMA -divn_mulAC // -muln_divA // g_cdt.
        by rewrite mulnA [f i * f j * g (a.+1 %/ i)]mulnC
            mulnA [g (a.+1 %/ i) * f i]mulnC -mulnA.
      apply: (@proj1 _ (coprime i (b.+1%/j))). apply/andP.
      rewrite -coprimeMl divnK //.
      apply: (@proj1 _ (coprime a.+1 j)). apply/andP.
      by rewrite -coprimeMr divnK.
    apply: (@proj2 (coprime (a.+1%/i) j) _). apply/andP.
    rewrite -coprimeMl divnK //.
    apply: (@proj2 (coprime a.+1 (b.+1%/j)) _). apply/andP.
    by rewrite -coprimeMr divnK.
  by rewrite -big_distrlr.
Qed.

Theorem geoSum p n m: (p > 1) ->
    \sum_(i <- (iota m n)) p^i = (p^(m+n) - p^m)%/(p-1).
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

Proposition sigmaX p n: prime p -> n > 0 ->
    sigma (p^n) = (p^n.+1-1)%/(p-1).
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
  move => primp; rewrite -{1}[p]expn1 sigmaX //.
  by rewrite -{2}(exp1n 2) subn_sqr mulKn // subn_gt0 prime_gt1.
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
Proof.
  move => Ngt1.
  have Npos: N > 0. exact: (@ltn_trans 1).
  have divNp: N \in divisors N.
    by rewrite -dvdn_divisors.
  have div1p: 1 \in rem N (divisors N).
    apply: remK.
      by rewrite ltn_eqF.
    by rewrite -dvdn_divisors.
  rewrite /sigma /dirichlet_conv Npos /= (big_rem N) //= (big_rem 1) //=.
  by rewrite !muln1 !addnA -{1}[N+1]addn0 leq_add2l.
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
    apply: remK => //; move: dltp => /andP /proj2 /ltn_eqF.
    by rewrite eq_sym => /negP /negP.
  have _1dvdp2: 1 \in rem p (rem d (divisors p)).
    apply: remK => //. move: (dltp) => /andP /(and_ind (@ltn_trans d 1 p))
      /ltn_eqF. rewrite eq_sym => /negP /negP // _.
    by apply: remK => //; move: (dltp) => /andP /proj1 /ltn_eqF /negP /negP.
  move: sisp; rewrite (big_rem _ ddvdp) (big_rem _ pdvdp2) (big_rem _ _1dvdp2).
  rewrite ppos /= !muln1 [p+_]addnA [(p+1)+_]addnC addnA -{2}(add0n (p+1)).
  move/eqP; rewrite (eqn_add2r (p+1)) => sum0.
  move: (leq_addr (\sum_(y <- rem 1 (rem p (rem d (divisors p)))) y * 1) d).
  by rewrite (eqP sum0) leqn0 => /eqP dis0; rewrite dis0 in dltp.
Qed.

Proposition sigma_geqdvd2 p k l: p > 1 -> k!=1 -> p!=k ->
    (k)*(l) = p -> sigma p >= 1+k+p.
Proof.
  move => pgt1 kgt1 pneqk piskl; have ppos: p > 0.
    exact: (@ltn_trans 1).
  have kdivp: k \in divisors p.
    rewrite -dvdn_divisors //. apply/dvdnP.
    by apply: (ex_intro _ l); rewrite mulnC.
  have pdvip: p \in (rem k (divisors p)).
    by apply: remK; rewrite // -dvdn_divisors //; apply/dvdnP.
  have _1dvip: 1 \in rem p (rem k (divisors p)).
    apply: remK. apply/negPf; exact: ltn_eqF.
    apply: remK. rewrite eq_sym //.
    by rewrite -dvdn_divisors.
  rewrite /sigma /dirichlet_conv ppos.
  rewrite (big_rem k) //= (big_rem p) //= (big_rem 1) //= [1*1+_]addnC !muln1.
  by rewrite !addnA [_+1]addnC !addnA -{1}[_+_+_]addn0 leq_add2l.
Qed.

Theorem EuclidT p: prime (2^p-1) -> perfect (2^(p-1)*(2^p-1)).
Proof.
  case pisp: p => [|p'].
    by rewrite expn0 subnn; move /prime_gt0.
  rewrite /perfect => primp.
  rewrite sigmaM; last first.
    rewrite coprime_sym prime_coprime // Euclid_dvdX // negb_and.
    case: p' => [| p'] in primp pisp *; first by rewrite subnn.
    apply /orP; left; rewrite gtnNdvd //.
    rewrite -iter_predn expnS /= -ltnS prednK expnS mulnA.
      by rewrite -(muln1 4) {3}/muln /= leq_pmul2l // expn_gt0.
    by rewrite -{1}(muln0 4) {3}/muln /= (ltn_mul2l 4) /= expn_gt0.
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
  have nPpos: 0 < n.-1.
    by rewrite /n succnK -pfactor_dvdn.
  apply: (ex_intro _ n); move: (cpr2m) (cpr2m).
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
  move: H => /dvdnP [q sisq]. move: (perp2).
  rewrite [_*m]mulnC sisq mulnA => /eqP; rewrite eqn_pmul2r ?expn_gt0 //.
  move => /eqP perp3.
  case qis1: (q == 1).
    rewrite (eqP qis1) muln1 in perp3.
    rewrite (eqP qis1) mul1n /s -[_^n](@subnK 1) ?expn_gt0 // perp3 in sisq.
    move: (pfac); rewrite -perp3 mulnC => pfac2; split => //.
    by apply: sigmapS => //; rewrite perp3.
  move: qis1 => /negP /negP qis1.
  have mgt1: m > 1.
    case H: m => [|m']. by rewrite H in mpos.
    case H2: m' => [|//].
    rewrite H2 in H; rewrite H mulnC in perp3; move: perp3 nPpos => /eqP.
    rewrite eq_sym => /eqP /(ex_intro (fun k => 1 = k*_) _) /dvdnP.
    rewrite dvdn1 => /eqP; rewrite subn1.
    move /(f_equal succn); rewrite prednK.
      by rewrite -{2}(expn1 2) => /eqP; rewrite eqn_exp2l // => /eqP ->.
    exact: expn_gt0.
  have misnq: m != q.
    case H: (m == q) => [|//]; move: H perp3 nPpos => /eqP H /eqP.
    rewrite -H -{2}[m]mul1n eqn_pmul2r // => /eqP.
    rewrite subn1; move /(f_equal succn); rewrite prednK.
      by rewrite -{2}(expn1 2) => /eqP; rewrite eqn_exp2l // => /eqP ->.
    exact: expn_gt0.
  rewrite mulnC in perp3.
  move: (sigma_geqdvd2 mgt1 qis1 misnq perp3) => H.
  have /(leq_trans H): sigma m <= q+m.
    rewrite -/s sisq -{1}perp3 -{2}(muln1 q).
    by rewrite -mulnDr addnC subn1 addn1 prednK ?leqnn ?expn_gt0.
  by rewrite -[q+_]add0n addnA !leq_add2r.
Qed.