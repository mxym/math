# Exact common-cofactor forks with opposite ordinary parity at small-radical targets

Fix \(B>0\), \(J=[\alpha,\beta]\subset(0,1)\) with \(\alpha<\beta\), and \(I=PJ\), \(L=\log P\). Suppose the **individual even target** \(P\) satisfies \(\operatorname{rad}(P)\le L^B\). Choose one admissible family of \(K\) disjoint prime tag bands of the full-target comparison, where \(K\) is sufficiently large and fixed as described below. Write \(\mathcal T\) for the products of one prime from each band and \(\mathcal V=\sum_{a\in\mathcal T}1/a\asymp_K1\). Each such \(a\) is squarefree, with exactly \(K\) prime factors in subpower ranges, and is coprime to \(P\) for large \(P\).

For every sufficiently large \(P\), **the same actual tag products \(a\)**, outside a set of small reciprocal mass, support both
\[
 P=p+a q,\qquad P=p'+a q_1q_2q_3q_4,
\tag{1}
\]
with \(p,p'\in I\) genuine primes, all \(q,q_i\) genuine primes, \(q>P/\exp(L^{1/4})\), and \(q_i\) in the respective angular ranges
\[
 (.21,.22),\quad(.23,.24),\quad(.25,.26),\quad(.27,.32)
\]
for \(\log q_i/L\) (the choice of open or closed endpoints is harmless). The second reflected integer is squarefree and all its prime factors are \(<P^{.32}\), hence are strictly below its own square root. The first has a unique near-full prime. The two reflected integers have ranks \(K+1\) and \(K+4\); their ordinary \(\lambda\) and \(\mu\) signs are opposite. The two prime rows are necessarily distinct.

More precisely, fix \(A>0\) and then choose \(K\) sufficiently large in terms of the required precision and fixed data. The exceptional \(a\) have **unnormalized** reciprocal mass \(\sum 1/a=O_{A,B,J,K}(L^{-A})\); hence their fraction of the harmonic measure on \(\mathcal T\) is \(O_{A,B,J,K}(L^{-A})\) as well. Off that exceptional set, the respective unweighted counts in (1) are
\[
 (1+o_{B,J,K}(1))\frac{\mathfrak S(P)|I|}{a L^2},
 \qquad
 (1+o_{B,J,K}(1))\frac{\mathfrak S(P)|I|}{a L^2}\,C_4,
\tag{2}
\]
where \(\mathfrak S\) is the binary singular series and
\[
 C_4=\int_{.21}^{.22}\int_{.23}^{.24}\int_{.25}^{.26}
       \frac{dt_3\,dt_2\,dt_1}{t_1t_2t_3(1-t_1-t_2-t_3)}>0 .
\tag{3}
\]
The target family includes powers of two and even integers supported on any fixed finite prime alphabet. There is no Riemann hypothesis or external conjectural zero exclusion, but effectiveness of the eventual threshold is not asserted. This does not produce a row with \(a=1\) or a binary Goldbach representation.

## 1. Whole-product masks in the projected comparison

Let \(w:\mathcal T\to\mathbb C\) with \(|w(a)|\le1\) be **any** mask, with no product decomposition or smoothness. It can depend on \(P\). In the physical reflected sum on a smooth tag shell, replace the tag weight \(\eta(a/Y)\) by \(w(a)\eta(a/Y)\). The existing [full-target minor comparison, §§1–3](../target_slope_switch/Proof.md) extends with the same log precision, holding uniformly over these masks. In fact the only change in its expanded square is the factor \(w(a)\overline{w(c)}\), or its conjugate depending on the choice of orientation. All coordinates, determinant constraints, opening of the ordered shared labels, cofactors, and endpoint weights are identical.

Here are the places in the [Jiang–Lau–Lü v2 operator input, §§5–6](https://arxiv.org/html/2611.12467v2) where this uniformity matters.

* In the real-to-independent-lines comparison (Prop. 6.5), the new per-path factor is independent of the starting frame and of the random projective lines once its labels are specified. Its modulus is at most one and the number of terms is unchanged. No new geometric boundary is introduced, since only the label products are masked.
* For a transition carrying no remembered entry or exit label, use Lemma 6.9 to pass to the fixed shared tuple and fixed-set block. In that block the integer product \(a\) is determined solely by the distinguished, unshared slots of the target tuple and \(c\) solely by those of the source. The mask factors are thus separate diagonal contractions on the two ends of (6.10) in Lemma 6.11. They can be retained through the Parseval bound (6.11), or absorbed into its endpoint functions. The tuple-order symmetrization is unchanged: each edge's unshared label in a given color is the unique label outside its shared list, so its product is independent of the order of the shared labels. Extending the block through coincidences \(a_\nu=c_\nu\) is done with the same mask and costs no extra in the absolute Schur estimate.
* For every other transition in Lemmas 6.10–6.11 the estimates are by absolute row and column sums. Multiplying a kernel entry by something of modulus at most one leaves them unchanged. The Fejér variables imposing distinct births in Prop. 5.7 multiply the same target-diagonal factors in the clean block, so the same proof and norm bound hold. The mask on opposite edge orientation is its complex conjugate, preserving the symmetry used for the even moment. The two exceptional edge bounds in Prop. 6.15 are absolute and also unchanged.

These verifications apply in the actual slope lattices and base-frame average of the full-target minor proof, not merely in the original shift-one coordinates. The parameters \(K\), \(Y\), the arc denominators and the normalized reciprocal tag mass are chosen from the **full** family. In particular the proof does not divide by the size or reciprocal mass of the retained mask.

For the major comparison, its real smooth factor is separated exactly as in §2 of [the companion proof](Proof.md), keeping the arbitrary \(w\) in its respective one-argument tag coefficient rather than differentiating it. The separated tag sums there already allow arbitrary uniformly bounded coefficients. Thus the high-moment exceptional set and small-radical Gram bounds are unchanged. The \(\varphi(P)^{-1}\) coefficient for the full projector and the exact scaled character modulus \(P d\) are retained. It follows that with the mask, for every specified \(E\) and sufficiently large fixed \(K\), the reflected shell mean square is \(O_{E,B,K}(P Y L^{-E})\), uniformly in \(w\).

Cauchy on the \(O(P/Y)\) possible **integer** residual values \(h\) yields the same arbitrary-log Type II estimate for any bounded residual \(F(h)\). This is uniform in the arbitrary mask and does not require an estimate for one modulus \(a\) alone. We use this together with the literal \(w(a)\) in Type I, and only then select the \(L^1\) mask.

## 2. A physical \(L^1\) transfer at exact \(a\)

We prove a transfer for \(F=F_1,F_4\). Here \(F_1(h)=1_{h\ {\rm prime}}\); \(F_4(h)\) indicates a product of four primes from the four mutually disjoint stated angular boxes. In the ranges considered, both are bounded by one and every prime factor of an accepted \(h\) exceeds \(P^{.20}\) for sufficiently large \(P\). For \(F_1\) the relevant \(h\) lie in \([(1-\beta)P/a,(1-\alpha)P/a]\), with \(\log a=O_K(L^{.2})\), so this last assertion holds also there. Define
\[
 \begin{split}
 R_a(F)&=\sum_{\substack{p\in I,\ p\ {\rm prime}\\a\mid P-p}}
                           (\log p)\,F((P-p)/a),\\
 M_a(F)&=\sum_{\substack{h\ge1,\ P-a h\in I\\(h,P)=1}}
                            F(h)\,\mathfrak S(P a h).
 \end{split}
\tag{4}
\]
We show, for arbitrary \(D_1>0\) and accordingly large fixed \(K\),
\[
 \sum_{a\in\mathcal T}|R_a(F)-M_a(F)|
 \ll_{D_1,B,J,K}P L^{-D_1}.
\tag{5}
\]
Both counts at the same \(a\) will follow from (5) for each of the two choices of \(F\).

**Distribution of \(F\) in Type I.** Uniform ordinary Bombieri–Vinogradov for \(F_1\) and the convolution form [Polymath, *New equidistribution estimates of Zhang type*, Theorem 2.9](https://msp.org/ant/2014/8-9/ant-v8-n9-p03-s.pdf) (the Motohashi principle) for \(F_4\) give the following estimate: for every \(D_2>0\), every \(X\asymp_J P/a\) and endpoints in a fixed compact positive multiple of \(X\), the sum over \(b\le X^{.46}\) of the absolute reduced-class discrepancy of \(F\), maximized over the reduced residue for **that common endpoint or interval**, is \(O_{D_2,J,K}(X L^{-D_2})\). The discrepancy is relative to the **coprime mean of \(F\)**. For \(F_1\) the usual prime-power removal across this modulus range costs \(O(X^{.96}\log^C X)\), or one may use the ordinary prime-count form directly, and the logarithmic weights are removed by partial summation.

For \(F_4\), the sequence is the convolution of four genuine prime indicators on the specified boxes, with exactly one ordered factorization on its support by disjointness of the boxes and unique factorization. Partition all four prime intervals into dyads, then into finer subintervals of relative width \(O(L^{-D_3})\), where \(D_3\) is a sufficiently large fixed number. There are only a fixed power of \(L\) rectangles. A retained rectangle has product scale \(\asymp_J X\); the first prime sequence on its subinterval satisfies the Siegel–Walfisz property at polynomial scale, uniformly in the shortened endpoints. In the stronger coprimality version of that property, omitting primes dividing an auxiliary integer costs at most its divisor count, and the genuine prime Siegel–Walfisz bound supplies the remaining error. The convolution of the other three sequences gives the other divisor-bounded coefficient at its product scale. Theorem 2.9 applies since the polynomial prime slot has scale at least \(P^{.20}\), hence is larger than a fixed power of \(X\). It gives arbitrary log saving after summing the rectangles. Rectangles crossing a product endpoint contain products only within \(O(X L^{-D_3})\) of that endpoint. A product belongs to at most one rectangle of the partition, since its factor in each color is uniquely determined. The error on these mixed rectangles summed over the moduli is at most \(O(X L^{-D_3+1}+X^{.46})\): for each reduced residue use the elementary count on this short **integer** interval, and for the coprime mean bound its mass divided by \(\varphi(b)\). No short-interval Bombieri–Davenport, Barban–Davenport–Halberstam, or prime-correlation assertion is being used at a shrinking endpoint. Ordinary distribution of the convolution at scale \(X\) is sufficient. We use this same reasoning at any common endpoint in a partial-summation integral.

**Extraction of the actual main for a bounded mask.** Use a sum of the left sides of (4) weighted by \(w(a)\). The identity \(P-n=a h\) is exact, not a congruence replacing it. Insert the rough mask \(P^-(n)>z=\exp(L^{.24})\) as in [the near-full cofactor proof, §2](../near_full_cofactor/Proof.md). The true prime terms are not lost; proper prime powers have negligible total contribution using the fixed-\(K\) divisor bounds. Since every prime factor of \(P\) is \(<z\), a rough \(n\) is a target unit. On a valid \(P-n=a h\) this is equivalent to \((h,R)=1\), where \(R=\operatorname{rad}(P)\). Apply Vaughan's identity with both short variables truncated at \(P^{1/5}\). The Type II source coefficient is the last term of Vaughan's identity, \(\mu_{>P^{1/5}}*(\Lambda_{>P^{1/5}}*1)\). On a product \(mn\in I\), the first, polynomial-length slot carries exactly \(\mu(m)1_{P^-(m)>z}\) restricted to \(m>P^{1/5}\), and the other carries \((\Lambda_{>P^{1/5}}*1)(n)1_{P^-(n)>z}\), bounded by \(\log n\) and zero unless \(n>P^{1/5}\). Roughness splits exactly across these slots, and their unit masks are independent (and automatic here since \(R<z\)). As in the preceding Vaughan argument, retain whole source boxes in a narrow log mesh for the actual \(mn\in I\) condition and pay the mixed boundary boxes by the divisor and tag moments. This leaves interval restrictions on the separate slots. The real major-arc multiplier separates into the bounded log frequencies of §2 of [the companion proof](Proof.md), so on the Möbius slot the only resulting real power is \(m^{iv}\), \(|v|\le L^{C_1}\), exactly the indicated coefficient in its (7), rather than an arbitrary long coefficient. The prime weight \(\log p\) is already represented in \(\Lambda\); there is no extra Type II source-log weight. The residual is \(F(h)1_{(h,R)=1}\) independent of \(a\). Thus §1 makes this term arbitrary-log small, without differentiating \(w\).

In Type I group the short divisor \(d\le P^{.4}\), with \(P^-(d)>z\). Open the remaining rough mask with squarefree \(e\) supported on primes \(\le z\), by a Bonferroni truncation at \(\lfloor L^{.1}\rfloor\) primes. The retained \(e\) and the first omitted layer satisfy \(e=\exp(O(L^{.34}))\). The omitted layer is bounded absolutely using \(O(P/(a d e)+1)\) per \(a,d,e\), and the factorial reciprocal bound \((C\log L)^j/j!\) for a layer with \(j\) prime factors. All floor errors are \(P^{.4+o(1)}\) (even after summing over all tag products), and \(\sum_a1/a=\mathcal V\) bounds the reciprocal terms. Thus the total cutoff error has arbitrary log saving. Terms with \((de,aP)>1\) are impossible on \((h,R)=1\); a prime dividing \(a\) and \(de\) would also divide \(P\), and a prime dividing \(P\) and \(de\) would divide \(h\). Otherwise the literal constraint is \(h\equiv P\bar a\bmod de\), together with \(h\) unit modulo \(R\). The CRT extends it to \(\varphi(R)\) reduced classes for modulus \(b=deR\); the latter determines \(d,e\) uniquely by their disjoint prime ranges. Uniformly \(b\le P^{.4+o(1)}<X^{.46}\), \(X\asymp_J P/a\). The aggregate Type I progression error is arbitrary-log small by the preceding distribution bound, allowing the factor \(R\le L^B\) and the fixed logarithmic coefficient and \(\log((P-a h)/d)\) variation. In particular one does not need a prime distribution theorem in progressions of modulus \(a\) with any specified relative error.

The CRT's principal contribution per \(a,d,e\) is exactly
\[
 \frac1{\varphi(de)}
 \sum_{\substack{P-a h\in I\\(h,deR)=1}}F(h)
\]
with the appropriate Vaughan coefficients (and the real endpoint \(\log((P-a h)/d)\) for its first term). We can interchange these finite \(d,e,h\) sums. For each \(h\) the \(e\) harmonic Euler product, after completion of the same factorial tail, is
\(V(P a h;z)=\prod_{\ell\le z,\,\ell\nmid P a h}(1-1/(\ell-1))\).
In the remaining \(d\) factors \(\varphi(d)^{-1}=d^{-1}(1+O(L/z))\), and removing the exclusion from primes dividing \(P a h\) in these \(z\)-rough \(d\)'s costs \(O(L^{O(1)}/z)\) per \(h\): each such prime \(>z\) contributes its \(1/\ell\) harmonic cost times fixed logarithms. The two grouped Vaughan harmonic terms then have sum
\[
 V_0(z)^{-1}+O_{D_1}(L^{-D_1}),\qquad
 V_0(z)=\prod_{\ell\le z}(1-1/\ell).
\]
This is exactly the elementary Type I identity in §2 of the prior near-full proof: the series for \(\mu(n)1_{P^-(n)>z}\) at \(1+s\) has value zero and derivative \(V_0(z)^{-1}\) at \(s=0\); the segment tails beyond \(P^{1/5}\) have arbitrary log saving by the classical Mertens bound and the same smooth-factor Rankin split. The independent short bounds in the second Vaughan term are important for this factorization. The total variation in \(h\) involved in obtaining the progression estimate was at bounded positive endpoint ratios, so these per-\(h\) harmonic factors are its correct principal term, not an independent assumed prime-pair asymptotic. We have
\[
 V(P a h;z)/V_0(z)=\mathfrak S(P a h)(1+O(L/z)),
\]
by the elementary local products, since \(2\mid P\) and at most \(O(L)\) omitted large prime factors of \(P a h\) can contribute relative loss \(O(L/z)\).

It follows after summing with \(|w(a)|\le1\) that
\(\big|\sum_a w(a)(R_a(F)-M_a(F))\big|\ll P L^{-D_1}\) with constants uniform in \(w\). Each error per \(h\) is bounded using \(\sum_a1/a=\mathcal V\); this uses the harmonic mass of the **full** tag family. Take \(w\) to be the sign of the real difference at each \(a\). This proves (5).

## 3. Same \(a\), genuine opposite parity

For both \(F\)'s, every prime of \(h\) on the physical range exceeds \(P^{.20}\); every prime of \(a\) exceeds \(\exp(cL^{.1})\). They are all target units for large \(P\). Hence uniformly
\(\mathfrak S(P a h)=(1+o(1))\mathfrak S(P)\) from its product at the primes of \(a h\) and the fixed bound \(K+4\) on their number. In the rank-one case the ordinary prime number theorem in the interval \([(1-\beta)P/a,(1-\alpha)P/a]\) gives \((1+o(1))|I|/(aL)\) choices of \(h\); they are all \(>P/\exp(L^{1/4})\) for large \(P\).

In the rank-four case fix \(q_1,q_2,q_3\) in their first three disjoint boxes, with \(t_i=\log q_i/L\). The residual prime \(q_4\) has interval endpoints \((1-\beta)P/(a q_1q_2q_3)\) and \((1-\alpha)P/(a q_1q_2q_3)\). These have a fixed positive ratio and exponents between \(.28-o(1)\) and \(.31+o(1)\), inside the fourth chosen box. They are at a polynomial scale; ordinary prime number theorem estimates on proportional subintervals give uniformly
\[
 (1+o(1))\,
     \frac{|I|}
      {a q_1q_2q_3\,L(1-t_1-t_2-t_3)}
\]
choices. Log-scale prime harmonic sums in the first three boxes converge to \(dt_i/t_i\) by Mertens and elementary partition into fixed subintervals. Thus \(M_a(F_j)\) in (4) is uniformly \((1+o(1))\mathfrak S(P)|I|C_j/(aL)\) with \(C_1=1\) and (3) for \(j=4\). No analytic estimate at a short prime interval conditional on any one particular \(a\) is required; (5) is the mechanism that certifies most individual tag products.

Declare \(a\) exceptional if either exact weighted count differs from its exact \(M_a(F_j)\) by more than \(M_a(F_j)/L\). Each such \(a\) costs \(\gg_J P/(a L^2)\) in the two sums (5), since \(\mathfrak S(P)\gg1\) and \(C_4>0\). With \(D_1>A+2\) this proves the stated exceptional reciprocal mass and gives relative error \(o(1)\) in the two counts on the same surviving \(a\)'s. Dividing by \(L\) gives the unweighted asymptotics (2), since \(\log p=L+O_J(1)\). The boxes and the arbitrary high-tag precision make the fixed parameters unambiguous. Each row has small tags and the asserted disjoint large primes, so the stated exact ranks and signs are literal.

The earlier [near-full cofactor theorem](../near_full_cofactor/Proof.md) counted near-full configurations averaged over tags, with an external zero-free input on unrestricted targets. The present joint statement gives exact-\(a\) reflected forks in two different macroscopic rank sectors in the polylogarithmic-radical family. The proof requires a nonempty family of multiple tags; its estimate cannot be specialized to \(a=1\), and it does not imply parity or a positive binary count on arbitrary even targets.
