# A presieved parity countermodel for the unguarded cubic gate

Let \(P\) run over large prescribed even integers, \(L=\log P\), \(I=[P/3,2P/3]\), \(X=|I|\mathfrak S(P)\), with the usual binary Goldbach singular series. Write \(y=P-x\). Put \(z=\exp(L^{1/10})\), \(W=\prod_{\ell\le z}\ell\), \(V=\prod_{\ell\le z}(1-1/\ell)\), over primes, and \(\lambda=(-1)^\Omega\). For \(-1\le t\le1\) put on **all integers** \(x\in I\) the nonnegative weight
\[
 w_t(x)=V^{-1}1_{(x,W)=1}(1+t\lambda(P-x)).
 \tag{1}
\]
It models **one** von Mangoldt weight, not an unweighted prime indicator; in particular it is not supported on primes. The integers factoring \(y\), on the other hand, will be genuine. No conjecture about primes is used to construct it.

**Distribution theorem.** Fix \(0<\epsilon<1/2\) and \(A,C>0\). Uniformly in even \(P,t\), with maxima over all subintervals \(J\subset I\), both estimates hold:
\[
 \sum_{q\le P^{1/2-\epsilon}}\tau(q)^C
 \max_{(a,q)=1,J}\left|\sum_{x\in J,\ x\equiv a\ (q)}w_t(x)-{|J|\over\phi(q)}\right|
 \ll_{\epsilon,A,C} P L^{-A},                                            \tag{2}
\]
\[
 \sum_{\substack{d\le P^{1-\epsilon}\\(d,P)=1}}\tau(d)^C
 \max_J\left|\sum_{x\in J,\ d\mid P-x}w_t(x)-{|J|\over\phi(d)}\right|
 \ll_{\epsilon,A,C} P L^{-A}.                                            \tag{3}
\]
For (3) there is just **one** residue in the source, not all reduced residues beyond the square root. The sums (2),(3) use exactly (1), without silently removing additional residue classes. In angular applications take the usual unit restriction \((x,P)=1\).

For \(k=2,3,4\) take the own-log cubic score of the [unguarded cubic gate](https://github.com/mxym/math/commit/d581f0c4): on a squarefree \(y=\prod_{i=1}^k r_i\), \(u_i=\log r_i/\log y\),
\[
 A_k(\mathbf u)=\sum_{S\subset[k]}(-1)^{|S|}(1-2\sum_{i\in S}u_i)_+^3,\qquad
 I_k=\int_{\sum u_i=1} A_k(\mathbf u)\,{du_1\cdots du_{k-1}\over k!\prod u_i}.
\]
Define \(\widetilde H_t=L\sum w_t(x)A_k(\mathbf u)\) on these three ranks and units, and \(\widetilde G_t=\sum_{x\in I,(x,P)=1,\,y\ {\rm prime}}w_t(x)\log y\). Then uniformly in \(t\)
\[
 \widetilde G_t/X=1-t+o(1),\qquad
 \widetilde H_t/X=(1+t)m_E+(1-t)m_O+o(1),\quad
 m_E=I_2+I_4,\quad m_O=I_3=2.                                          \tag{4}
\]
In particular at \(t=1\) the model prime-pair statistic is **exactly zero**, while \(\widetilde H_1/X\to6.07334309\ldots>5.9415\). This family satisfies the *numerical* cubic bracket \(5.9415<(\widetilde G_t+\widetilde H_t)/X<6.183\) eventually. It satisfies the complete cubic angular model on any fixed compact rank profile, multiplied by \(1+(-1)^k t\), so in particular it satisfies any upper domination by \(200/53\) times the nonnegative compact rank reference. For a finite sum of such tests (or the unguarded cubics above), if its signed ordinary angular integrals on even and odd ranks agree, its model value does not depend on \(t\). It is **not** a model proved to satisfy general Type II estimates, simultaneous bounds for arbitrary residues to level one, the von Mangoldt convolution identities for the \(x\)-weights, or all prior bilateral theorems. Even (3), stronger in level than what is known for arbitrary coefficients for the true reflected primes, does not by itself price this gate.

## 1. Distribution

We record the standard ingredients to fix the norms. The classical maximal Bombieri–Vinogradov bound for Möbius with zero main term ([Siebert–Wolke, Corollary 1, *Math. Z.* 122 (1971), 327–341](https://doi.org/10.1007/BF01110168), explicitly restated as [Murty–Vatwani, Proposition 3, *J. Ramanujan Math. Soc.* 33 (2018), 111–123](https://www.mathjournals.org/jrms/2018-033-002/2018-033-002-001.html)) implies, at every fixed power gap from the square root, the corresponding bound
\[
 \sum_{h\le Y^{1/2-\sigma}}\tau(h)^D
 \max_{(b,h)=1,\ J'\subset[1,Y]}
 \left|\sum_{n\in J',\,n\equiv b\ (h)}\lambda(n)\right|
 \ll_{\sigma,D,B} Y(\log Y)^{-B} .                                     \tag{5}
\]
Indeed \(\lambda=\mu*1_{\rm squares}\). Truncate the square root \(j\) at \((\log Y)^K\). Small \(j\) use the maximal Möbius bound at \(Y/j^2\); for large \(j\) the absolute progression count is at most \(Y/(j^2h)+1\), since \((b,h)=1\); the total is \(O(Y(\log Y)^{1-K}+Y^{1-\sigma})\) before divisor weights. Divisor weights follow by Cauchy from the unweighted bound with doubled log reserve, the elementary individual bound \(Y/h+1\), and harmonic divisor moments. This includes \(h=1\), and interval sums by differencing prefixes.

In each progression use the dimension-one fundamental lemma with \(K_0=P^{\epsilon/20}\), on the divisibility tests \(\ell\mid x,\ \ell\le z\), omitting any primes at which they are impossible. The upper/lower divisor sums \(U^\pm\) have squarefree labels \(k\mid W,\ k\le K_0\) with coefficients bounded by 1. They trap the indicator pointwise; their model main terms at density \(1/\ell\) differ from the sifted Euler product by \(O_B(L^{-B})\) relative, since \(\log K_0/\log z\gg_\epsilon L^{9/10}\). This is the usual combinatorial fundamental lemma, e.g. [Theorem 2.2 here](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136). The same error applies to the positive difference \(U^+-U^-\). By \(|\lambda|=1\), replacing the indicator by \(U^+\) in a signed sum costs at most the **unsigned** sum of this difference; no signed inequality is assumed.

For the untwisted part of (2) on \(x\equiv a\bmod q\), a prime dividing \(q\) is omitted, and each other sieve label contributes \(|J|/(qk)+O(1)\). For (3) set \(y=dv\); on \(x=P-dv\) the primes dividing \(d\) are omitted since \(d\) is a target unit, and the other labels give \(|J|/(dk)+O(1)\). In either case, writing \(b_0=q\) or \(d\), normalization by \(V\) gives \((|J|/b_0)\prod_{\ell\mid b_0,\,\ell\le z}(1-1/\ell)^{-1}\), apart from the fundamental-lemma error and \(O(K_0/V)\) in each progression. Extending the product to all \(\ell\mid b_0\) incurs relative \(O(L/z)\). These errors, including the floors with divisor multiplicities, total \(O_A(PL^{-A})\); in (3) note \(P^{1-\epsilon}K_0=P^{1-19\epsilon/20}\). The same applies to the unsigned difference just described, uniformly over the intervals.

For the \(\lambda\) part of (2), fix \(q,a\) and a sieve label \(k\) coprime to \(q\). The conditions on \(y\) are \(y\equiv P-a\bmod q,\ y\equiv P\bmod k\), one class modulo \(D=qk\). If the class is not reduced, divide by its actual gcd \(g\mid D\): \(y=g v\), \(v\) belongs to one reduced class modulo \(D/g\), and \(\lambda(y)=\lambda(g)\lambda(v)\). There is no coprimality assumption between \(g\) and \(D/g\). After taking absolute values and the maxima, enlarge by summing over **all** \(g\mid D\). Pairing \(q,k\) costs at most \(\tau(D)^{C+1}\). Write \(D=gh\); now \(h\le P^{1/2-19\epsilon/20}/g\le(P/g)^{1/2-\epsilon/2}\). Apply (5) at \(Y=P/g\), then sum \(P\,\tau(g)^{C+1}/g\) with arbitrary log reserve. The factor \(V^{-1}\ll L^{1/10}\) is harmless.

For (3), with \(y=dv\), one has \(v\equiv P\bar d\bmod k\), \((d,k)=1\). Divide by \(g=(P,k)\); the reduced residual class has modulus \(h=k/g\). For each fixed \(d,g\), \(h\le K_0/g\le(P/(dg))^{1/4}\), since \(d\le P^{1-\epsilon}\). Apply (5) at \(Y=P/(dg)\) with the factor \(\lambda(dg)\) of modulus one; then sum over \(g\le K_0\) and \(d\le P^{1-\epsilon}\), at cost \(P\sum_{d,g}\tau(d)^C/(dg)\) before arbitrary log saving. Here \(\log(P/(dg))\gg_\epsilon L\). This proves both bounds.

## 2. Angular profile law and removal of small factors

First take a fixed compact rank-\(k\) profile, all \(u_i>\kappa>0\), and a bounded, piecewise Lipschitz angular weight \(B\) with finitely many polyhedral boundaries. The ordinary mass over actual unlabelled squarefree \(k\)-prime products in \(I\) is \((|I|/L)(\int B\,d\sigma_k+o(1))\), \(d\sigma_k=du_1\cdots du_{k-1}/(k!\prod u_i)\), by PNT; for \(k=1\) use the atom of mass one. In the sieve for \(x=P-y\), small primes dividing \(P\) can be omitted, since \(P^-(y)>z\). For the other squarefree labels \(k'\le P^{.01}\), the actual rank-\(k\) source in the reduced class \(P\bmod k'\) has model equal to its own total divided by \(\phi(k')\), with discrepancies saving every fixed power of log in sum. For \(k=1\) this is prime BV; for \(k\ge2\) it is the classical convolution BV used in the [giant comparison, §2](https://github.com/mxym/math/commit/3334f60c), for fixed polynomial prime slots: a slot and the complementary product both exceed a fixed power, prime slots have Siegel–Walfisz, and independent fine log boxes separate the product/order and piecewise Lipschitz cuts. Equivalently first use fixed upper/lower smooth angular envelopes with arbitrarily small ordinary mass difference, obtain the formula for each, then squeeze. No transfer for an arbitrary Boolean subset of products is being used. The reduced-class total sees no nonunits at \(k'\mid W\) on this compact source. Target primes exceeding \(z\) in \(y\) may be discarded physically at a cost \(O(P L^{O(1)}/z)\) using their number \(O(L)\) and the integer multiples bound. Local factors give
\[
 V^{-1}\prod_{\ell\le z,\ \ell\nmid P}(1-1/(\ell-1))
 =\mathfrak S(P)(1+O(L/z)).
\]
Indeed \(2\mid P\), and the factors on the left divided by the Mertens factors are \(\ell/(\ell-1)\) at \(\ell\mid P\) and \(1-(\ell-1)^{-2}\) otherwise. The dimension-one fundamental lemma for the nontrivial local densities \(1/(\ell-1)\), \(\ell>2\), at level \(P^{.01}\) has relative error \(O_B(L^{-B})\). This proves the compact law, with the exact multiplier \(1+t(-1)^k\). At rank one replace \(L\) by \(\log y=L+O(1)\), using the already bounded normalized nonnegative mass.

For the three unguarded weights, the following elementary bound controls the **model arithmetic** and all target local factors. On ranks \(2\le k\le4\), pairing subsets differing in a smallest exponent and using the cubic hinge's Lipschitz bound yields
\[
 |A_k|\le 6\,2^{k-1}\min_i u_i\le 48\prod_i u_i^{1/4}.
\]
Suppose one exponent is at most \(\kappa\); choose a largest prime \(q\) last and put \(d=y/q\le(2P/3)^{1-1/k}\). In this tail a smallest prime dividing \(d\) is \(\le P^\kappa\). Keep the unit, odd \(d\); for an upper bound on the remaining prime \(q\), sieve \(q\) through \(P^{.01}\), and \(P-dq\) through \(z\). Both conditions held on the original rows for large \(P\). Use the ordinary dimension-at-most-two upper sieve in the \(q\) variable at level \(P^{.12}\). There are two roots at \(\ell\le z,\ \ell\nmid Pd\), one at the other tested primes, including 2. Compared with the product of the two separate Mertens factors the local corrections are bounded by \(O(\mathfrak S(P))\): primes of \(P\) supply the singular factors and the at most three odd prime factors of \(d\) cost an absolute factor. CRT floors total \(O(P^{.12+o(1)})\) per \(d\), absorbed by \(P/(d L\log z)\) uniformly since \(d\le P^{3/4}\). Thus the count is \(\ll \mathfrak S(P)P/(dL\log z)\). Multiply by \(LV^{-1}\asymp L\log z\); on \(I\) replace \(u_i^{1/4}\) in this upper by \(O((\log r_i/L)^{1/4})\). Dropping the largest factor's weight, the remaining prime harmonic sums \(\sum_{r\le P}(\log r/L)^{1/4}/r\) are bounded, and one restricted to \(r\le P^\kappa\) is \(O(\kappa^{1/4})\), in limsup by partial summation. The total discarded actual model mass is \(O(\kappa^{1/4})X\), uniformly in \(t\) and \(P\) in that order. The same finite-rank integrals converge by this angular bound (use a largest coordinate). This proves (4) by taking \(P\to\infty\) then \(\kappa\downarrow0\).

## 3. Exact amount of missing even/odd information

From the [audited angular integrals](https://github.com/mxym/math/commit/d581f0c4), \(I_2=1+2\log2\), \(I_3=2\),
\[
 I_4=\tfrac32\zeta(3)+(4-\pi^2/3)\log2-\pi^2/6,\qquad
 M=m_E+m_O=5.0366715499\ldots,\quad D=m_E-m_O=M-4.
\]
These are independent of the parity model: for instance \(A_3=24u_1u_2u_3\), so the rank-three integral is \(24/(3!\cdot 2!)=2\). The two-prime integral is \(\int_0^{1/2}(1-(1-2u)^3)\,du/(u(1-u))=1+2\log2\). The cited rank-four cosine/Mellin evaluation uses only the unrestricted simplex, not a sieve conjecture.

For the **actual** prime source split \(h_E=(H_2+H_4)/X,\ h_O=H_3/X\). The balanced mass and its signed parity correlation are
\[
 T=\tfrac12(h_E/m_E+h_O/m_O),\qquad B=\tfrac12(h_E/m_E-h_O/m_O).
\]
Equivalently the second uses the multiplier \(\lambda(y)\) on the same nonnegative normalized test as the first. Exactly \(H_{234}/X=MT+DB\). Therefore if independently \(T\le1+\eta\), a sufficient single parity upper to meet the cubic gate is
\[
 B\le {5.9415-M\over D}-{M\over D}\eta
     =0.87282075\ldots-4.85850272\ldots\,\eta .
\]
Use the exact fractions, not the rounded decimals, at an endpoint. For a known actual value of \(T\), put \(\eta=T-1\) to obtain the necessary and sufficient condition for **this numerical gate**, not for Goldbach itself. No calibrated bound \(T\le1+o(1)\) or strict parity gain for the actual primes is asserted. Equivalently the genuine even deficit from the endpoint model, \(2m_E-h_E\), must exceed \(h_O\) by at least \(2m_E-5.9415=0.13184309\ldots\) to cross this gate. In the explicit family \(T\to1,\ B\to t\), so under exact parity-neutral calibration no weaker single upper on \(B\) can force the gate throughout even this specified family. A theorem for the actual primes must use a fact not shared by the relevant countermodels; this does not refute any such theorem.

The parity mechanism is classical, not a new obstruction to sieve theory in general: compare [Friedlander–Iwaniec, *On Bombieri's asymptotic sieve* (1978)](https://www.numdam.org/item/ASNSP_1978_4_5_4_719_0/) and [Tao, notes on the Bombieri asymptotic sieve](https://terrytao.wordpress.com/2016/07/17/notes-on-the-bombieri-asymptotic-sieve/). The content here is the simultaneous concrete source/reflected distribution ranges, actual cubic H234 profile law and exact obstruction threshold for this particular criterion. It is different from deleting selected **genuine** primes in the [true-prime mask](https://github.com/mxym/math/commit/0377f919); (1) makes no genuine-prime-support claim.

A closer recent comparison is [B. Arneth, *Finite Bonferroni–Liouville Transfer*, 22 October 2026](https://zenodo.org/records/23560521). In the author's description, the starting sequence is supported on genuine primes, the complementary integer is sifted beyond its cube root, and the Liouville projector then separates the two remaining ranks. A second shifted presieve and finite Bonferroni expansions give a comparison sequence; a coupled Liouville progression estimate and a one-sided transfer to the actual primes remain assumptions for positivity. We do not claim priority for shifted presieves with Liouville projectors or infer any unstated modulus level from that description. In (1) there is instead no prime-support assumption on \(x\), no cube-root cutoff on \(y\), and the two levels (2),(3) are proved for this explicit countermodel, not assumed for the primes. The published record was accessible; the accompanying PDF was not available for independent equation-by-equation comparison here.

## Appendix. A prime-sized deterministic support, still not the primes

For any fixed \(t\in[-1,1]\) there also exists a sequence of sets \(S_{P,t}\subset I\) for which replacing \(w_t\) by \(L1_{S_{P,t}}\) preserves (2)–(4), and all the fixed compact angular laws in §2. At \(t=1\), **no** member has a genuine prime complement. These sets may depend on \(P\); there is no claim that one infinite set works for every reflected target. They have \(|S_{P,t}|\sim |I|/L\) by (2) with \(q=1\), and the weight squares exactly to \(L\) times itself. Thus the obstruction does not depend on an artificially dense support or on small weights in a second moment.

Independently retain each \(x\) with probability \(w_t(x)/L\le1\) for large \(P\), zero wherever (1) is zero. For each interval/progression at modulus \(h\le P\), the centered retained weight has summands bounded by \(L\) and variance \(\ll(1+P/h)L^{1.1}\), since \(\max_x w_t(x)\ll L^{.1}\). Bernstein's inequality and a union bound over all moduli, residues and integer prefix endpoints show that one can simultaneously bound every prefix error by
\[
 O\big(L^3\sqrt{1+P/h}+L^3\big).
\]
The failure probability is \(O(P^{-10})\), say; the exponent in the Bernstein tail is \(\gg L^2\). Differencing gives all intervals. Summed with \(\tau(h)^C\) up to \(H\le P^{1-\epsilon}\) this is \(O_C(L^{O_C(1)}(\sqrt{PH}+H))=o_{\epsilon,C,A}(P L^{-A})\), hence works for every fixed positive gap on the same realization.

Also include these tests in the union bound: the prime-\(y\) weight \((\log y)/L\) and the three bounded unguarded cubic tests with their actual rank/unit indicators, and the rank-and-unit indicators of boxes in the coordinates of the **ordered** exponents of the factors of \(y\). For instance include dimensions \(k\le\lfloor\log\log\log P\rfloor\) and all box endpoints with rational numerator and denominator at most \(\lfloor\log\log P\rfloor\) in \([0,1]\). This is \(P^{o(1)}\) bounded tests besides the four single tests (the latter bounded by an absolute constant). Each centered sum is \(O(\sqrt P L^3+L^3)\) by the same argument; after multiplication by \(L/X\) its error vanishes. Pick a successful realization for each sufficiently large \(P\). Every fixed rational box in every fixed dimension is eventually included. On a compact sub-simplex separated from zero faces, sums on rational boxes bound any fixed bounded piecewise Lipschitz profile with null discontinuity set by upper/lower step approximation: the limiting ordinary measure is absolutely continuous there and finite, and the thinned and deterministic measures are nonnegative. For \(k=1\) the separate prime test covers the atom; for \(k\ge2\) coordinate threshold planes have measure zero. This establishes simultaneous compact universality without an uncountable union of probability events. The unguarded cubics already had their own bounded tests.
