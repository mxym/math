# Actual prime-prefix moduli in Pan's fixed-target remainder

Put \(L=\log P\), \(Q_0=P^{1/2}L^{-20}\) and \(\Theta=153/256\), where \(P\) is an arbitrary sufficiently large even target. Write
\[
 a_P(n)=\sum_{b\mid n,\ b>Q_0}\mu(b)\log b,\qquad
 E_d(f)=\sum_{n<P}f(n)\left(1_{n\equiv P\pmod d}-\frac{1_{(n,d)=1}}{\phi(d)}\right),\quad (d,P)=1.
\]
All variables here are positive. This is the actual orientation of [Huang–Li, eq. (6)](https://arxiv.org/html/2005.03811v2#S1), with no gcd restriction on \(b\).

**I (transfer).** For any fixed \(\vartheta<\Theta\) and any triply well-factorable sequence \(\lambda\) of level \(Q\le P^\vartheta\) in [Lichtman's Definition 1.4](https://arxiv.org/pdf/2309.08522),
\[
 \left|\sum_{d\le Q,(d,P)=1}\lambda_d E_d(a_P)\right|\ll_A P L^{-A}\qquad(A>0).\tag{1}
\]
This concerns a weighted sum, not the sum of the absolute values.

**II (unweighted description of an actual signed subcolumn).** Fix \(1/2\le v<\rho<\Theta\) and \(D\asymp P^v\). For a squarefree \(d=p_1\cdots p_h\) with strictly decreasing primes, let
\[
 \mathcal G=\left\{d:\ D<d\le 2D,\quad p_1\cdots p_{i-1}p_i^3\le P^\rho\quad(1\le i\le h)\right\}.
\]
Then, pointwise,
\[
 \sum_{d\in\mathcal G,(d,P)=1}\mu(d)\log d\ E_d(a_P)\ll_A P L^{-A}.\tag{2}
\]
Consequently the actual signed full dyadic Pan column equals its *centered* sum on squarefree \(d\notin\mathcal G\) up to this error: use the signed mean cancellation for the **full dyad** proved in [§D here](PanPolynomiallyRoughSurvivors.md). No vanishing of the mean on the partial mask is inferred. For example at \(v=.57,\rho=.59\), (2) includes every squarefree modulus in the dyad with one prime in \([P^{.18},P^{.19}]\) and all its remaining primes \(\le P^{.009}\). Indeed the first cube is at most \(P^{.57}\); later prefixes times the extra square are \(\le 2D P^{.018}<P^{.59}\). This is not a restriction of either input to composites. It does not bound the whole centered remainder, give its sign, or prove Goldbach.

## 1. Transfer of the dispersion inputs

We use the **large-residue** branch of [J. D. Lichtman, Propositions 3.1 and 3.2, Lemma 3.4](https://arxiv.org/pdf/2309.08522). In Proposition 3.1 the level is
\[
 x^{\min((5-4\theta)/(8-6\theta),(5-\alpha\theta)/8)-50\epsilon},
 \qquad 0<|a|<x^\alpha,quad \theta=7/32.
\]
Choose \(\alpha=1+\epsilon\) and \(\epsilon>0\) sufficiently small relative to the fixed gap in (1). We can discard \(n<P/L^K\), with \(K\) large depending on \(A\). Indeed progression multiplicity for each \(n<P\) is at most \(\tau(P-n)\), \(|a_P(n)|\le L\tau(n)\), and \(\sum_{d\le Q}1/\phi(d)\ll L^{O(1)}\); apply Hölder and the usual full divisor moments. A triply well-factorable sequence is 1-bounded (take splitting \(Q,1,1\)). The same reasoning applies to any exceptional physical set of size \(\ll_H PL^{-H}\) for every \(H\), under any fixed divisor-power coefficient. Work on bands \(n\in I\subset[x,2x],\ P/(2L^K)\le x\le P, n<P\). Then \(P<x^\alpha\) uniformly for large \(P\), and the chosen level is admissible. The modulus unit restriction may always be imposed on the input weight: multiplying by \(1_{(d,P)=1}\) preserves every convolution factorization, by imposing the same unit condition on each factor. The arithmetic equality \(n=P\) is excluded throughout.

Let \(U=P^{1/4}\), \(M_U=\mu 1_{[1,U]}\). The Dirichlet-convolution identity, valid on \(b\le P\), is
\[
 \mu(b)=\sum_{j=1}^4(-1)^{j-1}\binom4j\big(M_U^{*j}*1^{*(j-1)}\big)(b).
\]
Indeed \((\delta_1-1*M_U)^{*4}\) vanishes through \(P\); multiply its expansion by \(\mu\). Thus \(n=bu\) is a product of \(j\) bounded Möbius variables and \(j\) free variables, one of the latter being \(u\). The inequality uses the *true* product \(b=n/u\).

For each coordinate split \(w=t y\) uniquely into the full \(z_0\)-smooth part \(t\) and a \(z_0\)-rough part \(y\), with \(z_0=x^{1/(\log\log x)^3}\) as in the source. Their weights factor, with \(\mu(w)=\mu(t)\mu(y)\) for the bounded variables. The product \(T\) of all smooth parts is the full smooth part of \(n\), **with prime powers**. We may restrict to \(T\le x^\eta\), for any small fixed \(\eta>0\): the density upper bound for the exception is
\[
 \sum_{t>x^\eta,\ P^+(t)\le z_0}\frac1t
 \le x^{-\eta/\log z_0}\prod_{p\le z_0}(1-p^{-1+1/\log z_0})^{-1}
 \ll (\log x)^{O(1)}\exp[-\eta(\log\log x)^3].
\]
Here the product bound follows from Mertens' prime harmonic sum (and a convergent prime-square sum). The exception is negligible under the divisor weights by the preceding physical argument.

Take independent geometric meshes of ratio \(1+L^{-H}\) for each of at most sixteen variables \(t,y\), separating all product inequalities \(w\le U\), \(b>Q_0\), and \(T\le x^\eta\); replace \(\log b\) by the logarithm of the product of the corresponding lower endpoints with error \(O(L^{-H})\). Overcounted or deleted boundary possibilities require that \(n\) be divisible by an integer in \(B(1+O(L^{-H}))\) for one of \(B=U,Q_0,x^\eta\). There are \(\ll P(L^{-H}+1/B)\) such \(n\), even without primality constraints. Hölder gives the required total error for large \(H=H(A)\); at most \(L^{O_H(1)}\) meshes occur. Keep the final interval \(mn\in I\) exactly.

The SW short sequences are \(1_{P^-(y)>z_0}\) and \(\mu(y)1_{P^-(y)>z_0}\), including any interval cut inside a dyad of length \(Y\ge x^\epsilon\), with the extra coprimality condition of Lichtman (2.2). For clarity, write these as \(1*(\mu 1_{P^+\le z_0})\) and \(\mu*1_{P^+\le z_0}\) respectively, by Euler products. Truncate the smooth convolution variable at \(Y^{1/2}\) with arbitrary-log error by the preceding Rankin bound. For smaller smooth factors apply ordinary SW for \(1\) or \(\mu\) in the remaining residue, with the same extra unit restriction, as in the source following (2.2); only units modulo \(dq\) can contribute from the smooth factor on either side. Endpoint differences satisfy the same bound, and \(\sum_{P^+(t)\le z_0}1/t\ll L^{O(1)}\). This proves the required SW property with its permitted divisor factor and uniformly in the cut.

Now classify the rough lengths in each box by their lower endpoints (a fixed-factor change at a rail is absorbed by choosing inner margins). If some rough length is in \([x^\epsilon,x^{1/3+\epsilon}]\), this variable has exactly the preceding SW rough coefficient. All other factors, **including all smooth parts**, convolve into one long divisor-bounded sequence. Subdivide its support dyadically if needed and apply Proposition 3.1. Log savings absorb the meshes. Otherwise every bounded Möbius rough part is short (\(\le P^{1/4}<x^{1/3}\)); at most two free rough variables can exceed \(x^{1/3+\epsilon}\). The product of the nonlarge variables, smooth parts included, is \(\ll x^{\eta+8\epsilon}\). At least one large free variable remains. If exactly one, sum that rough variable in a progression for each product of the other factors: its length scale is \(\gg x^{1-\eta-8\epsilon}\gg Qx^\epsilon\). Lemma 3.4 gives arbitrary-log savings, also for subintervals by endpoint subtraction. Its printed average omits the unit restriction on the rough integers; the difference is at most \(\sum_{p\mid d,p>z_0}t/p\ll tL/z_0\) before division by \(\phi(d)\), negligible at these endpoints. For nonunit long product neither physical sum contributes. The per-modulus error \(\ll (x/m)/(dL^B)\) sums with the divisor-bounded long coefficients to the desired bound. If there are two large free rough variables, the combined remaining length \(M\ll x^{\eta+8\epsilon}\) satisfies \(Q\le (x/M)^{2/3-3\epsilon}\) upon making \(\eta,\epsilon\) small. Apply the uniform-in-residue **absolute-moduli** Proposition 3.2 dyadically, with both free rough coefficients exactly its rough indicators. To restrict either dyad to a mesh interval \((s,t]\), telescope \(1_{n\le t}-1_{n\le s}\) into dyads with endpoints \(t2^{-j},s2^{-j}\); the retained product \(mn_1n_2\in I\) and upper bounds on the other variables force any contributing dyad to have length comparable to its original scale. This justifies all Proposition 3.2 intervals without adding an arbitrary short-variable coefficient. This proves (1).

## 2. Uniform packing of entire independent coefficient boxes

Choose \(\rho<\vartheta<\Theta\), and fix \(\gamma>0\) sufficiently small that \(v+6\gamma<\rho\). For each squarefree \(d\asymp P^v\), every prime \(p>P^\gamma\) is a singleton component in decreasing order. For the rest, read its primes in decreasing order and stop a block just when its product first reaches \(P^\gamma\); start the next block with the next prime, leaving at most one shorter terminal block. These later blocks are each \(\le P^{2\gamma}\), and the number of all components is bounded in terms of \(v,\gamma\). The condition for a completed block of product \(y\) is exactly \(y\ge P^\gamma, y/P^-(y)<P^\gamma\). This is a **local condition on that single component**; there is no unspecified coprimality, moveable prefix or coupled greedy cut.

Put the product and the smallest/largest prime of each nonempty component in independent meshes of ratio \(1+L^{-H}\). Discard boxes where the prime ranges of adjacent components overlap in a mesh cell. The number of affected \(d\le2D\) is
\[
 \ll D\sum_{p<r\le(1+O(L^{-H}))p}\frac1{pr}\ll DL^{-H}L^{O(1)},
\]
where both primes divide \(d\) and are distinct; use that the number of eligible integers \(r>p\) is at most \(O(L^{-H}p)\), and prime harmonic summation. This bound also handles very small prime coordinates with no neighbor. Discard boxes crossing \(D,2D\) at the product endpoints; their total size is \(O(D L^{-H}+1)\), as the number of components is bounded. Only singleton prefix inequalities need be checked: for every small prime \(p_i\le P^\gamma\) its prefix times its extra square is at most \(2D P^{2\gamma}<P^\rho\). Boxes crossing a tested inequality have an actual divisor \(bp\mid d\) with \(p>P^\gamma\) and \(bp^3=P^\rho(1+O(L^{-H}))\). For each \(b\le 2D\) the eligible \(p\) lie in one relatively \(O(L^{-H})\)-short interval; their reciprocal sum, even counting all integers, is \(\ll L^{-H}+P^{-\gamma}\). Summing \(2D/(bp)\) proves the same arbitrary-log density bound. These discards cost \(O_A(P L^{-A})\) in (2): if \(E\) is an exceptional modulus set, the physical support has size \(\le |E|(P/D+1)\), and \(\sum_{d\in E}1/\phi(d)\ll L^{O(1)}|E|/D\). Apply the earlier divisor moments, taking \(H\) large. Replace \(\log d\) by the logarithm of the product of the component lower endpoints at negligible total cost, using the absolute divisor bound for the full domain.

Each remaining box coefficient is now *exactly* the convolution of 1-bounded independent single-component sequences: squarefree \(\mu(y)\) with the described local restrictions (and prime indicator as appropriate). Component prime ranges are disjoint and strictly ordered. Thus the convolution of **any subcollection**, not just all components together, is 1-bounded: the prime partition of the argument recovers the unique possible factor in each component. Conversely any tuple in this convolution obeys the original ordered pattern and greedy rule, lies in the true dyad, and satisfies the true prefix inequalities. These boxes are disjoint on actual moduli.

For a box let \(B_i\) be the numerical upper endpoint of component \(i\) in the stated order. Then for every \(i\),
\[
 (B_1\cdots B_{i-1})B_i^3\le P^\vartheta.
\]
For singletons use the tested prefix cutoff and the fixed gap \(\vartheta-\rho\); for later components use the total product \(\le 2D(1+o(1))\) and \(B_i^2\le P^{4\gamma}(1+o(1))\). Given **any real splitting** \(P^\vartheta=Q_1Q_2Q_3\) with \(Q_j\ge1\), assign components successively. Before item \(i\), the three remaining capacities have product \(P^\vartheta/(B_1\cdots B_{i-1})\ge B_i^3\), so one capacity is at least \(B_i\); assign it there and divide that capacity by \(B_i\). The assignment depends on the splitting and the entire **box**, never on the individual modulus. The three grouped convolutions are 1-bounded by the preceding uniqueness and supported within their three assigned capacities. Empty bins give \(\delta_1\). This gives the exact factorization required in Lichtman's Definition 1.4, for each splitting. Apply (1) separately to the \(L^{O_H(1)}\) boxes, with arbitrary additional log savings; the constant \(O(L)\) from the log weight costs only another logarithm. This proves (2).

The analytical engine, the triply well-factorable class, and the broader use of anatomies of sifted moduli are prior work: see Lichtman's §§2–7 and his comparison with Maynard, Bombieri–Friedlander–Iwaniec and Iwaniec. We do not insert a single-factorization weight into a theorem requiring every split, or allege new distribution of primes in general moduli. The unresolved centered sum retains moduli having a failed cubic prefix, and larger unrestricted columns. No absolute-priority or global positivity statement follows.

Recent comparisons through 21 November 2026: [The Restricted Chen Sieve, v1](https://www.preprints.org/manuscript/202611.0694) records the same published large-residue exponent for primes, and [Slava Chan's (1+1.75) preprint, sections 4 and F.1](https://aixiv.online/pdf/2611.00586) uses odd-rank cubic prefixes and first exits for a nonnegative sieve majorant. The argument here imposes every prefix on an actual signed Pan modulus subcolumn and transfers to its different truncated-divisor input. The related work is not a claim about its remaining centered sign, and this search does not establish priority.
