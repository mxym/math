# The G23 mixed statistic has a genuine positive major-arc term on a dispersed polynomial-factor core

Research note, 2026-11-24. This is not a lower bound for the full additive coefficient or a minor-arc estimate. It shows why hoping for an arbitrary-log **localized** mixed estimate on just the A2/A3 sectors is not a consequence of matching their true marginals: on a specific width-positive core its standard major term is already too large.

## 1. Real prime product sequences and the statement

Let \(P\) be large even, \(\operatorname{rad}(P)\le L^B\), \(L=\log P\), and take smooth \(0\le\phi\le1\) compactly supported in a fixed interior portion of \((0,1)\), centered so that \(\int_0^1\phi(t)\phi(1-t)\,dt>0\). Define the true classes, with all factors prime and distinct:
\[
\begin{aligned}
A_2'&=\{n=pq:\ p<q,\ P^{.26}<p<P^{.49}\},\\
A_3'&=\{n=p q r:\ p<q<r,\ p,q,r>P^{.30}\}.
\end{aligned}
\]
On the central support, in \(A_2'\) the larger \(q>P^{.51-o(1)}\), and in \(A_3'\) each factor \(<P^{.40}\). Thus these are genuine dispersed angular regions of \(A_2,A_3\), squarefree, all factors \(>P^{1/4}\). The marker in [the \(G_{23}\) proof](SmallRadicalG23CoreBilateral.md) is exactly 1 and 3, respectively, for every such genuine row, for \(D=P^{1/2}e^{-L^{3/5}}\) and any fixed cutoff \(P^\sigma\) with \(\sigma<1/4\). In particular these rows are **base-uncovered** once \(K>3\).

Set
\[
f(n)=\phi(n/P)(\log n)(1_{A_2'}(n)-3\,1_{A_3'}(n)),\quad
g(n)=\phi(n/P)(1_{A_2'}(n)-1_{A_3'}(n)).
\]
Then \(\sum_n f(n)g(P-n)\) is the actual unmarked mixed statistic restricted to this core, with a smooth window. Let \(Q=L^J\) for a sufficiently large fixed \(J\), and take disjoint major arcs \(\alpha=a/q+\beta\), \(q\le Q,(a,q)=1, |\beta|\le Q/P\) on the unit torus. Define \(S_f(\alpha)=\sum_n f(n)e(n\alpha)\), and similarly \(S_g\). The true major-arc contribution is
\[
\int_{\mathfrak M}S_f(\alpha)S_g(\alpha)e(-P\alpha)\,d\alpha
=\frac{P S(P)}{L}(C_2-3C_3)(C_2-C_3)
 \left(\int_0^1\phi(t)\phi(1-t)\,dt\right)
+O\left(\frac{P S(P)}{L^2}\right),
\tag{1}
\]
with \(C_2>\tfrac12\) and \(0<C_3\le\tfrac16\). Consequently the leading coefficient is strictly positive and of size \(PS(P)/L\), larger than \(PV_y(P)/L\) by \(\asymp L^\delta\) when \(y=e^{L^\delta}\). This does not assert the same sign or magnitude for the **whole** Fourier integral.

## 2. Genuine one-coordinate prime AP approximations, with all previous factors fixed first

Let \(t\asymp P\) denote a real physical product and \(A=\log t/L\). The continuum counting-density factors for the two classes are
\[
\begin{aligned}
D_2(t)&=\frac1L\int_{.26}^{.49}\frac{du}{u(A-u)},\\
D_3(t)&=\frac1L\int_{\substack{.30<u<v<A-u-v\\A-u-v>.30}}
                  \frac{du\,dv}{uv(A-u-v)} .
\end{aligned}
\tag{2}
\]
The domain in the second integral contains precisely the sorted angular simplex with all three coordinates greater than \(.30\) and sum \(A\). The functions are smooth uniformly on every fixed interior \(t/P\) range: parameterize the ordered simplex by subtracting \(.30\) from each angle and dividing by the positive excess \(A-.90\), which stays bounded away from zero. They have size \(O(L^{-1})\) and any fixed derivative of order \(j\) is \(O(L^{-1}P^{-j})\) there. Moreover \(D_i(t)=C_i/L+O(L^{-2})\) uniformly, with \(C_i=L D_i(P)\).

Here is a direct derivation for true Fourier coefficients on those major arcs. In either class fix the first one or two actual smaller primes, write \(d\) for their product, and the final true prime as \(r\), with \(t=d r\). On the \(\phi\) support and under the last-factor angular constraints the endpoint for \(r\) is polynomial in \(P\), and all valid \(r\)'s exceed a fixed power of \(P\); both moving endpoints can be handled by differences of prime AP prefixes. Every previous factor exceeds \(P^{.26}\) for the rank two case and \(P^{.30}\) for the rank three case, so \((d,q)=1\) for all small \(q\le Q\). Ordinary Siegel–Walfisz on \(r\) uniformly over reduced residues modulo \(q\), followed by partial summation with \(\phi(d r/P)e(\beta d r)\) and optional \(\log(d r)\), gives the factor
\[
\frac{1}{\varphi(q)}\sum_{a'\bmod q,\ (a',q)=1}e(a d a'/q)
=\frac{\mu(q)}{\varphi(q)}.
\]
All Fourier weights in this step have variation at most \(L^{O(J)}\) times their natural log amplitude, since \(|\beta|P\le Q\). Summing absolute arithmetic errors over previous factors costs only \(\sum_d 1/d=O(1)\) on the relevant polynomial prime ranges (even ordered pairs), while the progression input can be taken with arbitrary extra powers of log saving. Proper equality endpoints such as \(r=q\) in the rank-three ordering can be omitted in the prefix integer convention; the total possible repeated-prime source count is \(O(P^{.74+o(1)})\) even without primality of the residual part, by requiring a prime square \(>P^{.52}\). Such deletions are also arbitrary-log negligible.

After \(t=d r\) is substituted in the continuous model, the previous prime labels occur with weights \(1/[d\log(t/d)]\) and true angular cutoffs. For each fixed \(t\asymp P\), replace each previous prime sum by an integral via the ordinary PNT and partial summation. In the rank-three case the smaller label \(p\) ranges up to \(t^{1/3}\); at fixed \(p\) the middle label lies between \(\max(p,P^{.30})\) and \(\sqrt{t/p}\). Every relevant endpoint is polynomial and the reciprocals \(1/[d\log(t/d)]\) on these intervals have their usual bounded-variation weights. In iterating the PNT, endpoint variation of the inner integral is also polynomially scaled with bounded log losses (differentiate its smooth integrand and \(\sqrt{t/p}\)); this proves arbitrary-log uniform errors by taking extra PNT accuracy. On changing variables \(p=P^u,q'=P^v\), the resulting integrals are exactly (2). This establishes the uniform major arc replacements
\[
\begin{aligned}
S_f(a/q+\beta)&=\frac{\mu(q)}{\varphi(q)}
 \int \phi(t/P)(\log t)(D_2(t)-3D_3(t))e(\beta t)\,dt+O_E(PL^{-E}),\\
S_g(a/q+\beta)&=\frac{\mu(q)}{\varphi(q)}
 \int \phi(t/P)(D_2(t)-D_3(t))e(\beta t)\,dt+O_E(PL^{-E})
\end{aligned}
\tag{3}
\]
for all fixed \(E\), after increasing the original PNT precision. These are approximations of the true prime product coefficients, not factor-independence assumptions.

## 3. Complete the major term and check its sign

The sum over \(a\bmod q\) in the product (3) gives the usual partial singular series \(\sum_{q\le Q}\mu(q)^2 c_q(P)/\varphi(q)^2\). It tends to \(S(P)\) with any required logarithmic saving after choosing \(J\) sufficiently large in terms of \(B\): by Rankin with exponent \(1/2\), the absolute tail is bounded by \(Q^{-1/2}\) times the product of \(1+\ell^{1/2}|c_\ell(P)|/(\ell-1)^2\). The nontarget product converges, and the target product is at most \(L^{O_B(1)}\) since \(\omega(P)\ll_B\log L\). The real transforms in (3) have rapid decay in \(P|\beta|\) by smoothness and support of \(\phi(t/P)\) and the derivative bounds after (2); the \(f\)-amplitude has size \(O(1)\), and the \(g\)-amplitude \(O(1/L)\). Thus extending \(\beta\) to \(\mathbb R\) costs arbitrarily small fixed log powers of \(P\)'s main scale after increasing \(J\). The total major measure is \(O(Q^3/P)\), so all errors in (3) are negligible by taking \(E\) after \(J\). Fourier inversion on the real integrals reduces the answer to the product of real densities at \(t,P-t\); substitute \(D_i=C_i/L+O(L^{-2})\) there, and \(\log t=L+O(1)\). This proves (1).

For the signs,
\[
C_2=\int_{.26}^{.49}\frac{du}{u(1-u)}
=\log\!\left(\frac{49\cdot74}{51\cdot26}\right)>\frac12.
\]
For \(C_3\), enlarge the domain \(\alpha_i>.30\) to all three \(\alpha_i\ge1/4\), with sum 1. Its full coordinate-area is \(1/32\), its sorted region one sixth of that by symmetry, and \(1/(\alpha_1\alpha_2\alpha_3)\le32\) since the product is minimized at the corners \((1/4,1/4,1/2)\). Thus \(C_3\le1/6\), and \(C_3>0\) since a neighborhood of \(1/3,1/3,1/3\) has admitted sorted interior. This proves strict positivity of the product of constants.

The genuinely marked statistic restricted to these same true classes differs in absolute weight by \(O(P L^{-M/200})=o(PV_y/L)\) for fixed \(M\ge400\), without adding a complementary roughness restriction to the absolute deletion estimate. Indeed fix the earlier actual prime labels, all polynomial and hence units at packet primes, and pay actual final-prime multiplicity by the shifted cover sieve or the positive single-class variant of §4 at frequency zero. These labels have \(O(1)\) reciprocal mass, and \(\log n/\log r=O(1)\). The threshold must satisfy \(M/200>1+\delta\) for this deletion proof. This is about the **total** deletion error; (1) is a major-arc term for the unmarked source Fourier product. Even if (1) were canceled by minor arcs, such cancellation would be a genuine analytic input. Neither (1) nor the separate marginal estimates control the fixed-target total, and the full mixed coefficient also includes many other rank sectors that might contribute essential cancellation.


## 4. A separate genuine marked major-arc calculation

This is stronger than the comparison of full additive totals in the previous paragraph. Let \(\mathcal B_*\) be the packet prime union of the actual shifted selector \(C=C_{>1}\) at fixed \(M\). At each packet prime \(\ell\), in the reference **reduced-class** experiment independently choose one of \(M+1\) outcomes: offset \(j\) is hit with probability \(1/(\ell-1)\) for each \(j=2,\ldots,M+1\), or none with the remaining probability. No two offsets at the same prime can be hit. Apply the actual deterministic first-cover indicator to the resulting packet occupancy counts, and write \(\mathfrak c=\Pr(C=1)\). The standard greedy computation gives \(1-\mathfrak c=O(L^{-M/200})\). Unlike independence among offsets, independence among the primes is used only in this CRT reference law.

Put \(f_C(n)=C(n)f(n)\). For every fixed \(E>0\), the true marked source has the separate Fourier approximation
\[
S_{f_C}(a/q+\beta)=
\mathfrak c\frac{\mu(q)}{\varphi(q)}
 \int \phi(t/P)(\log t)(D_2(t)-3D_3(t))e(\beta t)\,dt
 +O_E(PL^{-E})
\tag{4}
\]
on the indicated major arcs. Here the prime source restriction is on its final genuine factor only, the true \(C(n)\) is kept, and (4) is **not** deduced from a signed comparison on paired target rows.

To prove (4), again fix the prior genuine label product \(d\) and put \(n=d r\), \(r\) the true final prime. For each \(j\), let \(a_j\) be the complete \(\mathcal B_*\)-smooth part of \(jP-dr\), including powers. Truncate all \(a_j\le\exp(L^{.27})\). **Pay the actual tail globally in the integer \(n\)**: for each possible larger packet-smooth \(a_j\le(M+1)P\), the number of \(n\in(0,P]\) with \(a_j\mid jP-n\) is \(O_M(P/a_j)\), since \(jP-n\) is positive and \(\le(M+1)P\). Rankin with exponent \(1/(2L^{.2})\) gives total \(O_A(PL^{-A})\), even with fixed log weights (Euler reciprocal product polylog, exponent gap \(.27-.2\)). Each true source \(n\) has at most one ordered factorization within each designated class, so there is no extra \(d\) multiplicity. This global step is needed; using a per-\(d\) floor sum over large \(a_j\) much bigger than \(P/d\) would not justify the tail.

For a retained tuple, the exact selector \(C\) is already determined by \(a_2,\ldots,a_{M+1}\). Open that these parts are complete by a factorial Bonferroni test through \(O_{A,M}(\log L)\) distinct primes on each quotient \((jP-dr)/a_j\). Thus the true modulus for its slot is \(a_j e_j\), not a least common multiple of \(a_j,e_j\) when they share primes. Across different \(j\) the slot moduli are coprime on any possible row, because a common packet prime would divide \((j-j')P\), which is impossible. Also every packet prime exceeds the small rational denominator \(q\le Q\); and \(d\) is coprime to all these primes. Impose \(r\equiv r_0\bmod q\) with \((r_0,q)=1\). The CRT gives one reduced class modulo \(q\prod_j a_j e_j\), since the packet residues are \(r\equiv jP d^{-1}\) on each slot and all are units. This is an actual whole prime progression at endpoint \(X=P/d\), with modulus \(P^{o(1)}\) safely below ordinary prime BV there; \(X\) is polynomial for every retained source label.

Uniformly in \(q,r_0\) and the actual moving endpoints of \(r\), the weighted prime BV pays this model to \(O_A(XL^{-A})\) per \(d\). In the modulus loop a prime power has only a bounded choice of slot and its possible \(e_j\)-flag, so grouping coefficients are bounded by a fixed \(C_M^{\omega(q\prod a_j e_j)}\). Use the standard Cauchy argument from [the exact shifted profile proof](SmallRadicalTranslatedTagTypeI.md) to absorb this weight, at the cost of requesting more ordinary log saving. The floor sums on all **retained** profile and sieve variables are \(P^{o(1)}\) for fixed \(d\). Their first omitted shells have factorial-small reciprocal mass because \(\sum_{\ell\in\mathcal B_*}1/\ell=O(\log L)\), and the other reciprocal sums have only fixed log powers. The fact that \(e_j\) can divide \(a_j\) changes no floor estimate: the exact progression modulus is their product on that slot. Sum per-\(d\) errors through \(\sum_d1/d=O(1)\), and arbitrary fixed log variation from the source Fourier weight by partial summation. These facts justify the true weighted expansions, not just a formal profile probability.

The model conditional on \(r_0\bmod q\) is independent of that reduced class: its usual prime denominator factors as \(\varphi(q)\varphi(\prod a_j e_j)\). At a fixed packet prime the \(M\) residues \(jP d^{-1}\) are distinct nonzero residues, establishing exactly the above first-hit law. If one keeps the valuations before forming occupancy indicators, the probability of a fixed \(j\) having valuation at least \(k\) is \(1/\varphi(\ell^k)\); no simultaneous valuations at two distinct offsets are allowed at that prime. The model profile truncation is again superlog-small by Rankin and this tail. Thus summing the actual selector weight in the model gives precisely \(\mathfrak c/\varphi(q)\) times the unmarked interval main, independent also of the prior label \(d\). The reduced rational sum is then \(\mu(q)\) exactly as in (3), and the same real integration over the earlier true primes completes (4).

Combining (4) with the unmarked \(S_g\) estimate proves the genuine **marked** major term equals \(\mathfrak c\) times the right hand leading term of (1), plus \(O(PS(P)/L^2)\). In particular it is still strictly positive and order \(PS(P)/L\) for every fixed \(M\) for which the genuine greedy cover is defined. This is separate from a possible minor cancellation and does not estimate the whole marked restricted mixed coefficient.