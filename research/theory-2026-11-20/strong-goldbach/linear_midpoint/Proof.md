# Absolute disappearance of a first-order smooth midpoint error against a rough reflected row

Let \(P\) tend to infinity through even integers, \(I=[P/3,2P/3]\),
\(X=P/3,\ L=\log P,\ r=P-n\), and let \(\mathfrak S(P)\) be the binary
singular series. Write \(D_F(n)=(\log n)\sum_{d\mid n}\mu(d)F(\log_n d)\).
Fix a real-valued compactly supported Gevrey function \(\Psi\) of order 2 on \([-1,1]\):
its derivatives satisfy \(\|\Psi^{(m)}\|_\infty\le C^{m+1}(m!)^2\).
For \(0<\delta<1/1000\) put
\[
 b_\delta(x)=\delta\,\Psi((x-1/2)/\delta).
\]
No vanishing or parity at the center is needed. For any fixed
\(0<\eta<1\) and arbitrary, possibly target-dependent weights with
\(|T(P-n)|\le L1_{P^-(P-n)>P^\eta}\), we have
\[
 \limsup_{\substack{P\to\infty\\2\mid P}}
 \frac{\sum_{n\in I}|D_{b_\delta}(n)T(P-n)|}{X\mathfrak S(P)}
                    \ll_{\eta,\Psi}\delta^{.03}                         \tag{1}
\]
for all sufficiently small \(\delta\). First fix \(\delta\), then take the
limsup. This is an absolute fixed-target deletion, not cancellation
among different values of \(T\).

In particular let \(\chi\) be an even Gevrey-2 cutoff, supported in
\([-1,1]\) and identically 1 near zero. Such plateau functions follow by
integrating and rescaling compact Gevrey-2 bumps (e.g. products of
\(\exp(-1/x)\) on positive half-lines). Put
\[
 R_e(z)=z(1-\chi(z/e)),\qquad
 Q_e(n)=\frac{\log n}{2}\sum_{d\mid n}\mu(d)R_e(1-2\log_n d).
\]
The unsmoothed full linear multiplier equals \(\Lambda(n)\) exactly,
since \(\sum_{d\mid n}\mu(d)\log d=-\Lambda(n)\) for \(n>1\).
Consequently \(Q_e\) converges to the actual prime weight
\(V(n)=1_{n\ {\rm prime}}\log n\) in the reflected absolute seminorm
in (1), with error \(O_{\eta,\chi}(e^{.03})\): take \(\delta=e/2\)
and the fixed shape proportional to \(s\chi(s)\). The difference between
\(\Lambda\) and \(V\) contributes \(P^{1/2+o(1)}\).
On squarefree inputs \(Q_e\) is the odd-rank half of the smooth one-sided
weight \(D_{a_e}\), \(a_e(x)=R_e(1-2x)1_{x<1/2}\); this weight vanishes
in an open neighborhood of the critical point \(1/2\). This is a
physical approximation result for a pure-prime selector. It is not
a pointwise minorant, nor a strictly positive lower bound for the
prime-prime correlation. Its purpose is specifically to overcome the
first-order central-tail loss in absolute value.

## 1. The rank split and collection of the very small primes

We may omit nonsquarefree and target-nonunit \(n\) at error
\(o_{\eta,\delta}(X\mathfrak S(P))\) for each fixed \(\delta\).
Indeed the smooth physical multiplicative estimate in
[the midpoint rank-window proof, §§1–2](../midpoint_rank_window/Proof.md)
allows omitting \(P^-(n)\le P^\alpha\) at cost
\(O_{\eta,\delta}(\alpha^{1/2}X\mathfrak S(P))\); squareful
\(P^\alpha\)-rough \(n\) cost \(P^{1-\alpha+o(1)}+P^{1/2+o(1)}\).
If \(p\mid(n,P)\), it also divides \(r\) and must exceed \(P^\eta\).
Send \(\alpha\downarrow0\) at fixed \(\delta\).

Write \(s=\log(1/\delta)\). For \(\omega(n)\le 1.6s\) use the lower
collar argument from §3 of the same proof with \(b=.8\), retaining the
extra amplitude \(\delta\). In detail, split off primes \(\le P^\delta\);
the opened larger divisor must lie in an exponent collar of width
\(O((1+s)\delta)\) around \(1/2\). Mark the rank by
\(b^{\omega(n)-\lfloor1.6s\rfloor}\). The reciprocal sum over larger
divisors in the collar is \(O_b((1+s)\delta^{1-b})\) by the one-form
rough bound on each dyad, and the remaining two-form upper bound costs
\(O_{\eta,b}(\delta^{-b})\) after the small-prime Fourier differences.
Those estimates use \(0<b<1\); \(b<1/2\) was needed only to obtain a
positive exponent for bumps of *unit* height. Here the resulting
normalized bound is
\[
 O_{\eta,\Psi}((1+s)\delta^{2-2b-1.6\log(1/b)})=O(\delta^{.03}).
\]
The exponent is \(0.4-1.6\log(1.25)>.042\). At \(\omega(n)\ge 4s\)
the high-rank Fourier argument in §4 of the cited proof with \(B=e\)
and \(\epsilon=.01\) costs \(O_{\eta,\Psi}(\delta^{1+4-e(4/\pi+.01)})\).
Both estimates apply to this fixed Gevrey shape, with no rank-parity
assumption. Rounding ranks at the endpoints only changes constants.

Set \(K=\lceil4s\rceil\). On the remaining inputs put
\(h=\prod_{p\mid n,\ p\le P^\delta}p,\ N=n/h\), so \((h,N)=1\),
\(P^-(N)>P^\delta\) (use \(P^-(1)=\infty\)),
\(\omega(h)\le K,\ h\le P^{K\delta},\ (h,P)=1\).
Shrink \(\delta\) at the outset so that \((K+3)\delta<.004\).
Set \(\gamma=1/4\) and
\[
     w(h)=\prod_{p\mid h}(\log p/(\delta L))^\gamma,\qquad w(1)=1.
\]
On the remaining physical rows Cauchy gives the product of square roots of
\[
 M=\sum |T(r)|w(h), \qquad
 E=\sum |T(r)|\, |D_{b_\delta}(n)|^2/w(h).
\]
For \(M\), use \(1\le2^{\omega(n)-1.6s}\).
The two-form Henriot bound on \(N,P-hN\) over length \(X/h\) gives
\[
 M\ll_\eta \frac{X\mathfrak S(P)}L \delta^{-2+1.6\log2}
          \sum_h\frac{h}{\phi(h)}\frac{2^{\omega(h)}w(h)}h
 \ll_\eta \frac{X\mathfrak S(P)}L \delta^{-2+1.6\log2}.                \tag{2}
\]
Indeed the prime weight \(2\,1_{p>P^\delta}\) on \(N\) has prime reciprocal
sum at most \(2\log(1/\delta)+O(1)\). In the raw local sum for the two
forms positive exponents on both forms are possible only at \(p\mid P\);
at \(p\le P^\eta\) their weights vanish, and at the \(O_\eta(1)\) larger
target primes they give bounded factors. The root-count prefactor is
\(O(\mathfrak S(P)h/(\phi(h)L^2))\), as in the rank-window proof, also
for non-rough squarefree \(h\): off primes of \(P\), changing two roots
to one at \(p\mid h\) gives \((p-1)/(p-2)\ll p/(p-1)\) with the product
of the ratios absolutely bounded. The coefficient-height hypothesis
is uniform since \(X/h\gg P^{.99}\).
Finally \(\sum_{p\le P^\delta}(\log p/(\delta L))^\gamma/p=O_\gamma(1)\)
by partial summation. The factor \(h/\phi(h)\) does not spoil convergence.

We show
\[
                  \limsup_{P\to\infty} \frac{E}{XL\mathfrak S(P)}
                                      \ll_{\eta,\Psi}\delta .             \tag{3}
\]
Then (2) and (3) yield a middle-rank saving of exponent
\((1.6\log2-1)/2>.054\), which suffices.

## 2. The conditional-energy comparison at the critical support

Choose \(0<\sigma<\min(\eta/2,.0005)\) fixed and a nonnegative smooth
\(\rho\), compactly supported on the real line, with \(\rho(0)=1\) and
support on the positive side in \([0,\sigma]\).
For the actual rough \(r\) the short sum
\[
       V_h(r)=\sum_{\substack{c\mid r\\ \gcd(c,Ph)=1}}\mu(c)\rho(\log_P c)
\]
equals 1; on every input \(V_h^2\) is nonnegative. Freeze
\(a=\log n/L\) at any point of each of \(O(L^B)\) physical intervals
of length \(O(P/L^B)\) in \(I\), with fixed \(B=B(\delta)\) sufficiently
large. Put
\[
 F(v)=a b_\delta(v/a),\quad
 F_h(v)=\sum_{b\mid h}\mu(b)F(v+\log_P b).
\]
Then \(D_{b_\delta}(hN)=L\sum_{d\mid N,(d,h)=1}\mu(d)F_h(\log_P d)\)
on the original squarefree rows, up to \(O_\delta(L^{-B}\tau(n))\).
Freezing in \(E\) costs \(o_\delta(P)\) on taking \(B\) sufficiently large:
\(1/w(h)\ll_{\delta,K}L^{\gamma K}\), and absolute fixed divisor moments
of \(n,r\) are polylogarithmic by Cauchy. We may now drop all restrictions
on \(N\) except the physical interval, keeping the square and the
restriction \((d,h)=1\) inside it. Thus an upper bound, apart from
\(o_\delta(P)\), is \(L^3\) times
\[
 \sum_{J,h}\frac1{w(h)}
 \sum_{hN\in J}
 \left(\sum_{\substack{d\mid N\\ \gcd(d,h)=1}}\mu(d)F_h(\log_P d)\right)^2
 V_h(P-hN)^2.                                                        \tag{4}
\]
Only the indicated squarefree \(h\) of §1 are summed; different terms
may now count the same integer and that is harmless.

We may replace the actual congruence counts in the opened (4) by their
CRT densities, in total with error \(O_{\delta,A}(PL^{-A})\) for any
fixed \(A\), **including the divisors at the square-root boundary**.
Here is the critical verification. With \(d,e\) from the first square
and \(c,c'\) from the second set \(g=(d,e),\ q=[c,c']\). Then
\((q,Ph)=1\). A contribution is possible only for \((q,[d,e])=1\),
in which case the model is \(|J|/(h[d,e]q)\). Each \(q\le P^{2\sigma}\)
carries total coefficient bounded by \(\|\rho\|_\infty^2\,3^{\omega(q)}\).
Also every active \(d,e\) lies between \(P^{.5-(K+2)\delta}\) and
\(P^{.5+2\delta}\) for large \(P\). For \(g>P^{.05}\), each floor error
is \(O(1)\), and the number of ordered pairs \(d,e\) is
\(O(P^{1+4\delta-.05})\) by summing \(\lfloor P^{.5+2\delta}/g\rfloor^2\).
Even after the \(P^{K\delta}\) choices of \(h\), the \(O(P^{2\sigma})\)
pairs \(c,c'\), the intervals and \(1/w(h)\), this saves a fixed power.
Constants depending on \(K,\delta\) here and in the remaining rail are
irrelevant at fixed \(\delta\).

For \(g\le P^{.05}\) the actual and modeled contributions are **separately**
arbitrary-log small. Set \(d=gu,e=gv,(u,v)=1\); the physical input
is \(n=hgmuv\), where \(m\le P^{.05+2(K+2)\delta}\), and
\(u,v\ge P^{.44}\). Dyadically split \(u,v\) into \([U,2U],[V,2V]\);
there are only log-power many boxes and a nonempty physical box has
\(UV\asymp P/(hgm)\).
The Möbius coefficients are \(\mu(g)^2\mu(u)\mu(v)\) with the necessary
coprimalities, in particular \((u,ghv)=1\) and \((v,gh)=1\).
Also \((g,h)=1\). If \((q,hgmv)>1\) the actual interval is empty;
otherwise the condition on \(u\) is a single unit residue modulo \(q\)
depending on \(h,g,m,v\). For fixed \(h,g,m,v\),
the interval in \(u\) is cut by \(hgmuv\in J\), and the remaining
\(u\)-weight \(F_h(\log_P(gu))\) has bounded supremum and variation
\(O_\delta(2^K)\). This allows maximal-prefix estimates by partial
summation, without treating the two prime-factor length constraints
as independent after \(v\) is fixed.

To impose \((u,ghv)=1\) expand it as \(\sum_{a\mid(u,ghv)}\mu(a)\).
Terms with \(a>L^C\) cost \(O_{\delta,A}(PL^{-A})\) after summation,
for large \(C=C(A,\delta,B)\). Indeed \(a^2\mid n=hgmuv\), so the
union of such rows has size \(O(P/L^C+\sqrt P)\), by summing \(P/a^2+1\).
The number and absolute weight of expanded labels at one physical \(n\)
are bounded by \(L^{O_\delta(1)}\tau(n)^{O(1)}\tau(P-n)^{O(1)}\);
\(h,g,m,u,v,a\) are divisor labels, and \(c,c'\) divide \(P-n\).
Cauchy and the elementary fixed divisor moments suffice; even a redundant
factor \(L^B\) is allowed. No squarefreeness of the enlarged \(n\) is
being assumed here. For \(a\le L^C\), put \(u=au'\). Nonzero Möbius
terms have \((u',a)=1\). If \((a,q)>1\) the progression is empty;
otherwise this condition gives at most \(a\) unit classes modulo \(qa\).
In each of them the remaining arithmetic coefficient is \(\mu(u')\).

The ordinary [maximal-prefix Bombieri–Vinogradov estimate for Möbius, (3.1)](https://arxiv.org/html/2610.20242v2#S3) now gives,
uniformly in all fixed labels, summed over \(q\), an error
\(O_{\delta,A}(U L^{-A})\), with arbitrary additional log saving available.
For clarity, \(qa\le P^{.002}\) for large \(P\), far below
\((U/a)^{1/2}/L^{B'}\) for any fixed \(B'\). In the *raw* unit-progression
version the reduced mean is also negligible: uniformly for \(b\le P^2\)
and \(Y\ge P^{.2}\), \(\sum_{n\le Y,(n,b)=1}\mu(n)\ll_A YL^{-A}\)
by \(\mu1_{(\cdot,b)=1}=\mu*1_{m\mid b^\infty}\), PNT, and the convergent
tilted auxiliary mass
\(\sum_{m\mid b^\infty}m^{-1+1/\log L}\ll(\log L)^{O(1)}\);
smaller prefixes may be bounded trivially at the scale \(U/a\).
The divisor factor \(3^{\omega(q)}\) is harmless by Cauchy between
arbitrary BV log savings and the trivial \(O(U/(qa)+1)\) bound with
\(9^{\omega(q)}\). Factors \(a\le L^C\), the number of classes, and
the fixed interval partitions are paid with further log savings.
Sum trivially over \(v\asymp V\), and use \(UV\ll P/(hgm)\);
the harmonic sums over \(h,g,m\) cost at most \(O(L^3)\).
This proves the physical small-\(g\) assertion.

For its model there is no \(m\) or residue constraint; the inner sum in
\(u\) has weight \(\mu(u)F_h(\log_P(gu))/u\) on a long dyad with
\((u,ghvq)=1\). Apply the preceding uniform coprime PNT and partial
summation directly. The other variables have harmonic denominators
\(h,g,v,q\); their log-power losses are absorbed. This proves the claimed
physical-to-CRT comparison. This use of the switched long Möbius
variable is necessary: a floor estimate on *all* \(d,e,c,c'\) would
exceed the available interval.

## 3. The CRT energy and the uniform first-order gain

For each \(J,h\) its CRT contribution (without the outside \(L^3/w(h)\))
is
\[
 \frac{|J|}{hL^2}\,\mathfrak S(P)\,C(h)
 \int_0^\infty |F_h'(x)|^2dx\int_0^\infty|\rho'(x)|^2dx
 \quad+\quad\text{summably negligible error},                       \tag{5}
\]
where \(C(h)=\prod_{p\mid h}(1-2/p)^{-1}\); \(h\) is odd, \((h,P)=1\).
Here 'summably negligible' means \(o_\delta(XL\mathfrak S(P))\) after
the \(L^3/w(h)\) weights and the sum over \(J,h\).
We verify the uniformity; the basic computation is the smooth
divisor-sum Euler calculation of
[D. H. J. Polymath, Lemma 4.1 and (38)–(40)](https://arxiv.org/html/1407.4897v3#S4), but the
actual-to-model switch above and the uniform small-prime differences
must also be accounted for.

For Fourier inversion use \(f(x)=\int \mathcal T_f(t)e^{-(1+it)x}dt\)
on the real line, so \(s_i=(1+it_i)/L\). With
\(A_p=-p^{-s_1}-p^{-s_2}+p^{-(s_1+s_2)}\) and \(B_p\) the same on
indices \(3,4\), the local density series is \(1+(A_p+B_p)/p\) at
\(p\nmid Ph\), \(1+A_p/p\) at \(p\mid P\) (the second sieve excludes
it), and 1 at \(p\mid h\) (both divisor sums exclude it).
The \(p\nmid Ph\) formula uses disjoint roots; in particular it has
no \(A_p B_p/p^2\) term. Divide the Euler product by
\[
  \frac{\zeta(1+s_1+s_2)}{\zeta(1+s_1)\zeta(1+s_2)}
  \frac{\zeta(1+s_3+s_4)}{\zeta(1+s_3)\zeta(1+s_4)} .
\]
The remaining product at zero is exactly \(\mathfrak S(P)C(h)\):
at \(p\nmid Ph\) its factor is \((1-2/p)/(1-1/p)^2\);
at \(p\mid P\) it is \((1-1/p)^{-1}\), and at \(p\mid h\)
it is \((1-1/p)^{-2}\).
For \(\max|t_i|\le L^{.02}\) the product differs from this value by
\(O(L^{-.9}(\log L)^{O(1)})\), uniformly in \(P,h\).
Indeed the ordinary local residual has derivative
\(O((\log p)/p^2)\) on the nonnegative-real-part polydisk near the
imaginary origin (expand the first-order cancellation), and the
exceptional local residuals have derivatives \(O((\log p)/p)\) and
size \(1+O(1/p)\). The finitely many smallest primes have uniformly
bounded local factors and derivatives: when an undivided root factor
vanishes, use the product rule, not logarithmic differentiation.
Moreover \(\sum_{p\mid Ph}(\log p)/p=O(\log L)\) and
\(\prod_{p\mid Ph}(1+C/p)\ll(\log L)^{O_C(1)}\), by splitting at \(L^2\).
The pole expansions of each displayed zeta ratio uniformly give
\((s_i s_j)/(s_i+s_j)\) times \(1+O(L^{-.9})\).
The elementary identity
\[
 \frac{(1+it_i)(1+it_j)}{2+it_i+it_j}
    =\int_0^\infty (1+it_i)(1+it_j)e^{-(2+it_i+it_j)x}\,dx
\]
then gives the derivative energy in (5). All four Fourier integrals
are over full real frequencies.

We explain why no divergent mass from \(1/w(h)\) is lost in these
expansions. The transform of \(F_h\) is that of \(F\) times
\(\prod_{p\mid h}(1-p^{-(1+it)/L})\). For real \(t\), \(q_t=\delta(1+|t|)\),
elementary partial summation gives
\[
 \sum_{p\le P^\delta}\frac{1+O(1/p)}{p\,w(p)}
       |1-p^{-(1+it)/L}|^2
       \ll_\gamma (1+q_t)^\gamma .                                   \tag{6}
\]
Indeed with \(v=\log p/(\delta L)\) the summand shape is bounded by
\(v^{-\gamma}\min(4,C q_t^2v^2)\). Split at \(v=\min(1,1/q_t)\);
on the lower portion use the Chebyshev log-moment bound and on the
higher portion sum reciprocal primes in geometric \(v\)-bands.
The same proof works when that split lies below the least prime, and
with phase \(p^{it/L}\) instead. Constants in (6) do not grow with
\(\delta\) for \(P\) sufficiently large at fixed \(\delta\).
By Euler multiplication and Cauchy, the two transforms of \(F_h\)
can therefore be summed against \(C(h)/(h w(h))\), at a cost bounded by
\(\exp(C(1+q_{t_1})^\gamma+C(1+q_{t_2})^\gamma)\) multiplying the
two unshifted transforms. It is also valid without \(C(h)\).
The Gevrey bound, by repeated integration by parts and optimizing
the derivative order, gives
\(|\mathcal T_F(t)|\ll_\Psi \delta^2 e^{-c_\Psi|\delta t|^{1/2}}\)
uniformly for all the central \(a\); multiplication by \(e^x\)
and dilation \(a=1+O(1/L)\) preserve these bounds. Since \(\gamma=1/4\),
all frequency-polynomial losses are integrable for fixed \(\delta\).
The two transforms of \(\rho\) are Schwartz. Beyond \(L^{.02}\) in
any frequency the absolute original density series is \(O(L^{C})\)
by the Euler product at real parts \(1/L\); the Fourier tails after (6)
give arbitrary log savings there. These facts justify the stated
summable error in (5), including after summing the physical lengths
\(\sum_J|J|=X\).

Finally apply ordinary Fourier Plancherel on the entire real line to
upper-bound the first half-line energy in (5). The usual transform of
\(F'_h\) is \(it\widehat F(t)\prod_{p\mid h}(1-p^{it/L})\) up to the
irrelevant Fourier sign. The same uniform Gevrey bound holds for
\(\widehat F\). Using (6) and enlarging the \(h\)-sum by positivity gives
\[
  \sum_h\frac{C(h)}{h w(h)}\int_0^\infty|F_h'(x)|^2dx
   \ll \delta^4\int_{\mathbb R} t^2
       \exp(-c|\delta t|^{1/2}+C(1+\delta|t|)^{1/4})\,dt
   \ll_\Psi \delta .                                                    \tag{7}
\]
Combining (4), (5), and (7) proves (3), and finishes the proof of (1).

**Scope.** The amplitude \(\delta\) is essential here. The result does
not show that a unit-height shrinking midpoint bump has negligible
physical mass. The roughness of the reflected row is fixed before
\(\delta\downarrow0\); the constants do not justify substituting a
shrinking \(\eta(\delta)\) without additional estimates. Conditional
squared energy alone would bound the first moment by
\(O(X\mathfrak S(P)\sqrt{L\delta})\), not by \(o(X\mathfrak S(P))\);
the headcount (2) is part of the proof. No sign or positivity for
\(\sum V(n)V(P-n)\) is asserted.

**Comparison.** The prior [balanced-triprime rank window](../midpoint_rank_window/Proof.md)
uses a unit-height shoulder and leaves a logarithmically growing range of ranks;
it supplies the two edge estimates here but not the conditional quadratic
energy. The [finite polynomial minorant obstruction](../PolynomialPrimeMinorantBoundary.md)
concerns globally signed minorants, not approximation in the indicated
fixed-rough seminorm. Recent related work includes [Arneth's October 2026
cubic minorant](https://zenodo.org/records/23477014) on rough integers and
[Pham's October 2026 v1](https://www.preprints.org/manuscript/202610.3061)
on a different comparison of shifted prime and rough rows. Neither is
used as a distribution input. The November [Bahbouhi rough-complement
identities](https://www.preprints.org/manuscript/202611.0975) likewise do not
supply the absolute shrinking-shoulder estimate. No priority is asserted.
