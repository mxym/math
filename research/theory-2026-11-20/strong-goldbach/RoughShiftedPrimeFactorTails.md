# Two disjoint largest-factor populations at every even prime-reflection target

There is an absolute fixed \(\epsilon>0\) such that every sufficiently large even \(P\) has \(\gg P\mathfrak S(P)/(\log P)^2\) true primes \(p\in[P/3,2P/3]\) in **each** of the following disjoint sets. In both, \(r=P-p\) is squarefree, composite and \(P^-(r)>P^\epsilon\); in the first \(P^+(r)\le P^{0.455}\), and in the second \(P^+(r)>P^{0.60}\). In particular the first always has at least three prime factors and both have at most \(\lfloor1/\epsilon\rfloor\). Here \(\mathfrak S(P)=2C_2\prod_{l\mid P,l>2}(l-1)/(l-2)\) is the standard even binary singular series.

This is about the distribution of **actual prime complements** at a prescribed macroscopic reflection, not the density averaged over targets. It does not say that any complement is prime, assign a sign to Pan's weight on either family, or resolve binary Goldbach. The method is a first-moment Chebyshev/sieve argument, not an invocation of a conjectural distribution of all factor sizes.

## 1. The measure and sub-square-root prime marks

Write \(L=\log P, I=[P/3,2P/3], X=P/3,z=P^\epsilon\), and give central primes \(p\) with \(r=P-p\) \(z\)-rough weight \(\log p\); write \(A\) for the total and \(\mathbb E\) for its normalized expectation. We may restrict to squarefree \(r\) in this measure and in all arguments: non-squarefree rough \(r\) cost \(O(PL/z)\) in log-weight, negligible even when multiplied by any fixed power of \(L\). For large \(P\), no central prime divides \(P\), with at most \(O(L)\) exceptions which may be discarded; then \((p r,P)=1\). Put
\[
 V_0=\prod_{l\le z}(1-1/l),\qquad V_1=\prod_{l\le z,l\nmid P}(1-1/(l-1)),\qquad
 V_2=\prod_{l\le z}(1-\nu_l/l),\quad \nu_l=\begin{cases}1&l\mid P,\\2&l\nmid P.\end{cases}
\]
The prime 2 divides \(P\). Direct local division gives \(V_j=(1+o_\epsilon(1))\mathfrak S(P)V_0^j\) for \(j=1,2\), and \(V_0\sim e^{-\gamma}/(\epsilon L)\), uniformly in \(P\) (the tail in \(\sum_{l>z,l\mid P}1/l\) is \(O(L/z)\)).

We use the following convenient order of limits: fix an arbitrarily small tolerance, then small fixed reserves \(\tau,\delta>0\), then \(\epsilon\) sufficiently small relative to them, and finally \(P\) large. Below \(o_*(1)\) denotes errors tending to zero in this ordered sense, not for a prescribed large \(\epsilon\). In particular all parameters can be fixed once and for all before \(P\to\infty\).

Let \(t_l=\log l/L\). For \(h<1/2\) a fixed distance below the BV endpoint (distance \(\delta\) is allowed), define \(H_h(r)=\sum_{z<l\le P^h,l\mid r}t_l\). The genuine shifted-prime measure has
\[
 A=(1+o_*(1))XV_1,\qquad \mathbb EH_h=h-\epsilon+o_*(1).            \tag{1}
\]
More generally the expected number of labeled prime factors in any fixed exponent window \([a,b]\subset(0,1/2-\delta]\), each weighted by a nonnegative Riemann-integrable function \(f(t_l)\), is \(\int_a^b f(t)dt/t+o_*(1)\) for bounded fixed test functions used below. To prove these statements, sieve \(r=P-p\) at primes \(l\le z,l\nmid P\) on the base of log-weighted primes \(p\in I\). These are single forbidden unit classes modulo each prime. With an extra marked prime \(d\) in \((z,P^h]\), the class is \(p\equiv P\bmod d\); no prime \(d\mid P\) can occur apart from discarded target prime labels. For a small sieve divisor \(e\) the new class is \(P\bmod de\), with unique rough-times-smooth modulus and main \(X/\phi(de)\). Use upper and lower fundamental-lemma weights with \(D=P^{\delta/2}\) for all \(h\le1/2-\delta\): all BV moduli are below the square root by a fixed power. Sum remainders over all the marked primes by maximal-residue BV, also for both endpoints of \(I\); possible target prime labels can alternatively be removed per modulus at cost \(O(P^{1/2-\delta/2}L^2)\). The normalized relative sieve error is \(O(e^{-\delta/(2\epsilon)})\), multiplied only by the harmonic mass of the marks with their indicated weights. This mass is bounded for the fixed positive exponent windows, and uniformly bounded for the whole \((\epsilon,h]\) when the mark is \(t\), since \(\sum_{l\le Y}(\log l)/l=\log Y+O(1)\). Mertens/PNT evaluates the remaining marked sums; prime divisors of \(P\) above \(z\) make a negligible harmonic change. This proves (1). One reference for the beta-sieve statement and its product dimension hypothesis is [Kurlberg–Lester–Rosenzweig, §2.1, Thm 2.2](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136); (2.5) there holds uniformly because the worst local factors differ from the Mertens factors of dimension 1 or 2 by \(1+O(l^{-2})\) for \(l\ge3\).

## 2. An upper bound for intermediate marked primes

For a bounded nonnegative piecewise continuous test \(f\) on a fixed interval \([a,b]\subset[.45,.62]\), we have
\[
 \mathbb E\sum_{a<t_l\le b,l\mid r}f(t_l)
 \ \le\ \int_a^b \frac{2f(t)}{t(1-t)}\,dt+o_*(1).              \tag{2}
\]
Unlike (1), this includes primes above the square root. Write \(r=l m\), \(Y=P/l\); the physical interval for \(m\) has length \(X/l+O(1)=Y/3+O(1)\). The case \(l\mid P\) has no central prime solutions for sufficiently large \(P\), since then \(l\mid p\) and \(l<P/3\). We need \(m\) rough and \(P-lm\) prime. At primes \(s\le z\) sieve **both** forms, whose local densities are the \(\nu_s/s\) in \(V_2\); at primes \(z<s\le W_l=Y^{1/2}P^{-\tau}\) sieve only \(P-lm\), with density \(1/s\). The large mark \(l>W_l\) never degenerates these linear forms. Central primes are above \(W_l\). Use respectively a dimension-two upper beta sieve of level \(D_0=P^\tau\), and a dimension-one upper **linear** sieve of level \(D_{1,l}=W_l^2\). The two divisor supports use *disjoint* sets of primes. Each upper convolution is pointwise at least its zero–one indicator, hence **nonnegative**; their product is a pointwise upper bound. For fixed divisor pair \((d,e)\) in these supports CRT contributes
\((X/l)\prod_{s\mid d}(\nu_s/s)/e+O(2^{\omega(d)})\). The sum of absolute errors, with bounded sieve coefficients, is \(O(D_0D_{1,l}L^{O(1)})=O(Y P^{-\tau}L^{O(1)})\); even after summing over all \(l\) and inserting \(\log p\le L+O(1)\), the result is \(o(A)\). Indeed \(\sum_{P^a<l\le P^b}1/l=O(1)\). No estimates for primes in a single supercritical progression have been assumed.

The local main factors now **separate**. For the small sieve the product factor is at most \((1+O(e^{-\tau/\epsilon}))V_2\). For the large sieve it is at most
\[
 (F_1(2)+o(1))\prod_{z<s\le W_l}(1-1/s)
   =(e^\gamma+o(1))\frac{\log z}{\log W_l}.
\]
Here \(\log D_{1,l}/\log W_l=2\) and the dimension-one linear-sieve upper function is \(F_1(s)=2e^\gamma/s\) for \(1\le s\le3\). This uses the **upper-sieve main sum** bound for the weights, e.g. [Friedlander–Iwaniec, *Opera de Cribro*, Chapter 11, Theorem 11.12](https://www.ams.org/books/coll/057/). The dimension bound holds for the interval of primes \((z,W_l]\) with an absolute dimension constant by taking the full prime set as an upper bound; the Mertens estimate is uniform over these \(W_l=P^{(1-t_l)/2-\tau}\) with \(t_l\in[.45,.62]\). Dividing each mark's result by \(A\sim XV_1\) in the stated limits pays
\[
 (1+o_*(1))\frac{L}{l}\frac{V_2}{V_1}\,e^\gamma\frac{\log z}{\log W_l}
 = \frac{1+o_*(1)}{l((1-t_l)/2-\tau)} .
\]
The \(e^\gamma\) cancels rather than multiplying the final constant. Let the fixed reserve \(\tau\) be small enough for the given tolerance; summing \(1/l\) by Mertens proves (2). The constant bounds concern the entire sum and do not use BV past \(P^{1/2}\).

**Independent verification of the needed large-sieve main constant.** Instead of using the linear-sieve main-sum theorem, take the Selberg square majorant on \(z<s\le W=W_l\) with divisor cutoff \(W\). Its optimized main quadratic form is exactly \(1/G(W;z)\), where
\[
G(W;z)=\sum_{d\le W,\ P^-(d)>z}\frac{\mu^2(d)}{\phi(d)}
\quad(d=1\text{ included}).
\]
See the [classical Selberg-square derivation](https://people.math.harvard.edu/~elkies/M259.02/sieve.pdf). The individual optimal divisor weights have absolute value at most 1: for squarefree supported \(d\), the numerator in their absolute value is \((d/\phi(d))\sum_{n\le W/d,(n,d)=1,P^-(n)>z}\mu^2(n)/\phi(n)\), at most \(G(W;z)\) by expanding \(d/\phi(d)=\sum_{a\mid d}1/\phi(a)\) and injecting each pair as \(an\). Consequently the total CRT error is still \(\ll D_0W^2 L^{O(1)}\) via the two independently bounded divisor indices in the square.

For fixed \(k=\log W/\log z\) the prime factor expansion and Mertens give
\[
G(z^k;z)\longrightarrow B(k)=\sum_{j\ge0}\frac1{j!}
 \int_{\substack{x_i\ge1\\\sum x_i\le k}}\prod_i dx_i/x_i .
\]
The \(j=0\) term is 1; the other terms stop at \(j\le k\), prime repeats are negligible, and exponent-grid Riemann sums give the integral. Convergence is uniform on compact \(k\)-intervals by monotonicity and continuity. The increasing function \(B(k)\), with its unit atom at zero, has Laplace–Stieltjes transform \(\exp(\int_1^\infty e^{-h x}dx/x)\sim e^{-\gamma}/h\) as \(h\downarrow0\). The ordinary Karamata Tauberian theorem for positive measures now gives \(B(k)\sim e^{-\gamma}k\) as \(k\to\infty\). In our two ordered limits \(k=((1-t_l)/2-\tau)/\epsilon\to\infty\) uniformly across the entire window (taking \(P\to\infty\) at fixed parameters first). This recovers \(1/G(W;z)\le(e^\gamma+o_*(1))\log z/\log W\) independently of any finite-\(s\) linear-sieve normalization. The square is manifestly nonnegative pointwise; its product with the small upper convolution needs no sign assumption.

## 3. Two pointwise consequences of the exponent mass

Put \(T=\log P^+(r)/L\), \(v=.455,\ c=.61\). Squarefree \(r\in I\) has total exponent \(\log r/L=1+O(1/L)\), at most 1. The following majorant holds on each retained \(r\):
\[
 H_v(r)\le 1-c+c\,1_{T\le v}
      +\sum_{v<t_l\le c,l\mid r}(c-t_l).                       \tag{3}
\]
For \(T\le v\) the bound is immediate. For \(T>v\), \(H_v\le1-T\); if \(T<c\), the largest factor itself supplies the needed \(c-T\). Intermediate factors can only increase the right side. Take expectations; use (1) for the window from \(v\) to \(.5-\delta\), and (2) from \(.5-\delta\) to \(c\). The transition interval length \(\delta\) has no singular density, so letting the reserves be small gives
\[
 c\Pr(T\le v)\ge v+c-1-I_{\rm lo}-I_{\rm hi}-o_*(1),
\quad I_{\rm lo}=c\log(.5/v)-(.5-v),\quad
 I_{\rm hi}=2\big(c\log(2c)+(1-c)\log(2(1-c))\big).
\]
The right side before the error exceeds \(.0036\). For a rational check of the rounding, for each positive rational argument \(q\) evaluate \(\log q=2\sum_{j=0}^{7}h^{2j+1}/(2j+1)+E\) with \(h=(q-1)/(q+1)\), \(|E|\le2|h|^{17}/(17(1-h^2))\): this gives \(I_{\rm lo}<.012530\), \(I_{\rm hi}<.048799\). Thus the smooth population is a fixed positive share of \(A\).

For the opposite tail take \(b=.60\). The portion of exponent mass below \(.5-\delta\) has expectation \(.5-\delta-\epsilon+o_*(1)\) by (1); the middle mass up to \(b\) is bounded by (2) with mark \(t\), at most \(2\log(.5/(1-b))+o_*(1)\) in the ordered limits. The remaining mass is zero outside \(T>b\), and at most 1 everywhere. Hence
\[
 \Pr(T>.60)\ge .5-2\log(5/4)-o_*(1)>.053-o_*(1).
\]
This tail could a priori contain true prime complements. But the standard two-linear-forms upper sieve gives \(\#\{p,r\in I\text{ prime}:p+r=P\}\ll \mathfrak S(P)P/L^2\) with absolute constant (see, e.g., [Deshouillers–Granville–Narkiewicz–Pomerance, §3, (2)](https://dms.umontreal.ca/~andrew/PDF/GoldbachII.pdf)). Therefore their log-weight is \(O(\epsilon A)\), and taking \(\epsilon\) small leaves a positive share of composites alone. The smooth population is already composite and has at least three prime factors because \(P^{2v}<P/3\). Each log-weight \(\log p\sim L\), so (1) gives the claimed count for both populations.

## 4. Coarser elementary control independent of the linear-sieve constant

As a check, the exponents \(v_0=.498,\ b_0=.52\) require only the arithmetic large sieve above the BV range. For one mark \(l\in(P^{.498},P^{.52}]\), on the same \(m\)-interval remove both local classes at primes \(s\le z\), and only the prime class up to \(W=P^{.10}\). Use the [arithmetic large sieve in its residue-class denominator form](https://ford126.web.illinois.edu/sieve_notes_large_sieve.pdf) with radius \(P^{.20}\). The numerator is \(X/l+O(P^{.40}+1)=(1+o(1))X/l\). In the full Euler-product denominator on primes up to \(W\), normalize the local weights \(\nu/(s-\nu)\) independently; the expected \(\log d\) is \(\sum\nu(\log s)/s\le(.10+\epsilon+o(1))L\). Markov therefore retains at least \(.49\) of the mass at \(d\le P^{.20}\) for all sufficiently small \(\epsilon\). Thus the count is at most \((1+o(1))(.49)^{-1}(X/l)V_2\prod_{z<s\le W}(1-1/s)\). Normalized by \(A\) after the prime weight, this is \(\le(12+o_*(1))/l\), since \(e^{-\gamma}/(.1\cdot.49)<12\). Summing the mark \(t_l\) gives middle mass \(\le12(.52-.498)+o_*(1)=.264+o_*(1)\). Consequently \(h=\Pr(T>.52)\ge1-.498-.264-o_*(1)=.238-o_*(1)\). On that set \(H_{.498}\le.48\); outside it but off the fully smooth class \(H_{.498}\le.502\). If \(g=\Pr(T\le.498)\), then \(.498-o_*(1)\le.502-.022 h+.498g\), forcing \(g\) bounded away from zero. The proper-power and true prime-pair removals are the same as in §3.

**Comparison and limitations.** The log-factor budget and its upper-sieve form are classical; vastly stronger largest-factor *thresholds* are available in some other regimes. [Baker–Harman](https://matwbn.icm.edu.pl/ksiazki/aa/aa83/aa8342.pdf) study a fixed shift, and [Lichtman](https://arxiv.org/abs/2211.09641) obtains a smaller smoothness exponent for prime predecessors. [Baker–Harman on additive representations](https://arxiv.org/abs/2011.10859) study a moving target, with the other summand sublinear, not our central rough population. The OpenAI [prime predecessor PD paper](https://github.com/openai/math/tree/main/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026) treats the fixed shift \(p-1\). [Runbo Li's shifted-prime large-factor work](https://arxiv.org/abs/2508.18285) is another comparison in the large-factor direction. The Nov. 2026 [work on sums of integers with small prime factors](https://arxiv.org/abs/2611.21136) has a different requirement on the other summand. The present features are uniformity for every prescribed even reflection, a true central prime, and a simultaneous polynomial lower factor cutoff on its squarefree complement. No priority or optimality claim is made.
