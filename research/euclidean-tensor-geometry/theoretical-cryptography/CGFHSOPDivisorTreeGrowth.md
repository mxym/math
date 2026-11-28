# A line-by-divisor-tree submonoid and a quantitative HSOP growth bound

Let \(H_n\) denote the number of basic degree-\(n\) cyclotomic generating functions that arise as Hilbert series of weighted polynomial rings modulo a homogeneous system of parameters, the monoid \(\Phi^{\mathrm{alg}}\) of [Billey–Swanson, Problem 62](https://arxiv.org/html/2305.07620v3#S6.SS3). We construct an explicit submonoid \(M\) whose exact Hilbert counting series and logarithmic growth constant can both be computed. Write \(M_n\) for its number of distinct polynomials of degree \(n\). With \(h_p=\prod_{\ell<p,\ \ell\text{ prime}}(1-1/\ell)\), the result is
\[
 \log M_n\sim \pi\sqrt{\frac{2D}{3}}\sqrt n,\qquad
 D=1+2\sum_{p\ge3\ \mathrm{prime}}h_p
          \left(\frac1{p-1}-\frac1{2p-1}\right).
\]
In particular,
\[
 3.32315\ldots=\pi\sqrt{2D/3}\ \le\
 \liminf_{n\to\infty}\frac{\log H_n}{\sqrt n}\ \le\
 \limsup_{n\to\infty}\frac{\log H_n}{\sqrt n}\ \le\
 \frac{\sqrt{105\zeta(3)}}{\pi}=3.57608\ldots .
\]
The upper bound uses the classical count of unrestricted cyclotomic products, whose constant is included below for comparison. This is a quantitative bound for Problem 62, not a determination of the exact full-monoid constant. [Gatzweiler–Levicán-Santibáñez–Yoshida, 2026, Proposition 3.3](https://arxiv.org/abs/2603.22226) solve the different membership problem (Billey–Swanson Problem 60); their criterion is not needed for the family below.

## 1. The monoid and exact Euler product

Write \([m]_q=(1-q^m)/(1-q)\). Every factor \([v]_q/[u]_q\) with \(u\mid v\) is an HSOP Hilbert series: use one variable of weight \(u\) and quotient by the monomial of degree \(v\). Products are realized on disjoint variables. Regard such a factor as the directed edge \(u\to v\), of cost \(v-u\).

Write each positive integer uniquely as \(2^a r\) with \(r\) odd. The odd integers form a rooted tree \(T\), with root 1 and parent \(t=r/p_{\min}(r)\) for each \(r>1\). In the graph \(\mathbb{Z}_{\ge0}\times T\), take all edges
\[
 E_{a,r}:(a,r)\to(a+1,r),\qquad
 V_{a,r}:(a,t)\to(a,r)\quad(r>1,\ t=r/p_{\min}(r)).
\]
Use the corresponding single-variable Hilbert factors as generators of \(M\). Their costs are \(e_{a,r}=2^a r\) and \(v_{a,r}=2^a(r-t)\).

A product of generators is a nonnegative integer flow on finitely many edges. Its net signed vector (incoming minus outgoing) gives its exponents in \(q\)-integers. This vector determines the polynomial, and conversely. Indeed, if two products are equal but some exponent at an index \(m\ge2\) differs, choose the largest such \(m\); its contribution at a primitive \(m\)-th root cannot be canceled by any lower index. The exponent at 1 is determined by the zero sum of the vector.

**Canonical flow lemma.** Every product can be uniquely represented by a flow containing no pair \(V_{a,r}E_{a,r}\) of successive positive-flow edges. Existence follows by replacing each occurrence of \(V_{a,r}E_{a,r}\) by \(E_{a,t}V_{a+1,r}\): this runs around a square with the same net vector. The sum of the depths in \(T\) over the horizontal edges, counted with multiplicity, decreases by one at each replacement. For uniqueness, the difference of two distinct candidate flows with equal net vector is a nonzero circulation on a finite subgraph. Orient its positive differences forward and its negative differences backward; it contains a simple directed cycle. On this cycle take a row \(r\) of greatest tree depth and a vertex with that row and smallest first coordinate \(a\). Its two cycle neighbors have to be its parent-row neighbor and its right neighbor: a child-row neighbor contradicts maximal depth, and its left neighbor contradicts minimal \(a\) in this row. The two cycle edges are therefore \(V_{a,r}\) and \(E_{a,r}\), either both in the forward or both in the backward direction. One of the candidate flows then contains the forbidden pair, contradiction.

Each generator variable belongs to at most one forbidden pair (every nonroot row has a unique parent), so counting the canonical forms gives
\[
 \sum_{n\ge0}M_n z^n=
 \prod_{\substack{a\ge0\\r\ {\rm odd}}}(1-z^{2^a r})^{-1}
 \prod_{\substack{a\ge0\\r>1\ {\rm odd}}}
 \frac{1-z^{2^a(2r-t)}}{1-z^{2^a(r-t)}} ,
 \qquad t=r/p_{\min}(r).
\tag{1}
\]
All products are defined coefficientwise. This is an enumeration of distinct Hilbert polynomials, not of presentations as products. It is exact even though the monoid has nontrivial square relations.

## 2. Degree densities and growth

The horizontal costs \(2^ar\) are exactly the positive integers, each once. To count each of the other cost multisets, write \(r=pt\) and require that \(t\) have no prime divisor below the odd prime \(p\). For fixed \(p,a\) the allowable \(t\) have periodic density \(h_p\), and their cost multipliers are \(2^a(p-1)\) and \(2^a(2p-1)\). Their total densities, after summing in \(a\), are \(2\sum_{p\ge3}h_p/(p-1)\) and \(2\sum_{p\ge3}h_p/(2p-1)\).

Here the fixed-\(p,a\) densities can safely be summed. For \(p>P\) all associated odd integers \(r\) have no prime factor at most \(P\), and each cost \(2^a(r-t)\) is at least \(2^ar/2\); the numerator cost is larger still. Each pair \((a,r)\) determines a unique integer \(2^ar\), so the upper density of these tails is at most \(2\prod_{\ell\le P}(1-1/\ell)\), which tends to zero. For \(a>A\), regardless of \(p\), those integers are divisible by \(2^{A+1}\), giving upper density at most \(2^{-A}\). The decay of the prime product follows, for example, by expanding its reciprocal as a sum of reciprocals of smooth integers and comparing to harmonic partial sums.

For any multiset of positive integer costs with counting function \(C(X)=dX+o(X)\) and \(C(X)=O(X)\), partial summation gives \(\sum_c e^{-\lambda c}\sim d/\lambda\) and a uniform \(O(1/\lambda)\) bound. Expanding
\(-\log(1-e^{-t c})=\sum_{j\ge1}e^{-tj c}/j\) and using domination by a constant times \(1/j^2\) yields the logarithm of its inverse-factor product asymptotic to \(d\zeta(2)/t\). Apply this separately to the three cost multisets in (1). With \(F(z)=\sum_nM_nz^n\), it gives \(\log F(e^{-t})\sim A/t\), where \(A=\zeta(2)D\).

The passage to exact degree, rather than just cumulative degree, uses monotonicity: multiplication by \(1+q=[2]_q/[1]_q\) injects \(M_n\) into \(M_{n+1}\). For clarity, the elementary coefficient argument is as follows. Give integer \(N\ge0\) probability \(M_Ne^{-tN}/F(e^{-t})\). Its normalized scale \(t^2 N\) tends to \(A\) in probability. For the upper tail \(t^2N\ge A+\epsilon\), use Markov's inequality with \(e^{\delta tN}\); the log bound is
\[
 t^{-1}\left(\frac{A}{1-\delta}-A-\delta(A+\epsilon)+o(1)\right).
\]
It is negative for fixed sufficiently small positive \(\delta\). For the lower tail \(t^2N\le A-\epsilon\), the same argument with \(e^{-\delta tN}\) gives \(t^{-1}(A/(1+\delta)-A+\delta(A-\epsilon)+o(1))\), again negative. Let \(t=\sqrt{(A+2\epsilon)/n}\); then the window \((A-\epsilon)/t^2\le N\le(A+\epsilon)/t^2\) lies below \(n\) and has probability \(1-o(1)\). Its total unnormalized mass is at most \((n+1)M_n e^{-(A-\epsilon)/t}\) by monotonicity. Taking logs gives a lower coefficient exponent arbitrarily close to \(2\sqrt{A n}\) as \(\epsilon\to0\); the upper follows from \(M_ne^{-tn}\le F(e^{-t})\) at \(t=\sqrt{A/n}\). This proves the stated asymptotic.

The free one-parent-per-integer submonoid alone would have degree density
\[
 D_0=\sum_{p\ \mathrm{prime}}\frac{h_p}{p-1}
     =1+\sum_{p\ \mathrm{prime}}\frac{h_p}{p(p-1)}.
\]
Adding all vertical edges at all even scales improves it by
\[
 D-D_0=\sum_{p\ge3\ \mathrm{prime}}
       \frac{h_p}{(p-1)(2p-1)}\;=\;0.06586\ldots.
\]
The \(p=3\) term alone is \(1/20\). For rigorous numerical bounds in both sums, the tails beyond \(P\) are each at most \(\prod_{\ell\le P}(1-1/\ell)/P\), by the telescoping identity \(\sum_{p>P}h_p/p=\prod_{\ell\le P}(1-1/\ell)\).

## 3. Upper benchmark for all HSOPs

Every basic HSOP polynomial has constant term 1 and is a product of cyclotomic factors \(\Phi_m\), \(m\ge2\); thus the unrestricted weighted-partition upper bound of Boyd and Montgomery (*Cyclotomic partitions*, 1990) applies. An elementary proof of the leading upper exponent is included here to specify the comparison.

The number of indices \(m\) with \(\varphi(m)\le X\) is asymptotic to \(C X\) with
\(C=\prod_p(1+1/[p(p-1)])=\zeta(2)\zeta(3)/\zeta(6)\).
To verify the density, put \(R(m)=m/\varphi(m)\) and truncate its prime product to \(R_P(m)\) over primes at most \(P\). Fixed \(R_P\) is periodic, and \(\#\{m:m\le X R_P(m)\}/X\) tends to the mean \(\prod_{p\le P}(1+1/[p(p-1)])\). Further, \(R(m)=\sum_{d\mid m}\mu^2(d)/\varphi(d)\), so the average difference \(R-R_P\) over \(m\le Y\) is uniformly bounded by the tail of the convergent product \(C\). The average of \(R^2\) is uniformly bounded as well, by expanding its prime product and using convergence of \(\prod_p(1+[(1-1/p)^{-2}-1]/p)\). A dyadic decomposition over \(m>TX\) shows that the number with \(m\le XR(m)\) there is \(O(X/T)\): in the \(j\)-th interval the bound uses \(R(m)\ge 2^jT\) and the preceding second moment. For \(m\le TX\) outside the periodic bound \(m\le X(R_P(m)+\epsilon)\), a counted \(m\) must have \(R-R_P>\epsilon\), contributing at most \(TX\) times the product tail divided by \(\epsilon\). Let \(P\) increase at fixed \(T,\epsilon\), then \(\epsilon\downarrow0\) and \(T\to\infty\). This proves the density and also \(O(X)\). Applying the same logarithmic product estimate to \(\prod_{m\ge2}(1-z^{\varphi(m)})^{-1}\) gives the upper constant \(2\sqrt{\zeta(2)C}=\sqrt{105\zeta(3)}/\pi\).

**Exact controls.** `python3 verify_cgf_hsop_divisor_tree_growth.py` compares (1) through degree 28 with an independent enumeration of distinct net vectors. It also bounds the prime-density sums using exact rational truncation. The normal form and asymptotic estimate are proved above; they do not rely on the finite checks.
