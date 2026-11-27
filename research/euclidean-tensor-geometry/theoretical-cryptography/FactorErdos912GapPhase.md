# Distinct exponents in factorials: unconditional gap reduction in density

Let \(h(n)\) be the number of distinct positive exponents in the prime factorization of \(n!\), as in [Erdős Problem 912](https://www.erdosproblems.com/912). Write \(p^+\) for the prime immediately after \(p\), and put
\[
T_p=\frac{p\,p^+}{p^+-p},\qquad
W(x)=\sum_{p}\min(1,x/T_p),\qquad
A(x)=\#\{p:T_p\le x\},\qquad L(x)=\sqrt{x/\log x}.
\]
The series for \(W\) converges, since \(1/T_p=1/p-1/p^+\).

**Theorem.** Uniformly over integers \(X\ge3\) and \(1\le H\le X\),
\[
\left(\frac1H\sum_{X\le n<X+H}|h(n)-W(n)|^2\right)^{1/2}
 \ll X^{3/5}H^{-1/5}(\log X)^{1/5}. \tag{1}
\]
Thus normalized concentration holds even on arbitrary intervals with \(H/[X^{1/2}(\log X)^{7/2}]\to\infty\). In particular, the root mean square error on \([X,2X)\) is \(O(X^{2/5}(\log X)^{1/5})\). For each positive \(c\), the following are equivalent:
- (i) \(h(n)/L(n)\) converges to \(c\) in natural density (that is, the proportion of \(n\le X\) with error exceeding any fixed positive tolerance tends to zero).
- (ii) \(W(x)/L(x)\to c\) as \(x\to\infty\).
- (iii) \(A(x)/L(x)\to c/2\) as \(x\to\infty\).

The theorem controls the floor phases unconditionally and isolates a single weighted gap statistic. It does **not** prove the existence of the limit in (3), and even that limit would imply the factorial asymptotic only in density by this argument.

## From prime powers to a gap sum

The exact identity
\[
h(n)=\#\{\lfloor n/p\rfloor:p\le n,\ p\text{ prime}\} \tag{2}
\]
is established in the proof of [Heyman–Miraj, Theorem 2](https://arxiv.org/abs/2309.16072). To recall why, if \(p\le\sqrt n\) and \(q>p\), then \(\lfloor n/p\rfloor>\lfloor n/q\rfloor\): when \(n<pq\) the two values are respectively at least \(p\) and at most \(p-1\); when \(n\ge pq\) their real-valued difference is at least one. The higher-power terms in Legendre's formula are nonincreasing with the prime and vanish for \(p>\sqrt n\). Thus the same small-prime terms are strictly separated whether we count floors or true exponents, and the large-prime terms are identical.

The sequence of floors in (2) is nonincreasing and eventually zero. Counting each positive value once at its last occurrence gives
\[
h(n)=\sum_p I_p(n),\qquad
I_p(n)=\mathbf 1_{\{\lfloor n/p\rfloor>\lfloor n/p^+\rfloor\}}. \tag{3}
\]
For \(n\ge T_p\), the unrounded difference is at least one and \(I_p(n)=1\). For \(n<T_p\), the floor difference is either zero or one, and hence
\[
 I_p(n)-\min(1,n/T_p)
 =\mathbf 1_{\{n<T_p\}}\big(\{n/p^+\}-\{n/p\}\big). \tag{4}
\]
This equality includes \(n=T_p\), where its two sides are zero. For any cutoff \(P\ge2\), let \(u\) be the first prime greater than \(P\). The sum over \(p>P\) of the indicators in (3) is at most \(\lfloor n/u\rfloor\) by telescoping the floor differences. The corresponding tail of \(W(n)\) is at most \(n/u\) by the reciprocal telescope. Consequently, discarding that tail incurs a pointwise \(O(X/P)\) error for \(X\le n<2X\).

## Controlling the moving cutoffs by the additive large sieve

For a prime \(q\) set
\[
f_q(n)=\{n/q\}-\frac{q-1}{2q}.
\]
It has mean zero modulo \(q\); its finite Fourier expansion uses precisely frequencies among the nonzero fractions \(a/q\) with \(1\le a<q\). By finite Parseval the sum of squared Fourier coefficients is \((q^2-1)/(12q^2)\le1/12\). On substituting these functions into (4), the sum of discarded constants for all active \(p\le P\) is bounded by
\(\sum_p(1/p-1/p^+)/2=1/4\).

For each \(p\le P\), the set of integers \(X\le n<X+H\) with \(n<T_p\) is a prefix of the interval. In the dyadic partition anchored at \(X\), decompose that prefix into disjoint dyadic blocks, at most one of each size (the binary expansion of its length). Let \(\mathcal P_I\) be the set of primes assigned to block \(I\) in this way. The truncated centered expression in (4), denoted \(E(n)\), is the sum over blocks \(I\ni n\) of
\[
E_I(n)=\sum_{p\in\mathcal P_I}\big(f_{p^+}(n)-f_p(n)\big).
\]
At most \(1+\lfloor\log_2 H\rfloor\) block sizes can contribute at a point. At a fixed size the blocks are disjoint and \(\sum_I|\mathcal P_I|\le\pi(P)\).

The denominators appearing in \(E_I\) are primes at most \(2P\) by Bertrand's postulate. Each denominator occurs at most once with positive and once with negative sign, since each prime has a unique predecessor and successor. After collecting coefficients the sum of squared Fourier coefficients is therefore at most \(|\mathcal P_I|/6\). All distinct frequencies are separated modulo one by at least \((2P)^{-2}\), since they are reduced fractions with denominators at most \(2P\). The dual form of the [Montgomery–Vaughan additive large sieve, Theorem 1](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf) gives
\[
\sum_{n\in I}|E_I(n)|^2\ll (|I|+P^2)|\mathcal P_I|.
\]
Apply Cauchy–Schwarz to the block sizes, sum over disjoint blocks at each size, and then sum the sizes. It follows that
\[
\sum_{X\le n<X+H}|E(n)|^2
\ll (1+\log H)^2(H+P^2)\pi(P).
\]
The triangle inequality in the normalized square norm, the bounded discarded constants, and the tail estimate yield
\[
\left(\frac1H\sum_{X\le n<X+H}|h(n)-W(n)|^2\right)^{1/2}
\ll (1+\log H)\sqrt{(1+P^2/H)\pi(P)}+1+X/P.
\]
Take \(P=(X^2H/\log X)^{1/5}\), adjusting by a bounded factor for small \(X\). Here \(\log P\asymp\log X\) and \(P^2/H\gg1\). The prime-counting upper bound \(\pi(P)\ll P/\log P\) gives (1).

## The density-order equivalence

Chebyshev's inequality and (1) with \(H=X\) give, for every fixed \(\epsilon>0\),
\[
\#\{X\le n<2X:|h(n)-W(n)|>\epsilon L(n)\}
 \ll_\epsilon X^{4/5}(\log X)^{7/5}. \tag{5}
\]
Summing over dyadic blocks shows convergence of the normalized difference to zero in natural density. By splitting the series at \(P=\sqrt{x\log x}\) and using the reciprocal telescope above, \(W(x)\ll L(x)\). For \(x\le y\le(1+\eta)x\) we have \(W(x)\le W(y)\le (1+\eta)W(x)\), and \(L(y)/L(x)\in[1,\sqrt{1+\eta}]\) for \(x>e\). The ratio \(W/L\) thus changes by at most \(O(\eta)\) on every such interval. A real sequence \(x_j\to\infty\) at which \(W/L\) stays a fixed distance from \(c\) would give intervals of integers of fixed relative length with the same discrepancy, contradicting convergence in density. This proves the equivalence of (i) and (ii).

For the remaining equivalence, the nonnegative sum gives the exact integral
\[
 \frac{W(x)}x=\int_x^\infty\frac{A(t)}{t^2}\,dt. \tag{6}
\]
If \(A(t)\sim aL(t)\), substituting \(t=xz\) shows \(W(x)\sim2aL(x)\) by dominated convergence. Conversely let \(B(x)=W(x)/x\sim c L(x)/x\). Monotonicity of \(A\) gives, for fixed \(\lambda>1\),
\[
 \frac{x[B(x/\lambda)-B(x)]}{\lambda-1}\le A(x)
 \le\frac{x[B(x)-B(\lambda x)]}{1-1/\lambda}.
\]
On dividing by \(L(x)\), the lower and upper bounds tend to \(c/(\sqrt\lambda+1)\) and \(c\sqrt\lambda/(\sqrt\lambda+1)\), respectively. Letting \(\lambda\downarrow1\) finishes the proof.

## Two consequences

**A strict unconditional upper constant in density.** There is an absolute \(\delta>0\) such that \(h(n)\le (2\sqrt2-\delta)L(n)\) off a set of natural density zero. Indeed, split \(W(x)\) at \(Y=\sqrt{x\log x/2}\). Counting all primes up to \(Y\) with weight one and telescoping the tail would give \(\pi(Y)+x/Y=(2\sqrt2+o(1))L(x)\). The same split in (2) gives the elementary pointwise upper constant \(2\sqrt2+o(1)\) for \(h\). But by [Goldston–Pintz–Yıldırım, *Primes in Tuples IV*, (3.1)–(3.2)](https://real.mtak.hu/10064/1/pintz.pdf), for every sufficiently small fixed \(\eta>0\) there are \(\gg_\eta Y/\log Y\) primes \(Y/2<p\le Y\) with \(p^+-p\le\eta\log(Y/2)\). Their individual weights are at most \(4x\eta\log Y/Y^2\le1/2\) for small enough fixed \(\eta\) and large \(x\). This gives a uniform saving \(\gg_\eta L(x)\) for \(W(x)\); (5) transfers, for example, half of the saving to \(h(n)\) in density.

**If normalized gaps have a limiting distribution.** Suppose the empirical probability law of \((p^+-p)/\log p\) for \(p\le y\) converges weakly to a probability law \(\nu\) as \(y\to\infty\). Put \(Y=\sqrt{x\log x}\), with \(Y\) now chosen without the factor \(1/\sqrt2\). For fixed \(0<a<b<\infty\), the joint measures of
\[
\left(\frac{p}{Y},\frac{p^+-p}{\log p}\right),\qquad aY<p\le bY,
\]
with weight \(1/(2L(x))\) per point, converge to \(dt\,d\nu(u)\) on \((a,b]\times[0,\infty)\). This follows first for rectangles by subtracting the empirical counts up to the two fixed multiples of \(Y\) and using \(\pi(vY)\sim2vL(x)\) for fixed \(v>0\). It extends to weak convergence by approximation and tightness. Uniformly on \(aY<p\le bY\), the prime number theorem gives \(p^+/p\to1\), and the inequality \(T_p\le x\) is equivalent to \(u\ge p p^+/(x\log p)\), where the right side tends uniformly to \(2t^2\). The boundary of the limiting event \(u\ge2t^2\) has product measure zero, even if \(\nu\) has atoms, because for each \(u\) there is at most one such \(t\). The contributions to \(A(x)\) below \(aY\) and above \(bY\) are bounded, respectively, by \((2a+o(1))L(x)\) and \(x/(bY)=L(x)/b\), the latter again by the reciprocal telescope. Letting \(a\downarrow0\) and \(b\uparrow\infty\) now yields
\[
 \frac{A(x)}{L(x)}\longrightarrow
 2\int_0^\infty\nu([2t^2,\infty))\,dt
 =\sqrt2\int_0^\infty\sqrt u\,d\nu(u).
\]
Therefore the constant for \(h(n)/L(n)\) in density is \(2\sqrt2\int\sqrt u\,d\nu(u)\). For the mean-one exponential law it is \(\sqrt{2\pi}\). The exponential gap law is itself conjectural; it follows from sufficiently uniform prime-tuple hypotheses via [Gallagher's short-interval result](https://doi.org/10.1112/S0025579300016442) as recorded for gaps in [Goldston–Pintz–Yıldırım, (1.3)](https://arxiv.org/abs/1103.5886).

## Relation to previous results and reproducibility

[Erdős and Selfridge's order-of-magnitude theorem](https://www.renyi.hu/~p_erdos/1982-08.pdf) bounds \(h(n)\) above and below by constant multiples of \(L(n)\), pointwise. The floor identity (2) is not new. [Gabdullin–Iudelevich, Theorem 1.2](https://arxiv.org/abs/2609.25341) give a refined asymptotic in the Cramér model, not for the actual prime sequence. This note's comparison (1), the resulting single-statistic equivalence in density, and its strict density upper bound concern actual primes unconditionally. Neither a gap limit nor the original pointwise asymptotic is established here.

[verify_factor_erdos912_gap_phase.js](verify_factor_erdos912_gap_phase.js) checks the finite identities, tail bounds, prefix decomposition and Fourier input on small exact-integer fixtures. These checks are not a test of any conjectural gap law.
