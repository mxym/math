# A density law for the simultaneous binomial prime-factor exponent

Let \(P(m)\) denote the largest prime factor, with \(P(1)=1\), and let \(p_-(n)\) be the largest prime at most \(n\). Write
\[
D(n)=n-p_-(n),\qquad
B(n)=\sup\left\{b\ge0:\ 
 P\!\binom nk\ge \min(n-k+1,k^b)\ \text{for every }1\le k\le n/2
 \right\}.
\]
Here \(b=1+c\) in [Erdős problem 683](https://www.erdosproblems.com/683). In particular the order of quantifiers in \(B(n)\) requires **all** of one row's relevant coefficients to satisfy the bound.

**Theorem.** There is a set of natural density one on which
\[
\frac{B(n)\log D(n)}{\log n}\longrightarrow 1 .
\]
More precisely, for every fixed \(0<\rho<1\) and each sufficiently large integer \(X\), all but \(O_\rho(X/\log\log\log X)\) integers \(n\in[X,2X]\) have \(D(n)>1\) and satisfy
\[
1-(\log\log X)^{-\rho}\ \le\
\frac{B(n)\log D(n)}{\log n}\ \le\ 1. \tag{1}
\]
Thus the almost-everywhere exponent is controlled by the preceding prime gap, even if the exponent depends on \(n\). In addition, for every fixed \(0<c<19\), the whole row satisfies the Erdős inequality with exponent \(1+c\) for all but \(O_c(X/(\log X)^{1/50})\) integers \(n\in[X,2X]\).

The original worst-case problem, with no exceptional \(n\), is not settled here. The result transfers existing prime-distribution theorems; it does not improve those prime estimates.

## 1. Deterministic bounds from the preceding prime

If \(D=D(n)\ge2\), then \(D<n/2\) by Bertrand's postulate. At \(k=D\), all \(D\) numerator terms in \(n!/(n-k)!\) are composite, by the definition of \(p_-(n)\). Every prime factor of these terms is at most \(n/2\). Since \(n-D+1=p_-(n)+1>n/2\), any feasible \(b\) must satisfy \(D^b\le n/2\). Consequently
\[
B(n)\log D(n)\le \log(n/2). \tag{2}
\]
At the other end, for every \(k>D(n)\) with \(k\le n/2\), the prime \(p_-(n)\) is a numerator term and exceeds \(k\). It cannot cancel against \(k!\), and gives \(P(\binom nk)\ge p_-(n)\ge n-k+1\), independently of \(b\).

For \(1\le k\le n/2\), [Sylvester–Schur in Erdős's 1934 form](https://www.renyi.hu/~p_erdos/1934-01.pdf) ensures that the largest prime factor of the numerator exceeds \(k\), hence survives division by \(k!\). Thus, writing \(M_n(k)=\max_{0\le j<k}P(n-j)\), we have \(P(\binom nk)=M_n(k)>k\), and every \(b\le1\) is feasible. More precisely, when \(D(n)\ge2\),
\[
B(n)=\min_{2\le k\le D(n)}\frac{\log M_n(k)}{\log k}. \tag{2a}
\]
Indeed for each of these \(k\) the numerator is a block of composites, \(M_n(k)\le n/2<n-k+1\), and thus feasibility requires exactly \(k^b\le M_n(k)\). The other \(k\)'s impose no restriction. In the lower-bound argument, if \(b\ge1\), finding any prime \(>k^b\) in the last \(k\) numerator terms is sufficient.

## 2. A high prime factor in one short window

We will use [Matomäki–Radziwiłł, Theorem 1](https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n3-p06-p.pdf). In their notation the short and dyadic averages of a multiplicative \(f:\mathbb N\to[-1,1]\) differ by at most
\[
\delta+C_0\frac{\log\log h}{\log h}
\]
outside a set of at most
\[
CX\left(\frac{(\log h)^{1/3}}{\delta^2h^{\delta/25}}
          +\frac1{\delta^2(\log X)^{1/50}}\right)
\tag{3}
\]
starting points. The constants are uniform when \(f,h,\delta\) depend on \(X\).

In this application \(f(m)=\mathbf 1_{P(m)\le X^\alpha}\), where \(3/4\le\alpha<1\) may vary with \(X\). For \(m\in[X,2X]\) there is at most one prime factor \(>X^\alpha\). Counting multiples and using Mertens' theorem for primes gives, uniformly for these \(\alpha\),
\[
\frac1X\sum_{X\le m\le2X} f(m)
=1-\sum_{X^\alpha<p\le2X}\frac1p+O(1/\log X)
=1-\log(1/\alpha)+O(1/\log X). \tag{4}
\]
The first error is \(O(\pi(2X)/X)\); in the second step the endpoint logarithms are comparable and the Mertens error has the same size.

For the backward window \(n-h+1,\ldots,n\) with \(h\) integral, apply (3) at starting point \(n-h+1\), taking length \(h-1\) in the inclusive convention of the paper. The change of normalization is \(O(1/h)\), and there are at most \(h\) exceptional boundary integers near \(X\). It follows that if \(\delta+C_0\log\log h/\log h+O(1/h+1/\log X)<\log(1/\alpha)\), then outside the resulting exceptional set at least one integer in the backward window has a prime factor \(>X^\alpha\).

## 3. Proof of the density law

Write \(L=\log X,\ M=\log L\), fix \(0<\rho<1\), and choose
\[
\kappa=(1+\rho)/2,\quad\varepsilon=M^{-\rho},\quad
\alpha=1-\varepsilon/2,\quad
\delta=\varepsilon/8,\quad
h=\lceil\exp(M^\kappa)\rceil .
\]
By (4), the dyadic smooth mean is below \(1\) by at least \(\varepsilon/2+O(1/L)\). The short-average error from (3), including the endpoint correction, is less than \(\varepsilon/3\) for large \(X\). The two terms in (3), divided by \(X\), are bounded by a polynomial in \(M\) times \(\exp(-c_0 M^{\kappa-\rho})\) and \(O(M^{2\rho}L^{-1/50})\), respectively. Both are \(o(1/\log M)\). Thus all but \(o(X/\log M)\) of the backward windows contain a prime factor \(>X^\alpha>(2X)^{1-\varepsilon}\).

Also, all but \(O(X/L^{1/2})\) integers \(n\in[X,2X]\) have \(D(n)\ge L^{1/2}\): an integer with smaller \(D(n)\) lies within that distance to the right of some prime, and the union of these intervals has at most \(O(L^{1/2}\pi(2X))\) integers. When \(D(n)\ge L^{1/2}\), set
\[
b=(1-\varepsilon)\frac{\log n}{\log D(n)}.
\]
It remains to prove this \(b\) feasible outside a small exceptional set; if \(b\le1\) feasibility is already known. For \(h\le k\le D(n)\), any high prime factor found in the last \(h\) terms is \(>n^{1-\varepsilon}\ge k^b\) and exceeds \(k\).

For \(k<h\), the bound on \(D(n)\) gives \(b\le 2\log(2X)/M\), so
\[
k^b\le X^{4/M^{1-\kappa}}
\]
for large \(X\). We show that all but \(O_\rho(X/\log M)\) integers \(n\in[X,2X]\) themselves have a prime divisor above this last threshold. Set \(Y=X^{4/M^{1-\kappa}}\), \(Z=X^{1/10}\), and let \(V(n)\) count the prime divisors of \(n\) in \((Y,Z]\). By Mertens,
\[
\mu:=\sum_{Y<p\le Z}1/p=(1-\kappa)\log M+O(1).
\]
For uniform \(n\) in the interval, each divisibility probability is \(1/p+O(1/X)\) and the two-prime probability for distinct \(p,q\) is \(1/(pq)+O(1/X)\), by counting multiples. The total error from pairs is \(O(Z^2/X)=o(1)\). Thus \(\mathbb E V=\mu+o(1)\) and \(\operatorname{Var}V\le\mu+o(1)\), so Chebyshev's inequality bounds the fraction with \(V=0\) by \(O(1/\mu)\). For all other \(n\), the factor of \(n\) itself is a valid numerator factor for every \(k<h\). The case \(k>D(n)\) was deterministic in Section 1. This proves the left side of (1), with total exception \(O_\rho(X/\log M)\); equation (2) proves the right side. Use \(X=2^j\) on each dyadic band. The union of the exceptional sets has density zero by summing the geometric band lengths, and the lower errors tend to zero on its complement.

## 4. Fixed exponents and comparison of exceptional sets

Fix \(c>0\), \(r=1/(1+c)\), and \(0<\sigma<r\). Write \(\mathcal B_c(X)\) for the integers \(n\in[X,2X]\) for which at least one coefficient violates the proposed bound with \(b=1+c\). The following comparison also follows from the argument:
\[
\begin{aligned}
\#\{n\in[X,2X]:D(n)>(n/2)^r\}
&\ \le\ |\mathcal B_c(X)|\\
&\ \le\ \#\{n\in[X,2X]:D(n)>n^{r-\sigma}\}
      +O_{c,\sigma}\big(X/(\log X)^{1/50}\big).
\end{aligned} \tag{5}
\]
The first inequality is (2). For the second, take a fixed
\(\max(3/4,1-(1+c)\sigma)<\alpha<1\). For \(k\le D(n)\le n^{r-\sigma}\) the threshold \(k^{1+c}\) is below \(X^\alpha\) for \(n\in[X,2X]\) and large \(X\). Apply Section 2 with a fixed small \(\delta>0\) and \(h=\lceil(\log X)^K\rceil\) for sufficiently large fixed \(K\) to make the first term in (3) \(O((\log X)^{-1/50})\). This covers \(k\ge h\). For \(k<h\) use a prime factor of \(n\) exceeding \(y=(\log X)^J\), with fixed \(J>K(1+c)\). All but \(O(X^{1-\varepsilon_J})\) integers have such a factor. In detail, for \(v=1-1/(2J)>0\),
\[
\#\{n\le2X:P(n)\le y\}\le
(2X)^v\prod_{p\le y}(1-p^{-v})^{-1}
\le (2X)^v\exp(O_J(\sqrt{\log X})),
\]
by the elementary bound on \(\sum_{m\le y}m^{-v}\). This proves (5).

[Chaohua Jia, *Almost all short intervals containing prime numbers*, Acta Arith. 76 (1996), main theorem](https://geodesic.mathdoc.fr/articles/10.4064/aa-76-1-21-84/) gives a prime in \((m,m+m^{1/20+\eta}]\) for every fixed \(\eta>0\) outside \(O_A(X/(\log X)^A)\) starting points \(m\in[X,2X]\), for any fixed \(A>0\). For \(c<19\), choose \(1/20+\eta<\gamma<r-\sigma<r\) and shift the starting point to \(m=n-\lfloor X^\gamma\rfloor\). For large \(X\), Jia's interval fits inside \((m,n]\); the \(O(X^\gamma)\) initial boundary points are negligible. Thus \(D(n)\le n^{r-\sigma}\) with the required exceptional bound, and (5) yields the fixed-exponent assertion in the theorem. Under the stronger short-prime-interval estimate stated in [Runbo Li's November 2026 working paper](https://www.cambridge.org/engage/coe/article-details/6ab6dc334770e67d9232ce45), the same transfer gives \(c<23\); that improvement depends on the unrefereed estimate and is not needed for \(c<19\).

Equivalently, if \(\theta_*\) is the infimum of exponents \(\theta>0\) for which \(D(n)\le n^\theta\) for a density-one set of \(n\), the supremal fixed exponent \(c\) that works for a density-one set of whole rows is \(\theta_*^{-1}-1\), with \(+\infty\) if \(\theta_*=0\). This follows immediately from (5); no assertion at an endpoint is required. The prior [#1201 short-interval argument of Chojecki](https://www.ulam.ai/research/erdos1201-lpd.pdf) uses the same Matomäki–Radziwiłł input for individual smooth blocks. The new deductions here are uniformity across a whole binomial row and the converse obstruction from the last prime gap.

The [companion checker](verify_erdos683_binomial_gap_density.js) verifies the finite numerator, denominator and preceding-gap comparisons. The density estimates follow from the proof and the stated analytic inputs.
