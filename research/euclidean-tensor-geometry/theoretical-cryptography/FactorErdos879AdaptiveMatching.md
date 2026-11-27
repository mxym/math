# Quantitative prime matching for the Erdős–van Lint coprime sum

For an integer \(n\), let \(G(n)\) be the maximum sum of a pairwise coprime subset of \(\{1,\ldots,n\}\), and put
\[
 H(n)=\sum_{p\le n}p+n\pi(\sqrt n).
\]
[Erdős, p. 120 after (30)](https://www.renyi.hu/~p_erdos/1984-16.pdf) reports the Erdős–van Lint asymptotic and the bounds \(H(n)-n^{3/2}<G(n)<H(n)\), as well as \((H(n)-G(n))/n\to\infty\), and asks about a deficit \(n^{1+o(1)}\); see [Erdős #879](https://www.erdosproblems.com/879). The alternative convention of excluding \(n\) or excluding the prime \(n\) from the sum on the right changes the quantities by at most \(O(n)\), irrelevant to the results here. The known reduction to matching small primes to distinct large prime partners is described explicitly in the [#879 working report](https://www.erdosproblemaday.com/report/879). We use a variable-width interval matching and a square fallback near the endpoint to get a quantitative bound:

**Theorem.** Unconditionally, there is an absolute \(c>0\) such that for all sufficiently large \(n\),
\[
 0<H(n)-G(n)\ll n^{3/2}\exp\left(-c\frac{(\log n)^{3/5}}
                                                     {(\log\log n)^{1/5}}\right).
 \tag{1}
\]
In particular there is a saving over \(n^{3/2}\) by every fixed power of \(\log n\). Under the Riemann hypothesis the same method with a localized discrepancy yields
\[
 H(n)-G(n)\ll n^{5/4}(\log n)^2.
 \tag{2}
\]
For either construction the chosen integers are primes, prime squares, products of two distinct primes, or \(1\). This is not the conjectured \(n^{1+o(1)}\) estimate, and it says nothing about whether a true optimum must contain an integer with three or more distinct prime factors.

## 1. A quantitative matching step

Write \(x=\sqrt n\). Let \(0<\alpha<1\) be fixed, and suppose on \([x^\alpha,x^{2-\alpha}]\) that
\[
  |\pi(y)-\operatorname{li}(y)|\ll \rho\,y/\log y,\qquad \rho=\rho(x)\to0,
 \tag{3}
\]
uniformly in \(y\), with the implied constant fixed. We will use positive \(\rho\ge x^{-1}\). Consider a bin of small primes \(I=(t,t(1+h)]\) with \(t\ge x^\alpha\), and a supply bin of large primes
\[
 J=\left(\frac{n}{t(1+h)^2},\frac{n}{t(1+h)}\right].
 \tag{4}
\]
Put \(r=1-t/x\), and suppose \(r>0\) and \(h\le r/16\). Then \(J\subset(x,x^{2-\alpha}]\). For any \(p\in I\) and \(q\in J\) one has
\[
  \frac{n}{(1+h)^2}<pq\le n,\qquad n-pq\ll nh.
 \tag{5}
\]
We show that if \(\rho/h\) is sufficiently small compared with \(r\), \(J\) has at least as many primes as \(I\).

Indeed \(s=n/((1+h)v)\) for \(t\le v\le t(1+h)\) transforms the logarithmic integral for \(J\) to an integral over \(I\), and the ratio of its density to that for \(I\) is
\[
 R(v)=\frac{n}{(1+h)v^2}\frac{\log v}{\log(n/((1+h)v))}.
\]
As a function of \(a=\log(x/v)\), with \(L=\log x\), its log is
\[
 2a-\log(1+h)+\log(L-a)-\log(L+a-\log(1+h)).
\]
On the relevant range \(0\le a\le(1-\alpha)L\) the derivative is at least \(3/2\) for large \(x\), because both logarithm denominators are \(\gg_\alpha L\). At \(a=0\) the log ratio is at least \(-h\). In \(I\) one has \(a\ge 1-v/x\ge r-h\ge 15r/16\). Thus the integral for \(J\) exceeds that for \(I\) by a ratio at least \(1+r\). At either bin, (3) gives relative error \(O(\rho/h)\) in its prime count: the endpoint error is \(O(\rho y/\log y)\) while the integral is \(\asymp h y/\log y\) for the bin's lower endpoint \(y\). In particular when \(h=A\rho/r\) with \(A\) a sufficiently large fixed constant, the relative errors are at most \(r/10\), so \(\#\{p\in J\}\ge\#\{p\in I\}\). More generally the same argument only needs (3) at the four bin endpoints, and \(A\) may depend on the uniform error constant.

## 2. Global bin assignment and the near-square escape

Set \(\sigma=4\sqrt{A\rho}\). Starting at \(t_0=x^\alpha\), let \(h_j=A\rho/(1-t_j/x)\), and form a bin \(I_j=(t_j,t_{j+1}]\) with \(t_{j+1}=t_j(1+h_j)\) as long as \(t_{j+1}\le x(1-\sigma)\). Associate \(J_j\) by (4). The bins \(I_j\) are disjoint, \(h_j\) is nondecreasing, and the bins \(J_j\) are disjoint as well: the upper endpoint of \(J_{j+1}\), if it exists, is \(n/[t_{j+1}(1+h_{j+1})]\), at most the lower endpoint of \(J_j\). The half-open convention permits equality. Also \(h_j/(1-t_j/x)\le1/16\) by the stopping rule, so the capacity comparison in Section 1 applies. Pick a distinct \(q_p\in J_j\) for each \(p\in I_j\).

At the last endpoint \(t_\ast\) the next bin would cross \(x(1-\sigma)\) and its width is at most \((\sigma/16)x\). Thus \(t_\ast\ge x(1-2\sigma)\), including the initial endpoint if there were no bins. For all primes \(t_\ast<p\le x\), use the singleton **square** \(p^2\), not a conflicting partner at \(q\) near \(x\). Let \(S\) be the pairwise coprime set formed by replacing the two primes \(p,q_p\) in the baseline of all primes by \(pq_p\), replacing each prime in the residual near-square strip by its square, keeping all remaining primes, and adjoining \(1\). All pair primes lie on opposite sides of \(x\); every prime is used exactly once in the resulting supports. The exact deficit from this admissible construction is
\[
 H(n)-\sum_{a\in S}a
 =\sum_{\text{matched }p}(n-pq_p+p+q_p)
  +\sum_{t_\ast<p\le x}(n-p^2+p)
  +n\pi(x^\alpha)-1.
 \tag{6}
\]
Here and below \(p\) is prime in every sum over \(p\).

To bound the pairing loss, (5) reduces it to \(O(n\sum_{\text{matched }p}h_j)\). For a prime \(p\in I_j\), \(h_j\le A\rho/(1-p/x)\). The primes \(p\le x/2\) contribute \(O(\rho x/\log x)\). For \(p>x/2\), split \(1-p/x\ge\sigma\) into dyadic bands \([u,2u]\). There are \(O(1+\log(1/\rho))\) such bands. By (3), since \(u\gg\rho\), the number of primes in each is \(O(u x/\log x)\), including the endpoint rounding. This bounds the contribution per band by \(O(\rho x/\log x)\). The near-square strip has \(O(\sigma x/\log x)\) primes, and \(n-p^2\le 2x(x-p)\ll n\sigma\); hence its square loss is \(O(n x\sigma^2/\log x)=O(n x\rho/\log x)\). The \(+p\) terms have total \(O(n)\). Finally the partner costs satisfy
\[
 \sum_{\text{matched }p}q_p\le n\sum_{x^\alpha<p\le x}\frac1p=O_\alpha(n)
\]
by Mertens. We conclude the discrepancy-to-matching bound
\[
 H(n)-G(n)\ll_\alpha n x^\alpha+n+
       \frac{n x}{\log x}\rho\,\{1+\log(1/\rho)\}.
 \tag{7}
\]
In contrast with a fixed-width partition, the bin cost here is summed by distance from \(x\) and is essentially proportional to \(\rho\), up to the displayed logarithm.

For positivity of the deficit, an optimal set contains \(1\) and collectively uses every prime at most \(n\): an unused prime could itself be adjoined. For a chosen \(a>1\) with \(b\) distinct small prime divisors \(p\le x\), allocate to \(a\) the budget \(\sum_{p\mid a}p+nb\). If \(b=0\), then \(a\) must be a prime \(>x\), because the product of two primes \(>x\), even repeated, exceeds \(n\). Its budget equals \(a\). If \(b\ge1\), \(a\le n\) and the budget exceeds \(a\) by at least the sum of its small prime divisors. Sum these inequalities and subtract \(1\) for the element \(1\) to get \(H(n)-G(n)\ge\sum_{p\le x}p-1>0\) for \(x\ge2\).

Take \(\alpha=1/2\). The classical Vinogradov–Korobov prime number theorem, for example [the Chebyshev-function estimate in Johnston–Yang, Theorem 1.4](https://arxiv.org/abs/2204.01980) followed by partial summation, gives (3) with \(\rho=\exp(-c_0(\log x)^{3/5}/(\log\log x)^{1/5})\) for a sufficiently small absolute \(c_0>0\), uniformly for \(y\in[x^{1/2},x^{3/2}]\). The factor \(\log y\) in (3) is absorbed by decreasing \(c_0\). Equation (7) proves (1).

## 3. Conditional RH refinement: localizing the error

Here assume the Riemann hypothesis, so that \(\pi(y)-\operatorname{li}(y)=O(\sqrt y\log y)\) (e.g. the standard consequence noted in [Tao's prime-counting reference, Theorem 14.5](https://teorth.github.io/expdb/blueprint/chap-prime_counting_function.html)). The near-square region \(p\in(x/2,x]\) uses just the construction of Section 2 started at \(t_0=x/2\), with the **local** error \(\rho_x=x^{-1/2}(\log x)^2\) for endpoints in \([x/2,2x]\). All supply primes there are in \((x,2x]\). The matched shortfalls plus the square loss are \(O(nx^{1/2}(\log x)^2)\) by the same proof of (7), but no lost-prime term \(n\pi(t_0)\) is charged to this region.

Below \(x/2\) partition the primes into dyadic intervals \((T,2T]\) of the form \(T=x/2^{j+1}\), \(j\ge1\), keeping those with \(T\ge x^{1/2}\). Primes left below these bands are at most \(2x^{1/2}\), costing \(O(nx^{1/2})\) if left unchanged. For each kept band take a constant relative bin width \(h_T=A T^{-1/2}(\log x)^2\). In the small-prime interval start at \(t=T\), and form bins as in (4) only while \(t(1+h_T)^2\le 2T\). Their supply intervals all lie in the corresponding disjoint band \((n/(2T),n/T]\). Now \(r\ge1/2\) and the uniform endpoint bound in (3) for this bin is valid with \(\rho_T=T^{-1/2}(\log x)^2\) by RH, since its endpoints are at least \(T\) and at most \(x^2\). Thus \(h_T=A\rho_T\) produces enough supply for a sufficiently large \(A\). The leftover small-prime interval has length \(O(h_T T)\), so RH gives \(O(h_T T/\log T)\) primes there. Leave them unchanged.

By (5), the loss of matched products and leftover small primes summed over the dyadic band is \(O(nh_T T/\log T)\). Summing over the decreasing dyadic scales gives \(O(nx^{1/2}\log x)\) because \(\log T\ge(\log x)/2\). No supply primes overlap the near-square supply, and the prime costs in (6) stay \(O(n)\) by Mertens. This proves (2), including its conditional status.

## Finite verification

Run `node verify_erdos879_adaptive_matching.js`. It checks the exact feasibility/supply-bin separation and the deficit accounting for rational endpoints and small primes. It does not test the prime-number theorem or compute the claimed asymptotic maximum.
