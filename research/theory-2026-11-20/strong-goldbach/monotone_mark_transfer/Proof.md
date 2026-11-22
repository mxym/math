# Transferring the true semiprime cusp debit to ranks at least five

Write \(N=2x\), \(L=\log x\), \(J=xJ_0\) for a fixed nondegenerate interval \(J_0\subseteq[1,3/2]\), and \(P=N-y\). Every opposite prime in this note is the actual prime \(P\), and its weight is \(\log P\). Write \(\mathfrak S(N)\) for the Goldbach singular series in the [true even-cusp theorem](../true_even_cusp_rank_tail/Proof.md). For squarefree \(y\), let \(u_p=\log p/L\) for each \(p\mid y\), \(T=\log y/L\), and
\[
 F(y)=\sum_{d\mid y}\mu(d)\left|\frac{\log d}{L}-\frac T2\right|.
\]
In particular \(F(y)=0\) on all odd ranks. An upper bound on its true composite sum with coefficient below the calibrated reference \(2|J|\mathfrak S(N)\) would suffice for Goldbach at \(N\). We do not prove that bound.

Fix \(0<\beta<1/8\). Take a smooth nondecreasing function \(w\) with values in \([0,1]\), zero on \([0,\beta]\), and one on \([2\beta,\infty)\). For \(0<\delta<1/8\), let \(\chi_\delta\) be a smooth cutoff with values in \([0,1]\), one up to \(1/2-\delta\) and zero at and above \(1/2-\delta/2\). Define
\[
 \phi(u)=2u\,w(u)\chi_\delta(u).
\]
For \(0<\epsilon<\delta/5\), take \(g=g_\epsilon\) by rescaling a fixed smooth nonincreasing transition: \(g=1\) through \(1/2-2\epsilon\), \(g=0\) at and above \(1/2-\epsilon\), with \(0\le g\le1\). Define the transfer and the new score
\[
 Z(y)=-\sum_{d\mid y}\mu(d)g(\log d/L)\sum_{p\mid d}\phi(u_p),
 \qquad
 \widetilde F(y)=F(y)-Z(y).                                      \tag{1}
\]

**Theorem.** Given any \(\xi>0\), one can fix \(\beta,\delta,\epsilon\) as above and then a finite integer \(K\) so that for all sufficiently large even \(N\),
\[
 \mathcal G_J(N)\ge 2|J|\mathfrak S(N)
  -\sum_{\substack{y\in J,\ P=N-y\text{ prime}\\
    y\text{ squarefree},\ P^-(y)>x^{1/\log L}\\
    5\le\omega(y)\le K}}
        \log P\,L\,\widetilde F(y)
  -\xi x\mathfrak S(N).                                         \tag{2}
\]
Here \(\mathcal G_J(N)\) is the original ordered prime-pair count weighted by \(\log P\log y\). The same inequality is valid if one retains only the positive part of \(\widetilde F\) in that sum. The residual includes **both odd and even ranks**: the calibration transfers a debit; it does not delete it without compensation. In particular rank five and the subsequent finite ranks are unpriced.

## 1. The true shifted-prime calibration is zero

For fixed \(\beta,\delta,\epsilon\) and each \(A>0\),
\[
 \sum_{\substack{y\in J\\P=N-y\text{ prime}}}
       \log P\,L\,\mu(y)^2 Z(y)=O_{\beta,\delta,\epsilon,A}(x L^{-A}).
                                                                    \tag{3}
\]
We give the local details to distinguish this from a prime-pair input. Discard the \(O(1)\) cases \(P\mid N\) in the fixed central range; their divisor-power scores are \(x^{o(1)}\). Thereafter \((y,N)=1\). Expand \(\mu(y)^2=\sum_{e^2\mid y}\mu(e)\) and truncate at \(e\le x^\rho\) with fixed \(2\rho<\epsilon\); the literal large-square error is power-small by the divisor bound and \(\sum_{e>x^\rho}x/e^2\ll x^{1-\rho}\). The progression modulus is \([d,e^2]\le x^{1/2-\epsilon+2\rho}<x^{1/2}\) at the actual residue \(N\). If \(q=[d,e^2]\), choices of \((d,e)\), including the mark \(p\mid d\), are at most \(\tau(q)^3\), and all coefficient factors in \(g,\phi\) are bounded. Apply maximal-prefix Bombieri--Vinogradov and ordinary divisor moments, as in [the squarefree short transfer](https://github.com/mxym/math/commit/18df7d45), to count actual primes with weight \(\log P\). The model density is \(|J|/\varphi(q)\); fixed powers of \(L\) are harmless. In the model extend \(e\) to infinity by exactly the \(e^{1/2}\) Rankin estimate in that proof. This extension still saves a fixed power after summing over the marked \(d\).

For \(A_p=1-1/[p(p-1)]\), the exact local \(e\)-sum factor is:
\[
 \begin{array}{c|c}
 p\nmid dN&A_p\\
 p\mid d,\ p\nmid N&1/(p-1)-1/[p(p-1)]=1/p\\
 p\mid N&1.
 \end{array}
\]
The final line means **both variables are coprime to the actual target**. Set \(b_M(m)=\mathbf1_{(m,M)=1}\mu(m)\prod_{r\mid m}(rA_r)^{-1}\). Writing each marked \(d=pm\) with \((p,mN)=1\) cancels the minus sign in (1). The resulting main term is exactly
\[
 |J|L\prod_{r\nmid N} A_r
    \sum_{p\nmid N}\frac{\phi(u_p)}{pA_p}
            \sum_m b_{pN}(m)g(u_p+\log m/L).                      \tag{4}
\]
The inverse-Mertens harmonic estimate from the same squarefree transfer applies uniformly with \(M=pN\le O(x^{3/2})\). It is unchanged by replacing \(N\) there by such an \(M\): the Euler correction at \(r\mid M\) has absolute zero moment \(O(L^{O(1)})\) and absolute quarter moment \(x^{o(1)}\), by splitting at \(r=L\); the other correction factors converge absolutely. The inner \(g\) is flat one at zero, with the start of its transition at
\[
 \tfrac12-2\epsilon-u_p\ge\delta/2-2\epsilon>0.
\]
Partial summation therefore gives \(O_A(L^{-A})\) uniformly in the actual prime \(p\). The outside harmonic sum is \(O_\beta(1)\) since \(p\ge x^\beta\) and \(u_p\le1/2\). This proves (3). In particular (3) is a **zero** recalibration, not a separate analytic reference to add to that for \(F\).

## 2. Exact ranks two, three, and four

Put \(h=T/2\), the *own* half on the physical row. Call the largest label a giant when \(u_{\max}>h\). On squarefree \(y>1\) no subset equals the own half, since its integer divisor would have square equal to \(y\). For comparison use \(Z^\sharp_\phi\) with \(g=\mathbf1_{[0,h)}\). For every actual mark of \(\phi\), \(g(u_p)=1\) and \(u_p<h\). Also \(g\le \mathbf1_{[0,h)}\). Complementing each divisor bit gives
\[
 Z(y)=\sum_{p\mid y}\phi(u_p)
          \sum_{e\mid y/p}\mu(e)g(u_p+\log e/L).                \tag{5}
\]
On a prime row \(Z=F=0\).

On a semiprime row with smaller log label \(a\), \(F=2a\) and \(Z=\phi(a)\). Thus \(\widetilde F\ge0\) and it vanishes for \(2\beta\le a\le1/2-\delta\). The residual is at most \(2a\) on \(a<2\beta\) and \(O(1)\) on \(a>1/2-\delta\). Fix the smaller prime and use the true two-form sieve in its largest prime cofactor and \(N-y\) from [the absolute-tail proof](https://github.com/mxym/math/commit/18df7d45). Since the largest log label is at least \(h\), its logarithm is \(\asymp L\). The two ranges cost
\[
 O((\beta+\delta)x\mathfrak S(N))+o(x\mathfrak S(N)).              \tag{6}
\]
Indeed \(\sum_{q<x^{2\beta}} (\log q/L)(q-1)/[q(q-2)]\ll\beta+L^{-1}\) (odd prime \(q\)), whereas the near-half harmonic width is \(O(\delta)+o(1)\) by the prime number theorem. We retain \((q,N)=1\); including the correction \((q-1)/(q-2)\le2\) is safe.

On a non-giant rank-three row, any two-factor subset has log above \(h\). Equation (5) therefore gives \(Z=\sum\phi\ge0\). On a giant rank-three row the only possible mark is in the two-factor cofactor, so (5) is a sum of \(\phi(u_p)(1-g(t))\) with the same cofactor log \(t\). It remains nonnegative. In both cases \(F=0\); rank three cannot create new positive debit.

On a non-giant rank-four row write its logs in increasing order \(a<b<c<d<h\). Each of the three complementary pairs of two-subsets has exactly one short member; short two-subsets form the star \(ab,ac,ad\) when \(a+d<h\), and the triangle \(ab,ac,bc\) otherwise. No three-subset is short. Thus, for those rows,
\[
 \begin{array}{c|c|c}
 &F&Z^\sharp_\phi\\ \hline
 \mathrm{star}&-4a&-2\phi(a)\\
 \mathrm{triangle}&4d-2T&\phi(d)-\phi(a)-\phi(b)-\phi(c).
 \end{array}                                                       \tag{7}
\]
For example \(F=2\sum_{u_A<h}(-1)^{|A|}(h-u_A)\) by even complement symmetry; the constant cancels because \(1-4+3=0\), verifying its two entries. Since shortening \(g\) only lessens negative pair terms and leaves each marked singleton unchanged, \(Z\ge Z^\sharp_\phi\) **rowwise** in this case. With the uncut mark \(\phi_\infty(u)=2u w(u)\), the star leaves nonpositive \(F-Z^\sharp\). The triangle does too: monotonicity makes \(1-w(d)\le1-w(a),1-w(b),1-w(c)\), giving
\[
 F-Z^\sharp_{\phi_\infty}
  \le 2(1-w(d))(d-a-b-c)\le0.
\]
When truncating \(\phi_\infty\) to \(\phi\), the lower three labels can only help. A positive residual can occur only if \(d>1/2-\delta\) and some lower label has nonzero \(\phi\), hence \(c\ge\beta\). The triangle condition gives
\[
 0<h-d=a+b+c-h< a,
 \qquad h-d\le\delta+O(L^{-1}).                                   \tag{8}
\]
Fix the two actual smallest primes of log sizes \(a,b\). By \(h=1/2+O(L^{-1})\), (8) puts \(c\) in an interval of exponent length at most \(\min(\delta,a)+O(L^{-1})\), above \(\beta\). Apply the true two-form upper in the largest prime after fixing \(a,b,c\). For fixed \(\beta\), on any such polynomial interval the harmonic \(c\)-sum is \(O_\beta(\min(\delta,a)+L^{-1})\): partial summation and the classical prime number theorem with arbitrarily many log powers suffice, uniformly in both endpoints. Multiplying by the remaining \(a,b\) prime harmonic weights gives
\[
 O_\beta\!\left(x\mathfrak S(N)\,\delta(1+|\log\delta|)^2\right)
       +o_\beta(x\mathfrak S(N)).                                  \tag{9}
\]
To check the small-label integral, bin \(v=\log(2/u)\) at unit spacing; by Chebyshev each bin has uniformly bounded prime harmonic weight. The ordered sum of \(\min(\delta,a)\) is majorized, up to an absolute constant, by
\[
 \int_0^2 \min(\delta,a)(1+\log(2/a))\,\frac{da}{a}
       \ll \delta(1+|\log\delta|)^2.
\]
The \(O(L^{-1})\) strip loss costs \(O((\log L)^2/L)\). The local product from fixing three genuine prime factors is at most \(2^3\), not a target-dependent loss.

Finally on a giant rank-four row \(F=0\): the short subsets are all divisors of its three-factor cofactor, and the full signed linear sum on them is zero. For each actual mark \(p\) in that cofactor, write \(a\le b\) for its other two log labels (not necessarily ordered relative to the mark). Its term in (5), aside from the bounded multiplier \(\phi\), is a double difference of \(g\), bounded by \(O(\min(1,a/\epsilon))\). It vanishes unless the cofactor log is between \(1/2-2\epsilon\) and \(h=1/2+O(L^{-1})\), since otherwise all subsets have \(g=1\). Fixing the two unmarked primes confines the harmonic interval for the actual mark \(p\ge x^\beta\) to width \(O(\epsilon+L^{-1})\). Using the same two-form upper in the largest factor and the preceding integral with \(\delta\) replaced by \(\epsilon\) proves a cost
\[
 O_\beta\!\left(x\mathfrak S(N)\,\epsilon(1+|\log\epsilon|)^2\right)
       +o_{\beta,\epsilon}(x\mathfrak S(N)).                        \tag{10}
\]
Counting the possible marks separately only increases the bound. This proof controls the cutoff-to-own-root issue without requiring an absolute bound for *all* sharp divisor counts near the root.

## 3. Absolute rank and least-factor tails of the transfer

In (5), differentiate in the \(D\) smallest labels **other than the mark and the global largest factor**, leaving all remaining difference operators bounded in sup norm by two. When the mark is the largest, simply use the \(D\) smallest other labels. This gives, for each marked term and \(r=\omega(y)\ge D+2\), the bound
\[
 \ll_D \epsilon^{-D}2^{r}\prod_{i=1}^{D}u_i,
\]
with the \(u_i\)'s the indicated unmarked fixed labels. If the mark is not the largest, fix it separately before doing the same true two-form upper in the largest factor. Its harmonic cost \(\sum_{x^\beta\le p\le x^{1/2}}(p-1)/[p(p-2)]\) is \(O_\beta(1)\). The remaining independent ordered labels number \(r-2\) (or \(r-1\) if the largest is the mark). In the exact ordered harmonic integral (8) of [the absolute-tail proof](https://github.com/mxym/math/commit/18df7d45), use this number and its \(D\) smallest labels. With an absolute \(D\) chosen large once, the integration gives a geometric tail despite the factor \(2^r\) and the \(O(r^2)\) sieve loss. In particular for \(K\ge D+2\),
\[
 \sum_{\substack{y\in J,\ P\text{ prime},\ y\text{ squarefree}\\
                 \omega(y)>K}}\log P\,L\,|Z(y)|
 \ll_\beta \epsilon^{-D}2^{-K}x\mathfrak S(N)+O_A(xL^{-A}).       \tag{11}
\]
The term \(P\mid N\) is again negligible. If the least label is below \(x^\sigma\) with \(\sigma<\beta\), it cannot be the mark. For \(r\ge3\) it is also not the global largest and may be retained in the differentiated set. Use the same insertion in the ordered integral (an exponential half of the largest \(v=\log(2/u)\)), saving \(O(\sqrt\sigma)\). For \(3\le r<D+2\) use just this one derivative; for rank two the only supported mark is the smaller factor, so the transfer vanishes in this tiny range. It follows that, on all ranks and uniformly for \(0<\sigma<\beta\),
\[
 \sum_{\substack{y\in J,\ P\text{ prime},\ y\text{ squarefree}\\
                 P^-(y)\le x^\sigma}}\log P\,L\,|Z(y)|
 \ll_\beta \epsilon^{-D}\sqrt\sigma\,x\mathfrak S(N)
          +O_A(xL^{-A}).                                           \tag{12}
\]
Constants in (11)--(12) also depend on the fixed smooth transition and \(J_0\); they do not require derivatives of the mark or a limit of growing polynomial ranks.

Apply (3) and (12) at \(\sigma=1/\log L\) to replace \(F\) by \(\widetilde F\) in the calibrated [true even-cusp identity](../true_even_cusp_rank_tail/Proof.md). The sign of this replacement is immaterial to the error because the transfer has zero total sum. The original cusp may still be summed over all ranks since it already vanishes on every odd rank. Its published high tail on these same rough rows is \(O_c(e^{-cK}x\mathfrak S(N))\); the *additional* absolute tail is precisely (11), not a second copy of the original cusp. Dropping the nonpositive ranks two through four, with the positive errors in (6), (9), and (10), proves (2) by choosing first \(\beta\) small, then \(\delta\) small in terms of \(\beta\), then \(\epsilon\), then \(K\), then \(N\). These choices need not be uniform when any of the fixed kernel parameters varies with \(N\).

## Scope

The actual identity and the true two-form estimates are all at the same prescribed even center. The transfer removes the need to upper-bound true semiprimes directly at natural scale, and never charges genuine rank three. It does not make the remaining rank-five-and-higher sum small: new positive terms can occur there, including on odd ranks that had zero original cusp. For example, at five log sizes approximately \(0.18,0.19,0.20,0.21,0.22\), take \(2\beta<0.18\) and sufficiently small \(\delta,\epsilon\). Every pair is short and every triple is outside the cutoff. Here \(F=0\), \(Z=-3\sum_p2u_p=-6T\), and \(\widetilde F=6T>0\). Such individual rows with actual opposite primes exist: choose five actual primes in fixed multiplicative boxes around these five powers of a common parameter, then choose an actual prime \(P\) at a fixed ratio to their product \(y\) so that \(y/(N/2)\) belongs to the interior of \(J_0\), using the prime number theorem at both stages. This does not give their density at any prescribed target.

The only conclusion here is the signed finite-rank interface (2).

The exact combinatorial fixtures in `check.py` can be replayed with `python3 -O -B check.py`. They use rational log labels and piecewise linear test cutoffs to check the coefficient identities, including fringe necessity and the rank-five adverse example. They do not replace any analytic estimate.
