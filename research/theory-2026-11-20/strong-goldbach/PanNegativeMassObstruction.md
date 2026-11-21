# A negative-only Goldbach budget fails on a positive density of actual targets

Let \(P\) be even and use Pan's actual [long-divisor remainder in Huang–Li, (2)–(6)](https://arxiv.org/html/2005.03811v2#S1),
\[
 R_3(P)=\sum_{n+r=P}a(n)a^*(r),\quad a(n)=\sum_{d\mid n,\ d>Q_0}\mu(d)\log d,\quad
 a^*(n)=\sum_{d\mid n,\ d>Q_0,\ (d,P)=1}\mu(d)\log d,\quad Q_0=\sqrt P/(\log P)^{20}.
\]
The singular series is \(\mathfrak S(P)=2C_2\prod_{l\mid P,l>2}(1+1/(l-2))\), products indexed by primes, \(C_2=\prod_{l>2}(1-(l-1)^{-2})\). For fixed \(0<k<1/2\) let \(M_j(P;k)\) be the sum of the magnitudes of **negative terms only**, in *one* designated orientation with one actual prime and the other input squarefree of rank \(j\) and least prime \(>P^k\). Either orientation may be used. At rank 3 one may optionally further require the largest prime factor of the composite to be less than its square root.

**Theorem.** For fixed \(0<k<1/2\),
\[
 \frac{\sum_{X<P\le2X,\ 2\mid P}M_2(P;k)}
      {\sum_{X<P\le2X,\ 2\mid P}P\mathfrak S(P)}
 \longrightarrow I_2(k)=\log(2(1-k)).
\]
For rank three in the same ratio, for \(0<k\le1/4\), the limit is
\[
 I_3(k)=\frac{\pi^2}{12}-\int_0^k\frac{-\log(1-2t)}{t(1-t)}\,dt .
\]
The total from **both** orientations has twice these limits. For \(k=333/4000\), one orientation of just ranks 2 and 3 has limiting ratio exceeding 1.23. Both together exceed 2.46. For any fixed threshold strictly below the respective limit, the negative weight exceeds that threshold times \(P\mathfrak S(P)\) on a positive lower proportion of even targets on each sufficiently large dyadic interval. In particular even the two semiprime orientations *alone* exceed one full main term on a positive density whenever \(k<1-\sqrt e/2\).

This is an obstruction to a uniform proof which simply discards every positive term and budgets these negative terms against the single singular-series main term. It is not an obstacle to a bound on the **signed** remainder. It gives no lower bound on any individual prime-pair count. The pairs used in this obstruction never have two prime summands.

## First mean, retaining the physical parity and the moving cutoff

Write \(L=\log X\) for this mean calculation. For either orientation the prime labels dividing \(P\) have combined error \(O_j((\log P)^3)\) per target; otherwise \((p,P)=(r,P)=1\). A prime below \(Q_0\) has weight zero rather than \(-\log p\). We first work on \(p,r\ge\eta X\) for any fixed small \(\eta>0\), so \(a(p)=a^*(p)=-\log p\). On the complement the total error in replacing or omitting the true weights is \(O_{j,k}(\eta X^2)+o_{j,k,\eta}(X^2)\): each true composite weight is at most \(2^j\log(2X)\). For \(p<\eta X\), sum its log weight by Chebyshev and observe that the number of eligible \(r\le2X\) is \(O_{k,j}(X/L)\). For \(r<\eta X\) that count is \(O_{k,j}(\eta X/L)\), while the sum of all prime log weights up to \(2X\) is \(O(X)\). For the two counting assertions peel one prime \(q>X^k\) from \(r=Aq\): at upper endpoint \(U\), count \(q\le U/A\) by \(O_k(U/(AL))\) if \(U/A\ge X^k\), and sum over the remaining \(j-1\) prime labels in \([X^k,2X]\) using their bounded reciprocal sum. Here and below \(j\) is fixed. All retained prime inputs and all composite inputs are odd, so every such pair yields an even target; there is **no additional parity factor** restricting our pair count.

Put \(x_i=\log l_i/L\) for \(j-1\) labeled prime factors of the composite, \(A=\prod l_i\), and \(u=1-\sum_{i<j}x_i\). The last prime \(q=r/A\) then has log exponent \(u+O_\eta(1/L)\). In this full labeling every squarefree physical composite is counted exactly \(j!\) times. Repeated prime factors can be removed or restored in asymptotic upper bounds at total cost \(O_{j,k}(X^{2-k}L^2)\), since \(r\le2X\) and \(l^2\mid r\) with \(l>X^k\). Set \(x_j=u\). The limiting normalized coefficient off the subset-midpoint walls is
\[
 F_j(x)=\sum_{S\subseteq[j],\ \sum_{i\in S}x_i>1/2}(-1)^{|S|}\sum_{i\in S}x_i .
\]
The threshold exponent is \(1/2+O(\log L/L)\), uniformly in \(X<P\le2X\); \(P^k\) has exponent \(k+O_k(1/L)\). Away from an arbitrarily thin fixed neighborhood of these finitely many equality walls, the labels satisfy the exact cutoffs eventually and \(a(r)/L=F_j(x)+O_{j,\eta}(1/L)\). This accounts also for the exceptional semiprimes where *both* primes are above the moving cutoff (then \(a=0\)) or both below (then \(a=\log r\) on the retained macroscopic inputs): their macroscopic exponents must approach the midpoint. For the optional balanced restriction, the limiting wall is \(\max x_i=1/2\).

Here is the integration step. On any fixed physical rectangle \(p/X\in[c,d],\ r/X\in[e,f]\), endpoints at least \(\eta\), the prime log mass in the first interval is \((d-c)X+o(X)\) by the prime number theorem. For fixed \(A\) with \(u\ge k/2\), the number of last primes in \([eX/A,fX/A]\) is
\[
 (f-e)\frac{X}{A uL}(1+o_{k,\eta,e,f}(1))
\]
uniformly by that same theorem since \(X/A=X^u\). This factor cancels the log scale of the composite weights. The remaining measures \(\sum_{l_i}1/l_i\) on any compact exponent range in \((0,1]\) converge to \(dx_i/x_i\) by prime partial summation, and their products converge on boxes. The integrands are bounded on \(x_i,u\ge k/2\); every wall neighborhood has limiting measure tending to zero with its width, by the same box argument using the bounded majorant \(|a|/L\le O_j(1)\). Rectangles approximate the domain \(p/X,r/X\ge\eta,\ 1<(p+r)/X\le2\), whose boundary has zero area. Letting \(\eta\downarrow0\) gives total area \(3/2\). Thus the numerator divided by \(3X^2/2\) tends to
\[
 I_j(k)=\frac1{j!}\int_{\substack{\sum x_i=1\\x_i\ge k}}\frac{[F_j(x)]_+}{\prod_i x_i}\, dx_1\cdots dx_{j-1}.
\]
The same reasoning applies to an additional bounded polyhedral exponent mask, up to boundaries of zero measure.

For the denominator, expand \(\mathfrak S(2m)/(2C_2)\) in the divisibility indicators \(d\mid m\) with nonnegative weights \(\lambda(d)=\prod_{l\mid d}1/(l-2)\) for odd squarefree \(d\). The average of each indicator is \(1/d\), and tails in initial intervals are dominated by \(\sum \lambda(d)/d<\infty\). Its product equals \(1/C_2\). Thus \(\mathfrak S\) averages 2 on even integers, and partial summation gives the stated denominator \(\sim3X^2/2\).

## Evaluation and ordinary positive density

On the open rank-2 face, \(F_2=\min x_i\); integrating over the smaller coordinate gives \(I_2=\int_k^{1/2}dt/(1-t)\). On the rank-3 face \(F_3=1\) when \(\max x_i<1/2\), and zero when \(\max x_i>1/2\), by the subset formula. For one designated coordinate \(t\in(0,1/2)\) on the balanced face the other freely varying coordinate \(v\) has range \(1/2-t<v<1/2\). Integrating \(1/(t v(1-t-v))\) in \(v\) gives \(2[-\log(1-2t)]/[t(1-t)]\). At most one coordinate can lie strictly below \(k\le1/4\), as otherwise the third exceeds half. Dividing by \(3!\) and accounting for the three possible deletions gives the stated subtraction from \(I_3(0)\). The full improper integral is finite: substitution \(z=2t\) gives
\[
 3I_3(0)=\int_0^1[-\log(1-z)]\left(\frac1z+\frac1{2-z}\right)dz=\zeta(2)+(1-2^{-1})\zeta(2)=\frac{\pi^2}{4}.
\]
For the second integral substitute \(y=1-z\) and integrate the geometric expansion of \(1/(1+y)\), using dominated convergence of its bounded partial sums. Since \(-\log(1-2t)\le2t/(1-2t)\), the deletion costs at most \(2\log((1-k)/(1-2k))\). At \(k=333/4000<1/12\), monotonicity gives
\[
 I_2(k)+I_3(k)\ge \log(11/6)+\pi^2/12-2\log(11/10)>1.23 .
\]
For instance the elementary bounds \(\pi>3.14,\ \log(11/10)<0.096,\ \log(11/6)>0.605\) suffice. The numerical constants are not optimized.

For completeness these large first means are not supported only on a zero-density family with enormous local factors. For fixed \(j,k\), uniformly in the target, \(M_j(P;k)\ll_{j,k}P\mathfrak S(P)\): by the [two-prime upper sieve, §1](pan-rough-rank/Proof.md) applied to \(p=P-Aq\), \(Y=P/A\ge P^k\), there are \(O_{j,k}(\mathfrak S(P)Y/L^2)\) possibilities when \(p>P^{3/4}\). Peel all but \(q\) at total reciprocal cost \(O_{j,k}(1)\), the logs cost \(O_j(L^2)\), and the \(O(P^{3/4})\) small-prime inputs (and target prime divisors) are negligible. The same Euler-product argument as for the first singular-series moment gives \(\sum_{X<P\le2X,\ 2\mid P}\mathfrak S(P)^2\ll X\): the positive local divisor expansion now has prime coefficient \((1+1/(l-2))^2-1=O(1/l)\). For any fixed threshold \(h\) strictly below the limiting first-mean ratio of the chosen rows, the weight \(\sum_{P\in B}P\mathfrak S(P)\gg X^2\) on \(B=\{P:M(P)>hP\mathfrak S(P)\}\) follows by the uniform upper bound. Cauchy–Schwarz and the displayed second-moment bound give \(X^2\ll X^{3/2}|B|^{1/2}\), hence \(|B|\gg X\). This is a statement about actual even targets, not a mean-square surrogate for a fixed-target signed inequality.

This is separate from [the repository's positive-only Vaughan obstruction](UnmarkedVaughanPositiveRankThree.md), which concerns a different semiprime-weighted row with the opposite sign. [Chan's November preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) also separates semiprime-profile integrals and a prime-complement step for its own weight. The conclusion here is a genuine dyadic first mean and positive-density obstruction for the exact raw Pan terms, not an all-target asymptotic for their prime correlation.
