# Sharp exponential separation for Chen–Dai compromise pairs

Fix \(0<u<1\). Following [Chen and Dai (2007)](https://www.impan.pl/shop/publication/transaction/download/product/82089), two positive integers \(s,t\) are **\(u\)-compromise** if one can choose a prime divisor for every integer in each of
\[
I_s=[s,(1+u)s]\cap\mathbb Z,\qquad I_t=[t,(1+u)t]\cap\mathbb Z,
\]
so that any prime chosen on both sides divides \(t-s\). For \(s\ge2\), let \(m_u(s)\) be the least \(t>s\) with this property.

**Theorem.** For every fixed \(u\in(0,1)\) and every fixed \(A>0\),
\[
\boxed{\ \log m_u(s)=u s+O_{u,A}\!\left(\frac{s}{(\log s)^A}\right).\ } \tag{1}
\]
In particular this answers Chen and Dai's **Problems 1 and 2** on p. 127 affirmatively and gives the sharp first-order exponential separation. In their application to [Erdős problem 441](https://www.erdosproblems.com/441), let \(R_1(X)\) be the maximum number of elements that may be adjoined to Erdős's specified construction without violating the pairwise LCM bound \(X\). Then unconditionally
\[
R_1(X)\ \le\ 2\log^* X+O(1). \tag{2}
\]
More precisely, the number of distinct individually admissible offsets is at most \(\log^* X+O(1)\), and there are infinitely many \(X\) for which an actual extension uses at least \(\log^* X-O(1)\) distinct offsets.

Chen and Dai previously proved \(R_1(X)=O(\log\log X)\) unconditionally and proved (2) conditional on their second question. Their lower construction already gave \(R_1(X)\ge\log^* X-O(1)\) infinitely often. The theorem concerns extension of the prescribed set, **not** the gap between that set and the unrestricted maximum, nor the exact leading coefficient for \(R_1(X)\). Here \(\log^* y\) counts the iterations of the natural logarithm needed to reach at most \(1\); changing the endpoint convention affects only a bounded term.

## 1. Forced primes and the upper construction

If \(p^j\in I_s\), then \(p\) must be chosen on the \(s\)-side, since it is the only prime divisor of \(p^j\). Call such a prime **available** if it does not divide \(t-s\). It cannot be chosen on the \(t\)-side. Consequently, finding an integer in \(I_t\) whose prime factors are all available disproves \(u\)-compromise.

For the opposite direction, let \(M_s\) be the product of all primes in \(I_s\) and all primes \(\le\sqrt{(1+u)s}\), taking each prime once. Every \(n\in I_s\) has a prime divisor in \(M_s\): for composite \(n\), use its least prime divisor, and otherwise use \(n\) itself. Thus \(s\) and \(t=s+M_s\) are \(u\)-compromise; every prime chosen on the \(s\)-side already divides \(t-s\), regardless of choices on the other side. With \(\vartheta(x)=\sum_{p\le x}\log p\), the effective prime number theorem gives
\[
\log M_s=u s+O_{u,A}(s/(\log s)^A).
\]
The contribution of the small primes is \(O_u(\sqrt s)\), and inclusion of a prime at the lower endpoint changes the sum by at most \(\log s\). Since \(M_s=\exp((u+o(1))s)\), the same estimate holds for \(\log(s+M_s)\). This proves the upper bound in (1).

We use the prime number theorem only in the form
\[
\vartheta(x)=x+O_B(x/(\log x)^B),\qquad
\pi(x)=\operatorname{li}(x)+O_B(x/(\log x)^B)
\quad(B>0\text{ fixed}). \tag{3}
\]
For example the first follows from [Johnston and Yang, equation (1.8)](https://arxiv.org/abs/2204.01980) and the second by partial summation.

## 2. Moderate values of \(\log t\): two nearby powers of \(s\)

Write \(L=\log s,\ U=\log t,\ h=\log(1+u)>0\). We show first that, for any fixed \(D>1\), all \(t>s\) with \(U\le L^D\) fail to be \(u\)-compromise for sufficiently large \(s\) (depending on \(D,u\)).

Choose \(k=\lceil 4\sqrt{L/h}\rceil\), so \(L/(k(k+1))\le h/16\). The values
\[
L\left(\frac a k+\frac b{k+1}\right),\qquad a,b\in\mathbb Z_{\ge0},\quad a+b\ge k+1,
\]
include **every** lattice point of mesh \(L/(k(k+1))\) above or at \(L\). Indeed, for a fixed \(n=a+b\) their numerators in this mesh run through all integers in \([nk,n(k+1)]\); for successive \(n\ge k+1\), the intervals overlap and the first starts at \(k(k+1)\). Choose \(a,b\) with
\[
U+h/4\ \le\ L\left(\frac a k+\frac b{k+1}\right)\ \le\ U+h/2 .
\]
Their sum \(n\) is at most \((k+1)(U+h/2)/L=O_u(L^{D-1/2})\).

Set \(\eta=h/(16(n+k+1))\). For \(i=k,k+1\), the interval
\[
[s^{1/i},\, e^\eta s^{1/i}]
\]
contains a prime not dividing \(t-s\). To verify this, its lower endpoint \(z=s^{1/i}\) satisfies \(\log z\asymp_u \sqrt L\), and its relative length is \(\asymp\eta\gg_u L^{-(D-1/2)}\). By (3) with a sufficiently large fixed \(B\), the prime count is \(\gg \eta z/\log z\): the \(\operatorname{li}\) increment has this size, and the two endpoint error terms are smaller. In contrast the count of primes \(\ge z\) dividing \(t-s\) is at most \(U/\log z\), polynomial in \(L\). Choose \(p\) for \(i=k\) and \(q\) for \(i=k+1\). Their respective powers \(p^k,q^{k+1}\) are in \(I_s\), since each log overshoot above \(L\) is at most \(i\eta\le h/16\). Both are available. Also
\[
U+h/4\ \le\ \log(p^a q^b)\ \le\ U+h/2+n\eta<U+h.
\]
The integer \(p^a q^b\in I_t\) has only available prime factors, proving the claim. An exponent may be zero; this does not affect the argument.

## 3. Larger values of \(\log t\): two primes in the first interval

Fix \(A>0\) and suppose \(U\le us-s/L^A\). The log weight of primes in \(I_s\) is \(us+O_{u,A}(s/L^{A+2})\), by (3). Those dividing \(t-s\) have total weight at most \(\log(t-s)\le U\); hence the primes remaining in \(I_s\) have weight at least \(s/(2L^A)\) for large \(s\). Let \(p,q\) be the smallest and largest remaining primes. The same \(\vartheta\) estimate uniformly over \([s,(1+u)s]\) shows that this remaining set has diameter at least \(s/(4L^A)\): if smaller, even the weight of all primes between its endpoints would be less than \(s/(2L^A)\). Both \(p,q\) are available (already their first powers are in \(I_s\)).

Put \(P=\log p,\ Q=\log q,\ d=Q-P\). Then
\[
d\ge (q-p)/q\gg_u L^{-A},\qquad 0<d\le h,\qquad P\le L+h.
\]
For \(n\ge n_0=\lceil P/d\rceil\), the intervals \([nP,nQ]\) overlap successively because \(n d\ge P\); together they cover \([n_0P,\infty)\). Here \(n_0P=O_u(L^{A+2})\). If \(U\ge n_0P\), choose such an interval containing \(U\). The values \(nP+b d\) for integers \(0\le b\le n\) span the interval with spacing \(d\le h\). Choosing the first value \(\ge U\) produces
\[
U\le\log(p^{n-b}q^b)\le U+h.
\]
Again the resulting integer belongs to \(I_t\) and has only available prime factors. If \(U<n_0P\), Section 2 applies with, for instance, \(D=A+3\) for sufficiently large \(s\). Thus no \(t\) with \(U\le us-s/L^A\) works. Together with Section 1 this proves (1).

For compatible \(s<t\) and fixed \(u>0\), in particular \(\log t\ge (u/2)s\) for all large \(s\). Therefore \(\log\log t\ge \log s+O_u(1)\), which is stronger than the hypothesis in Chen and Dai's Problem 2 with \(r=2\). For every fixed \(r\ge1\), \(\log^{(r)}t-\log^{(r)}s\to+\infty\) uniformly over these pairs, proving their Problem 1 for all \(r\). These deductions also show why the sharp separation is substantially stronger than merely growing faster than a fixed power.

## 4. Application to extensions of Erdős's LCM construction

Let \(k=\lfloor\sqrt{X/2}\rfloor\). The given set is \(B_X=\{2j:1\le j\le k\}\cup\{j:1\le j\le k,\ j\text{ odd}\}\). Any additional integer compatible with every member of \(B_X\) is either \(a=2(k+s)\) or \(a=k+s\) odd, for some integer \(s>0\). Call \(s\) an individually admissible offset if at least one of these two choices works. We give the reduction to compromise pairs explicitly.

Take a prime \(q\le k\) with \(q\sim k\), by the prime number theorem. Write \(m=k+s\) and note that for either choice of \(a\), \([a,2j]=2[m,j]\). If \(q\mid m\), then \(m=q b\) with \(b>1\). At least one of \(q-1,q-2\) is not divisible by \(b\), so for that \(j\), \([a,2j]=2q[b,j]\ge4q(q-2)>X\) for large \(X\), impossible. If \(q\nmid m\), compatibility with \(2q\) gives \(m\le X/(2q)=k+o(k)\). Thus \(s=o(k)\) uniformly over all individually admissible offsets.

For any fixed \(u\in(0,1)\), if such an \(s\) exceeds a sufficiently large constant, then for \(0\le i\le\lfloor us\rfloor\),
\[
(k+s)(k-i)-(k+1)^2
=k(s-i-2)-si-1>0
\]
uniformly: \(s-i\ge(1-u)s\), while \(s=o(k)\). As \(X<2(k+1)^2\), comparison with \(2(k-i)\in B_X\) forces \(\gcd(k+s,k-i)>1\). This is \(\gcd(k+s,s+i)>1\), so one can choose a prime divisor of \(s+i\) that divides \(k+s\). All primes in \(I_s\) are forced in this way, giving \(s=O(\log X)\) by (3), since their product divides \(k+s\).

For any two sufficiently large individually admissible offsets \(s<t\), make these prime choices independently. Every prime chosen on both sides divides \(k+s\) and \(k+t\), hence \(t-s\). Thus \(s,t\) are \(u\)-compromise without even needing mutual compatibility of the two additional integers. Fix \(u=1/2\). By (1), for these offsets \(t\ge\exp(c s)\) for some constant \(c>0\). With \(y(s)=c s/2\), for all sufficiently large \(s\) this implies \(y(t)\ge\exp(y(s))\). Consecutive large offsets therefore increase the log-star of \(y(s)\) by at least one. The largest offset is \(O(\log X)\); discarding the bounded set of small offsets, there can be at most \(\log^* X+O(1)\) distinct offsets. Each supplies at most two integers, proving (2). Finally [Chen and Dai's proof of Theorem 1(ii), pp. 130–131](https://www.impan.pl/shop/publication/transaction/download/product/82089) adds its \(\log^* X-O(1)\) integers at distinct offsets (all are of the even form), so the offset-count bound is sharp to a bounded term on a subsequence.

The [companion checker](verify_erdos441_compromise_spacing.js) verifies the exact integer identities behind the exponent grids, forced prime and simultaneous CRT criteria, and the reduction from an admissible even or odd member to its offset. The limiting bounds use the proof and prime number theorem above, not any finite numerical experiments.
