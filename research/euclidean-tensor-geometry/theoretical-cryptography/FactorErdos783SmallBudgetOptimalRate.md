# Sharp finite-size gaps for the small coprime sieve at small budgets

Let \(N\) be an integer and let \(A\subseteq\{2,\ldots,N\}\) be pairwise coprime. Write
\[
\mu(A)=\sum_{a\in A}\frac1a,\qquad
\sigma_N(A)=\frac1N\#\{1\le n\le N:\ a\nmid n\text{ for all }a\in A\},
\qquad
F_N(C)=\min_{\mu(A)\le C}\sigma_N(A).
\]
Discarding larger moduli preserves the minimum. All logarithms are natural.

**Theorem.** For fixed \(C\in(0,\log 2]\), the following hold.

1. If \(0<C<\log 2\) and \(C\) is not the reciprocal of an integer, then
   \[
   F_N(C)-(1-C)=N^{-(1-e^C/2)+o(1)}.
   \]
2. If \(C=1/a\) for an integer \(a\ge2\), then for every \(N\ge a\),
   \[
   F_N(C)=1-\frac{\lfloor N/a\rfloor}{N}.
   \]
   For all sufficiently large \(N\), the only minimizing set is \(\{a\}\).
3. At the endpoint the gap has an asymptotic constant:
   \[
   F_N(\log 2)-(1-\log 2)\sim
   \left(\frac{\log\log N}{\log N}\right)^2.
   \]

In particular, taking consecutive primes downwards from \(N\) until the budget is exhausted is **strictly suboptimal** for every fixed \(0<C\le\log 2\) and all sufficiently large \(N\), even though that choice is asymptotically optimal at order one. The theorem concerns the already solved first-order version of [Erdős problem 783](https://www.erdosproblems.com/783), and does not identify the exact nonreciprocal minimizers or address gaps for \(C>\log 2\).

## 1. Exact deficit and a stability lemma

Let \(D(n)=\#\{a\in A:a\mid n\}\), with expectation over uniform \(n\in[1,N]\). The gap \(\delta=\sigma_N(A)-(1-C)\) has the exact decomposition
\[
\delta=C-\mu(A)+\frac1N\sum_{a\in A}\{N/a\}+\mathbb E(D-1)_+ . \tag{1}
\]
Indeed \(\mathbf 1_{D>0}=D-(D-1)_+\), and \(\mathbb E D=\sum_a\lfloor N/a\rfloor/N\). All three terms in (1) are nonnegative. For any integer \(r\ge0\),
\[
\mathbb E\binom Dr\le \frac{\mu(A)^r}{r!}
\]
because the least common multiple of a subset of \(A\) is its product. Expanding \(e^D=(1+(e-1))^D\) gives \(\mathbb E e^D\le e^{C(e-1)}\). Consequently, along any sequence with \(\delta\to0\),
\[
Q:=\mathbb E\binom D2=\sum_{\{a,b\}\subset A}\frac{\lfloor N/(ab)\rfloor}{N}=o(1). \tag{2}
\]
For example, restrict first to \(D\le R\), where \(\binom{D}{2}\le R(D-1)_+\); the part \(D>R\) is \(O_C(e^{-R/2})\). If \(ab\le N\), the corresponding summand in (2) is at least \(1/(2ab)\).

For every \(Y\ge2\), the composite members of \(A\) exceeding \(Y\) have total reciprocal weight \(O(Y^{-1/2})\). Map each to its least prime factor \(p\); pairwise coprimality makes this injection. For \(p\le\sqrt Y\) there are at most \(\sqrt Y\) terms each at most \(1/Y\); for \(p>\sqrt Y\) use \(a\ge p^2\) and bound by \(\sum_{m>\sqrt Y}1/m^2\).

The following consequences apply whenever \(\delta\to0\) (and then \(\mu(A)=C+o(1)\)):

* If some fixed \(a_0\in A\) occurs on a subsequence, the weight of the other \(b\le N/a_0\) is at most \(2a_0 Q=o(1)\). The weight of \(b>N/a_0\) is \(o(1)\) by the composite bound and Mertens' theorem for primes. Therefore \(C=1/a_0\).
* If \(\min A\to\infty\), write \(m=\sum_{a\in A,\ a\le\sqrt N}1/a\). Every pair among these \(a\)'s has product \(\le N\), giving \(m^2\le4Q+m/\min A\), hence \(m=o(1)\). The composite bound then shows that all but \(o(1)\) of the budget comes from selected primes \(>\sqrt N\).

In particular, for \(C\) nonreciprocal, \(\min A\to\infty\) along any sequence with \(\delta\to0\). At \(C=\log 2\), which lies strictly between \(1/2\) and \(1\), the selected primes above \(\sqrt N\) omit only \(o(1)\) of the reciprocal weight of **all** primes in \((\sqrt N,N]\), since their total weight is \(\log 2+o(1)\). For a reciprocal budget \(1/a\), the same conclusions for \(\min A\to\infty\) hold along any near-minimizing sequence that omits \(a\), by the first bullet.

## 2. Subcritical budgets

Write \(\beta=e^C/2\in(1/2,1)\). Take an initial segment of the primes \(>\sqrt N\), in increasing order, stopping just before including the next prime would exceed the budget. For fixed \(\epsilon>0\) small, the available mass below \(N^{\beta-\epsilon}\) is less than \(C\), and below \(N^{\beta+\epsilon}\) it is greater than \(C\), by Mertens' theorem. Thus the cutoff and the first rejected prime are \(N^{\beta+o(1)}\). The unused budget is at most the reciprocal of that first rejected prime (in particular at most \(N^{-1/2}\)); pairs do not intersect in \([1,N]\). The rounding term in (1) is at most the number of selected primes divided by \(N\), which is at most \(N^{\beta-1+o(1)}\). This gives the upper bound.

For the matching lower bound, suppose there is a subsequence with \(\min A\to\infty\) and
\[
\delta\le N^{-(1-\beta+\epsilon)}
\]
for some fixed \(\epsilon>0\). We may decrease \(\epsilon\) so \(b=\beta-\epsilon/2>1/2\); set \(\tau=N^{-\epsilon/4}\). Among \(a>N^b\), those with \(\{N/a\}\ge\tau\) have total weight at most \(N\delta/(\tau N^b)\le N^{-\epsilon/4}\), by (1). For the rest it is enough to bound the weight of **all** integers in a dyadic band \([T,2T)\cap[2,N]\) with \(\{N/a\}<\tau\), for \(T\ge N^b/2\). For \(j=\lfloor N/a\rfloor\), the condition requires
\[
\frac{N}{j+\tau}<a\le\frac{N}{j}.
\]
There are \(O(N/T)\) relevant \(j\ge1\), each comparable to \(N/T\), so the intervals have length \(O(\tau T^2/N)\) and contain \(O(\tau T+N/T)\) integers in total. Their weight in the band is \(O(\tau+N/T^2)\). Summing over the bands gives \(o(1)\). Thus \(a>N^b\) contribute \(o(1)\), as do \(a\le\sqrt N\) by Section 1 and the remaining composites. This leaves
\[
C+o(1)=\mu(A)\le\sum_{\sqrt N<p\le N^b}\frac1p+o(1)=\log(2b)+o(1),
\]
a contradiction since \(\log(2b)<C\). The fixed-modulus alternative is excluded for nonreciprocal \(C\), proving the rate in item 1.

For \(C=1/a\), the universal bound \(\sigma_N(A)\ge1-C\) and the fact that \(N\sigma_N(A)\) is integral give \(\sigma_N(A)\ge1-\lfloor N/a\rfloor/N\). The singleton attains it. If infinitely many optimizing sets omit \(a\), the stability lemma gives \(\min A\to\infty\) along that subsequence. They have \(\delta<1/N\), contrary to the same lower-bound argument, since \(1-\beta<1/2\). This proves eventual uniqueness.

## 3. Critical log-scale pair weights

For the rest of the proof, \(C=\log 2\). Set \(L=\log N\), \(\ell=\log L\), \(w=\ell/L\), and for a prime \(p\) put
\[
s(p)=\frac{\log p-L/2}{\ell}.
\]
For any fixed bounded \(u<v\), Mertens' theorem with error \(O(1/\log x)\) gives
\[
\sum_{u<s(p)\le v}\frac1p=(2(v-u)+o(1))w. \tag{3}
\]
Indeed the difference of the logarithms of \(\log p\) at the endpoints is
\(\log((L/2+v\ell)/(L/2+u\ell))\), and the Mertens error is \(o(w)\).
On a fixed bounded \(s\)-interval, the reciprocal prime measure normalized by \(w\) thus tends to \(2\,ds\). Normalized products of such measures converge on triangles: approximate each by inner and outer unions of rectangles, and then shrink the grid mesh, since the boundary has zero area. The same assertion holds when the triangle cutoffs move by \(o(1)\), by bracketing with fixed triangles.

For fixed \(B>0\) put \(Y_B=N/L^B\). A suffix of primes up to \(Y_B\), with total weight \(\log 2+o(w)\) and at most one partially taken prime at its bottom, has lower cutoff
\[
Z_B=\sqrt N\,L^{-B/2+o(1)}. \tag{4}
\]
To see this, fixed power cutoffs \(N^{0.4}\) and \(N^{0.6}\) bracket the desired lower cutoff by Mertens' theorem. The possible endpoint contribution \(O(N^{-0.4})\) is negligible. Then
\(\log(\log Y_B/\log Z_B)=\log 2+o(w)\), so \(\log Z_B=(L-B\ell)/2+o(\ell)\).

In particular, for fixed \(0\le\eta<B\), the ordered product weight of this suffix on \(pq\le N/L^\eta\), normalized by \(w^2\), tends to
\[
4\operatorname{area}\{(s,t):s,t\ge -B/2,\ s+t\le-\eta\}
=2(B-\eta)^2 . \tag{5}
\]
The product bound confines both coordinates to a bounded interval, (4) controls the lower edges, and (3) applies. Partially including an endpoint prime does not affect the limit. Diagonal weight in these suffixes is \(O(N^{-0.4})=o(w^2)\).

## 4. Critical upper bound

Take the longest suffix of primes up to \(Y_1=N/L\) whose weight does not exceed \(\log 2\), with no fractional inclusion. Its slack is less than the reciprocal of the next prime below the suffix; fixed power cutoffs as above show this is \(o(w^2)\). Its rounding loss is \(\le\pi(Y_1)/N=O(1/L^2)=o(w^2)\). Its redundancy is at most the unordered pair weight on \(pq\le N\), by (2) and \((D-1)_+\le\binom D2\). By (5) with \(B=1,\eta=0\) this is \((1+o(1))w^2\). Hence \(\limsup (F_N(\log 2)-(1-\log 2))/w^2\le1\).

## 5. Critical lower bound

Let \(A\) be an optimizer, so \(\delta=O(w^2)\) from Section 4. Take \(\theta=7/20\). The primes of \(A\) in \((\sqrt N,N^{3/5}]\) carry weight \(\log(6/5)+o(1)\) by the stability lemma. For every such prime \(q\) and every \(a\in A\) with \(a\le N^\theta\), we have \(aq\le N^{19/20}\). At most one such \(q\) divides each \(n\le N\). When one does, \((D(n)-1)_+\) is at least the number of small \(a\)'s dividing \(n\). Consequently
\[
\mathbb E(D-1)_+\ \ge\
\sum_{\substack{a\in A,\ a\le N^\theta\\q\in A\text{ prime},\ \sqrt N<q\le N^{3/5}}}
\frac{\lfloor N/(aq)\rfloor}{N}
\ \gg\ \sum_{a\in A,\ a\le N^\theta}\frac1a.
\]
Here pairwise coprimality and \(\lfloor N/(aq)\rfloor/N\ge 1/(2aq)\) justify the final step. Thus the small weight is \(O(w^2)=o(w)\), and the weight of composites above \(N^\theta\) is also \(o(w)\).

Fix \(0<B<1\). We show that the selected primes \(p>Y_B\) have weight \(o(w)\). Let \(u=(1-B)/2>0\) and \(\tau=L^{-u}\). Those with \(\{N/p\}\ge\tau\) have weight \(\le N\delta/(\tau Y_B)=O(w^2 L^{B+u})=o(w)\). For the others, reuse the intervals \((N/(j+\tau),N/j]\), now for \(1\le j\le L^B\). Without even truncating these intervals at \(Y_B\), the prime number theorem with \(\pi(t)=\operatorname{li}(t)+O_K(t/(\log t)^K)\) for every fixed \(K>0\) gives each interval \(O(\tau N/(j^2L))\) primes. In fact both endpoint logarithms are \(L+O(\ell)\); the main-term bound is length divided by \(\asymp L\), and the endpoint errors \(O_K(N/(jL^K))\) are absorbed on taking \(K>B+u+2\). The total reciprocal weight of these primes is then
\[
O\left(\frac{\tau}{L}\sum_{1\le j\le L^B}\frac1j\right)=O(\tau\ell/L)=o(w).
\]

It follows from (1) that \(A'=A\cap\{p\text{ prime}:N^\theta<p\le Y_B\}\) has weight \(m=\log 2+o(w)\). Of all submeasures of the ambient weighted prime measure on \((N^\theta,Y_B]\) with mass \(m\), the rightmost suffix (allowing fractional bottom weight) stochastically dominates all others. Indeed its weight to the right of any \(x\) is \(\min(m,\text{ambient weight to the right of }x)\), the largest possible. For the kernel \(\mathbf 1_{pq\le N/L^\eta}\) with fixed \(0<\eta<B\), it therefore **minimizes** the ordered product weight. To verify the direction, fix \(q\); the kernel tests the mass of \(p\) in a lower interval, and replacing the \(p\) measure by the rightmost suffix cannot increase this mass. Then fix \(p\) and do the same for \(q\).

As \(\theta>1/3\), no three distinct primes from \(A'\) have a common multiple \(\le N\). Its redundancy equals the sum of the unordered pair intersection probabilities, and is at most the redundancy of \(A\). Restrict to \(pq\le N/L^\eta\), on which \(\lfloor N/(pq)\rfloor/N\ge (1-L^{-\eta})/(pq)\). Subtracting the diagonal weight \(O(N^{-\theta})\) from the ordered sum and dividing by two, (5) and the comparison show
\[
\liminf_{N\to\infty}\frac{\delta}{w^2}\ \ge\ (B-\eta)^2.
\]
We may take \(B\) arbitrarily close to \(1\) and \(\eta\) arbitrarily close to \(0\) through fixed choices. This proves the endpoint constant.

## 6. Why the full prime suffix loses at finite size

For any fixed \(0<\alpha<1\), the primes in \((\alpha N,N]\) consume \(o(1)\) total weight, and so all are present in the longest prime suffix up to \(N\) under any fixed budget \(C>0\) for large \(N\). The rounding component of (1) alone then gives
\[
\liminf_{N\to\infty}(\log N)\,\delta_{\rm suffix}
\ \ge\ \int_\alpha^1\{1/t\}\,dt.
\]
This follows by prime number theorem Riemann sums on \([\alpha,1]\); the integrand has only finitely many jumps there. Letting \(\alpha\downarrow0\), the integral is \(1-\gamma>0\): substitute \(u=1/t\) and integrate \((u-j)/u^2\) on \([j,j+1]\), then telescope the resulting harmonic sum. In all three items of the theorem the optimal deficit is \(o(1/\log N)\), yielding strict suboptimality.

## Sources and finite checks

Erdős and Ruzsa's [original small-sieve paper](https://www.renyi.hu/~p_erdos/1980-29.pdf) posed the asymptotic prime-suffix comparison. The small-budget first-order result appears in [Chojecki's Theorem 1.1](https://www.ulam.ai/research/erdos783-final.pdf); [Tao's theorem](https://terrytao.wordpress.com/wp-content/uploads/2026/02/erdos783-2.pdf) gives the Dickman limit for all \(C\). These are first-order statements, compatible with strict finite-size suboptimality of a prime suffix ending at \(N\). [Chojecki's subsequent note](https://www.ulam.ai/research/erdos783-rem.pdf) studies a different, first-order rigidity question. For the effective prime number theorem used in Section 5, a stronger underlying estimate is given by [Johnston and Yang, Theorem 1.4, equation (1.8)](https://arxiv.org/abs/2204.01980); partial summation suffices here. The quantitative additions of this note are the subcritical exponent, the reciprocal-budget uniqueness and the critical asymptotic, proved above without taking any finite experiment as evidence for an asymptotic step.

The companion [exact checker](verify_erdos783_budget_gap.js) tests the deficit identity, factorial-moment formula, reciprocal-budget grid, truncated overlap comparisons, fractional-part intervals, suffix ordering and the elementary triangle normalization on finite examples.
