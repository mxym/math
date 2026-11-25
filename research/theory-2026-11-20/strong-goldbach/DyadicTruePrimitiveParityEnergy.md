# True primitive parity energies and the dyadic Goldbach target

A pointwise arithmetic check for \(P=2^k\), \(k\ge3\), using actual prime weights. It does not give an order-\(P\) signed lower bound or a Goldbach pair.

Let \(H=P/2\) and \(f(n)=(\log n)1_{\{n\ {\rm odd\ prime},\ 1\le n<P\}}\). Set
\[
 R(M)=\sum_{x+y=M} f(x)f(y),\qquad
 E_P^\pm=\frac1{\varphi(P)}
      \sum_{\substack{\operatorname{cond}(\chi)=P\\\chi(-1)=\pm1}}
        \left|\sum_n f(n)\chi(n)\right|^2.
\]
Exact character orthogonality and subtraction of the characters factoring through \(H\) give
\[
 E_P^++E_P^-=\tfrac12\sum_n f(n)^2-\sum_{n<H}f(n)f(n+H),\qquad
 E_P^+-E_P^-=\tfrac12\big(R(P)-R(H)-R(3H)\big).
 \tag{1}
\]
Indeed all characters modulo \(P\) give the congruences \(x=y\bmod P\) and \(x+y=0\bmod P\), respectively. The induced characters are precisely the lifts of all characters modulo \(H\), with relative normalization \(\varphi(H)/\varphi(P)=1/2\); their unsigned condition groups each sibling pair \(f(n),f(n+H)\), and their signed condition lifts the three actual sums \(H,P,3H\). Thus no shifted prime sum has been replaced by an average.

The two-prime upper sieve, as in the [uniform central bound](CentralSpectrumQuantization.md), gives \(R(H),R(P),R(3H)\ll P\) and \(\sum_{n<H}f(n)f(n+H)\ll P\), using its identical two-root argument for differences. The only possible odd prime divisor of those nonzero shifts is \(3\), so the sieve singular factors are bounded. Endpoints and small prime inputs can be discarded at a power-saving cost (take the fixed-power cutoff in the cited proof). PNT with its classical log-power error gives \(\sum f^2=P\log P+O(P)\). In particular
\[
 E_P^\pm=\tfrac14P\log P+O(P).
\]
The Goldbach term in (1) lives at the strictly smaller order-\(P\) scale of their difference; a leading-order energy law for each side alone is insufficient.

## Local windows and exact removal of aliases

More generally, for a power of two \(q\mid P\), \(q\ge4\), write \(D_f(q)\) for the normalized signed energy over all characters factoring through \(q\). If \(f\) is supported in a central interval whose distance from \(P/2\) is everywhere \(<q/4\), then the only supported sum divisible by \(q/2\) is \(P\). Orthogonality now gives
\[
 D_f(q)=\frac qP R(P),\qquad
 D_f(q)-D_f(q/2)=\frac{q}{2P}R(P).
\]
These equalities hold also for log-prime weights multiplied by a fixed bounded window. If the support width \(W\) is polynomial in \(P\), the localized two-root upper sieve gives \(R(P)\ll W\), with a constant depending on the fixed lower exponent for \(W\): choose the sieve level a sufficiently small positive power of \(W\) to bound the remainder, so \(\log W\asymp\log P\). The alias-free signed shell then has size at most \(O(qW/P)\), which is \(o(P)\) for \(q=o(P)\). For \(q\asymp P\), an order-\(P\) lower for this shell would already be an order-\(P\) local Goldbach lower. Moving the window to isolate a different actual sum changes the arithmetic target; a positive shell in such a window does not transfer to the coefficient at \(P\).
