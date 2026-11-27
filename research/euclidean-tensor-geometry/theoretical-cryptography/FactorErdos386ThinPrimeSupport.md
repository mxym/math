# Consecutive-prime products in fixed rows of binomial order (Erdős #386)

Fix an integer $k\ge2$. Suppose $\binom nk$ is the product of a nonempty block of consecutive primes, with smallest prime $Q$ and largest prime $P$. Write $L=\log n$. We prove the following restrictions, unconditional for each fixed $k$:
$$
P-Q\gg_k \frac{P\log P}{L}\quad\text{if }P\text{ is sufficiently large},\qquad
P\ll_k \left(\frac{L}{\log L}\right)^{40/19}.
\tag{1}
$$
We also obtain a polylogarithmic bound on the number of such $n$:
$$
\bigl|\{2k\le n\le X:\tbinom nk\text{ is a consecutive-prime product}\}\bigr|
 \ll_k \left(\frac{\log X}{\log\log X}\right)^3.
\tag{2}
$$
In a dyadic interval $[X,2X]$ the bound is $O_k((\log X/\log\log X)^2)$. Unlike earlier restrictions based on a prime-free interval immediately before $n$, these bounds use the structure of the whole prime-support band near $P$. They do not prove finiteness even for $k=2$, and the constants in (1)–(2) are not uniform in $k$.

## 1. An elementary necessary width of the prime band

Let $s_i$ be the part of $n-i$ supported on primes at most $k$, for $0\le i<k$. Since any solution is squarefree after division by $k!$, for each prime $\ell\le k$ one has
$$
v_\ell\left(\prod_{i=0}^{k-1}(n-i)\right)
\le v_\ell(k!)+1.
$$
In particular every $s_i$ divides the fixed integer $K=k!\prod_{\ell\le k}\ell$. The two adjacent values $s_0,s_1$ are distinct by parity. All prime factors above $k$ belong to $[Q,P]$, since they are not canceled by $k!$.

Write $\Delta=P-Q$. If $Q\le P/2$, the asserted width is immediate because $\log P\le L$. Otherwise, for $P>2k$ the primes above $k$ lie in $[Q,P]\subset[P/2,P]$. Write
$$
\log(n-i)=\log s_i + r_i\log P+e_i,\qquad
-r_i\log(P/Q)\le e_i\le0,\qquad r_i\le L/\log Q,
\tag{3}
$$
where $r_i$ counts the prime factors above $k$, with multiplicity. In particular
$$
\left|\log(s_0/s_1)+(r_0-r_1)\log P\right|\ge \log(1+1/K)
$$
for $P$ sufficiently large in terms of $k$: if $r_0=r_1$, use the separation of distinct positive integers at most $K$, and if $r_0\ne r_1$, use the bound $\log P-\log K$. On the other hand, (3), $\log(n/(n-1))=O(1/n)$ and $\log(P/Q)\le2\Delta/P$ bound the same expression by
$$
O(1/n)+O\!\left(\frac{L\,\Delta}{P\log P}\right).
$$
This proves the width assertion.

## 2. A uniform upper bound for the greatest prime

If $P$ is larger than a suitable constant times $kL$, then $Q>P/2$. Indeed, if $Q\le P/2$ the consecutiveness gives $\log\binom nk\ge \sum_{P/2<p\le P}\log p=(1/2+o(1))P$, whereas $\log\binom nk\le kL$.

Set $\theta=21/40$. The quantitative lower estimate on the last page of [Baker–Harman–Pintz, *The difference between consecutive primes, II*](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf) gives $\gg v^\theta/\log v$ primes in $(v,v+v^\theta]$ for every large $v$. If $Q>P/2$ and $\Delta\ge4P^\theta$, apply it to disjoint subintervals in $[Q,P]$, taking a forward interval of length $v^\theta$ from the start $v$ of each full piece of length $2P^\theta$. It follows that $\sum_{Q\le p\le P}\log p\gg \Delta$. Thus in all cases with $Q>P/2$,
$$
\Delta\ll kL+P^\theta.
$$
Combining the two bounds for $\Delta$ gives $P\log P\ll_k L^2$ or $P^{1-\theta}\log P\ll_k L$. The first implies $P\ll_k L^2/\log L$, and the second gives the exponent $1/(1-\theta)=40/19$ in (1). The previously excluded range $P=O_k(L)$ is smaller than both bounds.

## 3. From short-interval exceptions to a count of endpoints

We next show that with $L=\log X$ the possible upper primes $P$ for $n\le X$ and $P\ge C_k L^2/\log L$ number at most
$$
O_k\big((L/\log L)^{168/95}\big).
\tag{4}
$$
The constant $C_k$ may be taken sufficiently large. Work first on a dyadic $P$-block $[Y,2Y]$ above this threshold. By (1), each solution's support contains the interval $[P-W,P]$, with fixed common length
$$
W=c_k Y\log Y/L
$$
for a sufficiently small $c_k>0$. Here $W=o(Y)$, $W\ge C'_k L$ with $C'_k$ sufficiently large, and $W/Y^\vartheta\to\infty$ uniformly, for $\vartheta=49/100$. For the last assertion use $Y\gg_k L^2/\log L$ and $2(1-\vartheta)>1$. The total logarithmic prime weight in this support interval is at most $kL$.

We use a specific consequence of [Gafni–Tao, *On the number of exceptional intervals to the prime number theorem in short intervals*, Theorem 1.2 and Table 1](https://arxiv.org/html/2505.24017#S1). Outside a set of real starts of measure $O(Y^{21/25})$ in $[Y/2,2Y]$, the interval $(x,x+x^\vartheta]$ has $\gg Y^\vartheta$ logarithmic prime weight. Indeed their zero-density exponents $A(\sigma)$ satisfy $A(\sigma)\le 30/13$ for $1/2\le\sigma<1$ and $A(\sigma)\le15/8$ for $\sigma\ge4/5$ from Table 1. In the supremum of Theorem 1.2, the latter range is excluded since $15/8<1/(1-\vartheta)=100/51$. On $1/2\le\sigma\le 4/5$ the theorem's expression is bounded by
$$
1-\big(2-(1-\vartheta)\,30/13\big)(1-\sigma)\le543/650<21/25.
$$
On $\sigma\le 1/2$ it is at most $1-\vartheta$ by the zero-counting bound. Apply the resulting estimate with fixed relative deviation, say $1/2$. To pass from von Mangoldt weight to prime weight, all the prime powers with exponent at least two inside a given interval contribute at most $O((\log Y)^2)=o(Y^\vartheta)$, because the length is below $\sqrt{x}$ and hence there are at most two $j$th powers for each $j\ge2$.

For each possible prime $P$ in the dyad, consider starts $x\in[P-W,P-2Y^\vartheta]$, for which $(x,x+x^\vartheta]\subseteq[P-W,P]$. By integrating the logarithmic prime weight of these short intervals over $x$, one obtains at most $(2Y)^\vartheta kL$: each fixed prime in the support is counted for a set of $x$ of length at most $(2Y)^\vartheta$. Thus the nonexceptional starts in this interval have measure $O(kL)$, so at least a fixed fraction of $W$ lies in the exceptional set once $C'_k$ is large enough. At any given $x$, at most $W+O(1)$ different integer upper endpoints $P$ can contribute. Integrating gives $O(Y^{21/25})$ possible upper primes in the dyad. Sum the geometric series up to the bound in (1). This proves (4) because $(40/19)(21/25)=168/95$.

For each pair $(Q,P)$, the value of the consecutive-prime product is fixed, so there is at most one solution $n$ for the chosen $k$, by strict monotonicity of $\binom nk$. If $P\le C kL$, the number of pairs is at most $\pi(CkL)^2=O_k((L/\log L)^2)$. If $P>C kL$ with $C$ large, then $Q>P/2$ and at most $O_k(L/\log L)$ different $Q$ are possible for a given $P$, because every additional prime costs at least $\log(P/2)$ in the log of the product. Below $C_kL^2/\log L$ there are $O_k((L/\log L)^2)$ primes $P$ by the ordinary PNT, and above that cutoff (4) is smaller. This proves (2). On $n\in[X,2X]$ the log of the binomial coefficient varies by $O_k(1)$; for each $P$ adding or dropping one prime changes that log by at least $\log 2$. Thus only $O_k(1)$ choices of $Q$ per $P$ remain in a dyadic $n$-interval, proving the local bound.

## Prior work and scope

- [Erdős and Graham, *Old and new problems and results in combinatorial number theory*, p. 74](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf) pose the original question. [Granville–Ramaré, *Explicit bounds on exponential sums and the scarcity of squarefree binomial coefficients*, Theorem 2](https://doi.org/10.1112/S0025579300011608) restricts large solutions to $k=n^{o(1)}$ after symmetry; it does not state a fixed-$k$ endpoint/count bound of the type above.
- [A prior #386 working report](https://www.erdosproblemaday.com/report/386) and [the SciNet structure and scan note](https://api.scinet.pub/f/12ada956-8b18-4f35-96f8-c3117fee93b5) give prime-gap reductions near $n$ and finite searches. The width mechanism in (3) compares the distinct bounded small-prime parts of adjacent terms; the subsequent counting is over prime-band endpoints, not over the prime gaps near $n$.
- The [fixed finite verifier](verify_factor_erdos386_thin_prime_support.js) audits the small-part and width identities, independently checks the previously known toy solutions, and checks the rational exponent comparison. It passes 109,730 assertions including 49 narrow-band trials. These are not tests of the asymptotic theorem.
