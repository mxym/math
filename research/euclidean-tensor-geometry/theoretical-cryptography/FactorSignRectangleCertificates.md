# A lower bound for sign-only rectangle certificates of semiprime products

A certificate based only on multiplication ranges has a basic limitation: excluding all wrong pairs can require exponentially many regions even if the correct pair is given. We prove this for true prime candidates and a uniformly chosen balanced semiprime, not just for an integer grid or a continuous product threshold. The result is about an explicit certificate format and does not bound ordinary factor verification, SAT proof systems, or the complexity of integer factorization.

## Model and theorem

Let $P\ge3$, let $\mathcal P$ be the primes in $[P,2P)$, and write $M=|\mathcal P|$. The candidate cells are all $(p,q)\in\mathcal P^2$ with $p<q$. A random target $N$ is uniform among the $\binom M2$ products of these cells. These products are distinct. The correct cell may be supplied to the certificate prover for free.

A certified **strictly lower rectangle** is $(A\times B)\cap\{p<q\}$ for some $A,B\subseteq\mathcal P$, such that every cell in it has product less than $N$. A **strictly upper rectangle** is defined by product greater than $N$. A sign-only certificate covers every wrong cell with these rectangles. It may overlap rectangles arbitrarily; the sets need not be intervals. Let $B_-(N)$ and $B_+(N)$ be the respective smallest cover sizes of the two strict sides. More generally $B_\pm(N;k)$ allows leaving up to $k$ cells uncovered on that side (e.g. to certify individually by some other rule).

**Theorem.** For each fixed integer $r\ge2$, all nonnegative integers $k,s$, and either sign,
$$
\Pr_N\{B_\pm(N;k)\le s\}
 \ll_r \frac{k+1}{M}+\left(\frac{s}{M}\right)^{1-1/r}.
\tag{1}
$$
The constants are uniform in $P,k,s$. In particular, for every fixed $\epsilon>0$ there is $c_\epsilon>0$ so that, with probability at least $1-\epsilon$ for all large $P$, each side requires at least $c_\epsilon M$ rectangles when $k=0$ or $k=o(M)$. Since $\smash{B_\pm(N)\le M}$ by using one row at a time, this is the correct order at fixed high quantiles. With $P=2^{n-1}$, $M\asymp2^n/n$.

The restriction to a single sign per rectangle is essential. A certificate that uses primality and uniqueness of prime factorization can certify the complete factorization without covering this grid, and (1) does not apply to such a proof.

## Product bands and incompatible cells

Set $H=\lceil\log P\rceil$ and divide $[P^2,4P^2)$ into bands of width $PH$, with the last possibly shorter. Let $J$ denote their number. Also divide the first coordinate's range into half-open row buckets of width $H$. Let $n_{j,b}$ be the number of cells in product band $j$ and row bucket $b$, and put
$$
S_{j,r}=\sum_b n_{j,b}^r.
$$

Fix $N$ in band $j$. Two cells of this band in distinct row buckets of the same parity have first coordinates $p_1<p_2$ with $p_2-p_1>H$. Necessarily $q_1>q_2$: if $q_2\ge q_1$, then $p_2q_2-p_1q_1>PH$, impossible in a single band. Thus $p_2<q_2<q_1$, so both crossed cells $(p_2,q_1)$ and $(p_1,q_2)$ are in the strict triangular promise.

If the original cells are both below $N$, their crossing $(p_2,q_1)$ is above $N$: its product exceeds $p_1q_1$ by $(p_2-p_1)q_1>PH>N-p_1q_1$. No certified lower rectangle contains both original cells. If both originals are above $N$, $(p_1,q_2)$ is below $N$ by the symmetric inequality with $p_2q_2$. The band hypothesis is essential here: it supplies both the numerical sign gap and the fact that the crossed cell is admissible under $p<q$.

Let $a$ be the number of products in band $j$ strictly below $N$ (for the upper version, strictly above $N$). If that side is covered by at most $s$ rectangles with at most $k$ omissions, its covered points in the band occupy at most $2s$ row buckets, since each rectangle can meet at most one even and one odd bucket. By Hölder,
$$
a\le k+(2s)^{1-1/r}S_{j,r}^{1/r},
\tag{2}
$$
interpreting the second term as zero if $s=0$. Because the products are distinct, the values of $a$ in a band are distinct consecutive integers as $N$ runs through that band. Hence the number of targets in band $j$ with $B_\pm(N;k)\le s$ is at most $k+1+(2s)^{1-1/r}S_{j,r}^{1/r}$. Summing gives the deterministic inequality
$$
\#\{N:B_\pm(N;k)\le s\}
 \le J(k+1)+(2sJ)^{1-1/r}\left(\sum_j S_{j,r}\right)^{1/r}.
\tag{3}
$$
The step to random balanced semiprimes will be an upper bound on this occupancy moment, not an assumption of uniform density inside each product band.

## Occupancy moments for the prime grid

For a real $U>0$ and integer $r\ge2$, let $C_r(U)$ count ordered $r$-tuples of primes from $\mathcal P$, with repetitions allowed, of diameter at most $U$. For fixed $r$ and $U=O(\log P)$ we have
$$
C_r(U)\ll_r M
\tag{4}
$$
when the implied constant in $U=O(\log P)$ is fixed.

Here are standard sieve details. For tuples with $t$ distinct primes, order those primes, fix the smallest, and consider the shift set $\{0,h_1,\ldots,h_{t-1}\}$ with $1\le h_1<\cdots<h_{t-1}\le U$. For fixed shifts, Selberg's prime-tuple upper bound is $O_t(P(\log P)^{-t}\mathfrak S(\{0,h_1,\ldots,h_{t-1}\}))$ for an admissible tuple. An inadmissible tuple gives no primes here for large $P$: its forbidden local prime is at most $t$, while all tested values are larger. The total singular series over such anchored shift sets is $O_t((1+U)^{t-1})$. To see this from Gallagher's standard mean bound, translate each set by $1,\ldots,\max(1,\lfloor U\rfloor)$. The translated sets are distinct because their smallest element determines the translation, they stay in an interval of length $O(1+U)$, and translation preserves the singular series. Divide the ordinary mean bound by the number of translations. Summing over $t\le r$ and the $O_r(1)$ ways of ordering and repeating the distinct primes gives $O_r(P/\log P)$, which equals $O_r(M)$ by the prime number theorem. Neither lower bounds for prime tuples nor Hardy–Littlewood are used.

Any ordered $r$-tuple of cells counted in $n_{j,b}^r$ has first-coordinate diameter at most $H$ and second-coordinate diameter at most $3H$. To see the latter, use for two cells in the tuple
$$
p\,|q-q'|\le |pq-p'q'|+q'|p-p'|
       \le PH+2PH.
$$
The two coordinate lists determine the cell tuple and each tuple belongs to a single band and bucket. Therefore
$$
\sum_j S_{j,r}\le C_r(H)C_r(3H)\ll_r M^2.
\tag{5}
$$
Since $J\ll P/H\ll M$, substituting (5) in (3) and dividing by $\binom M2$ proves (1) whenever $M\ge2$. The high-quantile statement follows by choosing $s/M$ sufficiently small in (1) and applying the union bound to the two signs.

## Scope, prior ingredients, and checks

- The crossed-cell argument is the standard incompatible-cell lower bound for monochromatic rectangle covers in communication complexity; see [Aho, Ullman and Yannakakis, *On notions of information transfer in VLSI circuits*](https://doi.org/10.1145/800061.808742) and [Sherstov's survey](https://web.cs.ucla.edu/~sherstov/pdf/mfcs-disjointness.pdf) for the rectangle convention. The additional conclusion here is the quantitative lower-tail estimate on the sparse sorted prime grid with the target drawn from those very products.
- The analytic input in (4) is classical: Selberg's prime tuple upper bound and Gallagher's mean singular series. Both are used with explicit fixed-dimension bounds in [Goldston, Pintz and Yıldırım, *Primes in tuples IV*](https://arxiv.org/abs/1103.5886), equations (1.16), (4.4). Uniformity at shifts $O(\log P)$ is enough.
- The companion [exact checks](verify_factor_sign_rectangles.js) test the crossed-cell argument on the triangular promise, the deterministic moment inequalities at multiple scales, and exact cover sizes on a fixed very small grid. The scripts take no external input and solve no factoring instance.
