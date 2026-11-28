# A sharp random Lonely Runner threshold across densities

Let $S=S_{N,m}$ be a uniform $m$-element subset of $\{1,\ldots,N\}$, and set
\[
 L(S)=\max_{t\in\mathbb R/\mathbb Z}\min_{v\in S}\|vt\|,
 \qquad \lambda_N=-\log(1-m/N).
\]
Here $\|x\|$ is distance to the nearest integer and logarithms are natural.

**Theorem.** Suppose $m/(\log N)^2\to\infty$, $m\le(1-\epsilon)N$ for some fixed $\epsilon>0$, and $\log m/\log N\to\theta\in[0,1]$. Then
\[
 \frac{N\lambda_N L(S)}{\log N}
 \xrightarrow{\ \mathrm{probability}\ }
 \max\left\{\frac{1+\theta}{2},\frac{4\theta}{3}\right\}.
\tag{1}
\]
The two terms meet at $\theta=3/5$. In particular when $m/N\to0$ one may replace $N\lambda_N$ by $m$. If $\theta=1$ the conclusion includes the [previous constant-density theorem](DenseRandomLonelyRunner.md); if $\theta=0$ and the stated growth assumption holds, it yields constant $1/2$.

This is the fixed-size random model, not the deterministic Lonely Runner Conjecture. [Czerwiński](https://arxiv.org/abs/1102.4464) treats a fixed number of sampled speeds as the ambient bound grows. [Beck–Everett, Corollary 6 and proof of Theorem 7](https://arxiv.org/abs/2609.06259v3) treat fixed dimension and a growing-dimension construction on an exponentially large speed range. The sampling regime and small-gap scaling in (1) differ.

## 1. Sampling and a weighted second moment

For a fixed $c>0$, put $\delta=c\log N/(N\lambda_N)$, so $\delta\asymp(\log N)/m=o(1)$. A forbidden set is
$B(t)=\{1\le v\le N:\|vt\|<\delta\}$. A successful time with gap at least $\delta$ is exactly one whose forbidden set misses $S$.

Write $w=1-m/N=e^{-\lambda_N}$. A fixed set of size $b$ is avoided with probability zero if $b>N-m$; otherwise
\[
 P(b)=\frac{\binom{N-b}{m}}{\binom Nm}
   =w^b\prod_{j=0}^{b-1}
      \left(1-\frac{m j}{(N-m)(N-j)}\right)\le w^b .
\]
For $b=O(N\delta)$ this is $w^b(1+o(1))$ uniformly: the sum of the corrections is
$O(mb^2/N^2)=O((\log N)^2/m)=o(1)$ and $w\ge\epsilon$.

For a list $\mathcal T$ of tests with forbidden sets $B_t$ of size $O(N\delta)$, define
$X=\sum_{t\in\mathcal T}\boldsymbol1_{S\cap B_t=\varnothing}/P(|B_t|)$. Then $\mathbb E X=|\mathcal T|$ and the normalized two-test expectation is
\[
 \frac{P(|B_t\cup B_{t'}|)}{P(|B_t|)P(|B_{t'}|)}
   =(1+o(1))e^{\lambda_N |B_t\cap B_{t'}|}.
\tag{2}
\]
The error is uniform for all tests, including repeated or diagonal ones. Thus it suffices in each construction to show that the average of the last exponential over all ordered pairs tends to 1. The variance inequality then gives $\Pr(X=0)=o(1)$.

## 2. First lower bound: prime residue triples

For $\theta>0$ and $c<4\theta/3$, choose $0<\eta<1$ so that
$3c/(2-\eta)<2\theta$. Take primes $p\in((2-\eta)/\delta,2/\delta)$ and tests $a/p$ where $a j\equiv1\bmod p$ and $j$ ranges over one representative of each nonzero sign pair. The forbidden set consists exactly of the residue classes $0,\pm j\bmod p$, as $1<\delta p<2$. There are $N^{\theta+o(1)}$ such primes and $N^{2\theta+o(1)}$ tests by the prime number theorem; every $p\asymp m/\log N$.

The diagonal exponent in (2) is at most
$3\lambda_N(N/p+1)\le (3c/(2-\eta))\log N+O(1)$, negligible against the number of tests. Distinct sign pairs at one prime intersect only in the multiples of $p$; their fraction of ordered pairs is $N^{-\theta+o(1)}$ and their exponent is at most $(c/(2-\eta))\log N$.

For distinct primes $p,q$, the Chinese remainder theorem gives
$I=|B_t\cap B_{t'}|\le9(1+N/(pq))$. Over uniform sign pairs for those primes, $\mathbb E I=O(N/(pq))$. Indeed speeds divisible by both contribute at most $N/(pq)$, those divisible by just one are selected by the other with probability $2/(q-1)$ or $2/(p-1)$, and the rest are selected with probability $4/[(p-1)(q-1)]$. Also $\lambda_N N/(pq)=O((\log N)^2/m)=o(1)$, so $\lambda_N I$ is uniformly bounded. On a bounded interval $e^x-1=O(x)$, and hence the average excess in (2) is $O(\lambda_N N/(pq))=o(1)$. This reasoning includes $pq\le N$; no separated-CRT assumption on the density is required. This proves the $4\theta/3$ lower threshold.

## 3. Second lower bound: a large denominator and short lattice normals

Suppose now $\theta<1$ and $c<(1+\theta)/2$. Pick a prime $p$ in $[N/\delta,2N/\delta]$ (the prime number theorem suffices). It has size $N^{1+\theta+o(1)}$. For $a\in\mathbb F_p^\times$ define the planar lattice
\[
 \Lambda_a=\{(v,x)\in\mathbb Z^2:x\equiv a v\bmod p\},
 \quad\det\Lambda_a=p .
\]
Call $a$ good if this lattice has no nonzero vector shorter than $H=\sqrt p/\log N$ in Euclidean norm. At most $O(H^2)=o(p)$ numerators are not good: any such vector has $v\not\equiv0\bmod p$, since its coordinates are smaller than $p$, and determines $a$ uniquely. Use all good times $a/p$ as tests.

For a good $a$, a shortest nonzero lattice vector has length between $H$ and $O(\sqrt p)$ (the latter by the pigeonhole principle on an integer square of side $O(\sqrt p)$). This vector is primitive in $\Lambda_a$ and can be extended to a lattice basis. Subtract a nearest multiple of the short vector from the second basis vector. Its perpendicular component has length $p$ divided by the short length, and its parallel component has length at most half the short length. Consequently $\Lambda_a$ has a fundamental parallelogram of diameter $O(\sqrt p\log N)=o(N)$, since $\theta<1$ and $p\asymp N/\delta$. The forbidden set corresponds bijectively to points of $\Lambda_a$ with $1\le v\le N$ and $|x|<\delta p$. The parallelogram area bound, by enlarging the rectangle by its diameter in both directions, gives
\[
             |B(a/p)|\le (2+o(1))N\delta
\tag{3}
\]
uniformly over good $a$, since $\delta p\asymp N$.

For two good numerators $a,b$, a common forbidden speed corresponds bijectively to a point in
\[
 \Lambda_{a,b}=\{(v,x,y)\in\mathbb Z^3:
                   x\equiv av,\ y\equiv bv\bmod p\}
\]
in the box $1\le v\le N,\ |x|,|y|<\delta p$. This lattice has determinant $p^2$. To bound their number $I$, consider the rank of the span of the lattice points in the larger symmetric box $|v|\le N,\ |x|,|y|\le\delta p$. All its nonzero points have $v\not\equiv0\bmod p$ because every coordinate bound is smaller than $p$.

For use in ranks two and three, if a lattice of rank $j$ in a $j$-dimensional subspace has $j$ independent vectors in a ball of radius $O(N)$, then its point count in that ball is $O(N^j/\det\Lambda)$. Indeed those vectors generate a sublattice with a fundamental parallelepiped of diameter $O(N)$. In each sublattice coset, disjoint translates of the parallelepiped centered at the points are contained in a larger ball of radius $O(N)$. Bound the number per coset by that volume divided by the sublattice determinant, and multiply by the lattice index.

* At rank 0 there is nothing to count. At rank 1, the direction has nonzero projection onto the first two coordinates, so a primitive lattice vector along it has length at least $H$ by goodness of $a$. The count is $O(1+N/H)$. Thus $\lambda_N I=O(\lambda_N+\sqrt{m/N}(\log N)^{3/2})=o(1)$.
* At rank 3, the preceding full-rank bound gives $I=O(N^3/p^2)$, hence $\lambda_N I=O((\log N)^2/m)=o(1)$.
* At rank 2, let $n=(n_0,n_1,n_2)$ be a primitive integer normal of the spanned plane $\Pi$. A nonzero box point reduces to a nonzero multiple of $(1,a,b)$, so $n_0+n_1a+n_2b\equiv0\bmod p$. The lattice $\mathbb Z^3\cap\Pi$ has planar determinant $\|n\|_2$: extend its basis by an integer vector having dot product 1 with $n$, which gives a unimodular basis of $\mathbb Z^3$. Its reduction modulo $p$ spans the whole two-dimensional kernel of $n$, and the additional restriction to the line spanned by $(1,a,b)$ has index $p$. Hence $\Lambda_{a,b}\cap\Pi$ has determinant $p\|n\|_2$. Its count bound is $O(N^2/(p\|n\|_2))$. If $\|n\|_2>(\log N)^2$, then $\lambda_N I=O(1/\log N)=o(1)$.

For fixed good $a$, only $O((\log N)^6)$ values of $b$ can fall in the remaining rank-two case with a short normal. Each such normal has $n_2\ne0$: otherwise $n_0+n_1a\equiv0\bmod p$ would either make the entire short normal zero, or give the nonzero vector $(n_1,-n_0)$ shorter than $H$ in $\Lambda_a$. Since also $|n_2|<p$, such a normal determines at most one $b$. There are only $O((\log N)^6)$ integer triples of the indicated size. Therefore the exceptional fraction of pairs is $N^{-(1+\theta)+o(1)}$. By (3), even for these pairs
$e^{\lambda_N I}\le N^{2c+o(1)}$. Their contribution to (2) tends to zero by the strict choice of $c$. On all other pairs the factor is uniformly $1+o(1)$. This proves the $(1+\theta)/2$ lower threshold for $\theta<1$, and at $\theta=1$ the prime-triple bound already dominates it.

## 4. The upper bound: two sizes of grid entropy

Let $c>\max\{(1+\theta)/2,4\theta/3\}$. Choose a fixed $0<\gamma<1$ small enough that $c'=(1-\gamma)c$ still exceeds both thresholds, and put $\delta'=(1-\gamma)\delta$. Take a uniform circular grid of size
$T=\lceil N/(\gamma\delta)\rceil=N^{1+\theta+o(1)}$. If any real time reaches gap at least $\delta$, the nearest grid point reaches gap at least $\delta'$: each individual distance changes by at most $N$ times the circular distance between the times.

At every grid point $t$, write $t=a/q+\xi$ by Dirichlet approximation with
\[
 Q=\left\lfloor\frac{N}{\sqrt{\log N}}\right\rfloor,\quad
 1\le q\le Q,\quad(a,q)=1,\quad |\xi|\le\frac1{qQ}.
\]
Reduction of the fraction, if necessary, keeps this inequality valid. Put $D=q\delta'$ and $b=Nq|\xi|$. If $D,b\le1$, the forbidden set at threshold $\delta'$ contains the first $J=\lceil N\delta'\rceil-1$ positive multiples of $q$: $jq\le N$ and $|jq t-ja|\le j/N<\delta'$ for $j\le J$. There are at most $1/\delta'=N^{\theta+o(1)}$ possible denominators in this case, irrespective of the grid. The probability of avoiding any such set of multiples is at most $N^{\theta-c'+o(1)}=o(1)$.

In the other cases, define
\[
 G(D,b)=\int_0^1\#\{j\in\mathbb Z:|j+bu|<D\}\,du .
\]
In the forbidden count, each signed integer layer $j$ encodes one residue class of $v$ modulo $q$, namely $av$ or $-av$ according to the sign of $\xi$. Its allowable $v/N$ lie in the interval $|j+bu|<D$. The count in that arithmetic progression differs by at most 2 from its interval length times $N/q$; strict endpoints and the omission of $v=0$ cause no problem. There is no double count across layers because $2D<q$. Only $O(D+b+1)$ layers can be nonempty, so
\[
 |B_{\delta'}(t)|=\frac Nq G(D,b)+O(D+b+1).
\tag{4}
\]
Here $D\le N\delta'/\sqrt{\log N}$ and $b=O(\sqrt{\log N})$, so the error in (4) is $o(N\delta')$ uniformly.

The scalar bound $G(D,b)\ge3D/2$ when $D>1$ or $b>1$ is the [residue-average lemma of the fixed-density theorem](https://github.com/mxym/math/blob/e29bf659a0320183532df34ed75c6dda2e91b8f1/research/euclidean-tensor-geometry/theoretical-cryptography/DenseRandomLonelyRunner.md#3-an-elementary-residue-average). The same elementary count gives $G(D,b)\ge2D-1$ whenever $D\ge2$, by the minimum number of integers in any open interval of length $2D$. Fix $K>2$ sufficiently large that $(2-1/K)c'>1+\theta$.

If $D\le K$ in (4), then $q\le K/\delta'$. Grid points with such a Dirichlet approximant lie in the union of circular intervals centered at $a/q$, of radius $1/(qQ)$. Each contains at most $1+2T/(qQ)$ grid points. Counting at most $q$ centers for each $q$, the total is
\[
 O\left(\delta'^{-2}+\frac{T}{Q\delta'}\right)
       =N^{2\theta+o(1)}.
\]
Outside the exceptional-multiples case already handled, (4) gives a forbidden set of size at least $(3/2-o(1))N\delta'$. Its avoidance probability is at most $N^{-3c'/2+o(1)}$. Summing across these grid points tends to zero since $c'>4\theta/3$.

If $D>K$, (4) gives a forbidden set of size at least $(2-1/K-o(1))N\delta'$. All $T=N^{1+\theta+o(1)}$ grid points may now be counted. Their success probability tends to zero by the choice of $K$. This completes the upper bound, and combining it with the two lower constructions proves (1).

## 5. Exact finite controls

Run `python3 -O verify_varying_density_lonely_runner.py` for rational controls on the fixed-cardinality avoidance factorization; CRT intersections including the nonseparated case; counting small-denominator grid arcs; and the lift from pair overlap to a primitive integer normal determining the other numerator. These are finite checks of the ingredients, not a substitute for the lattice and asymptotic arguments.
