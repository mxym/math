# Triangle slack forces hundreds of near contacts in a six-dimensional kissing code

**Theorem.** Among 76 kissing points in $\mathbb R^6$, at least **439** unordered pairs have inner product above $0.490$, at least **202** have product above $0.495$, and at least **two** have product above $0.4976$. The last two pairs are at angles in $[60^\circ,60.159^\circ)$; they need not be disjoint. No symmetry or specified subconfiguration is assumed. Here is the full family of certified implications.

| Number of points | Threshold $t$ | Unordered pairs with $x\cdot y>t$, at least |
|---:|---:|---:|
| 73 | .480 | 73 |
| 74 | .485 | 99 |
| 75 | .485 | 278 |
| 75 | .490 | 144 |
| 76 | .490 | **439** |
| 76 | .49125 | **401** |
| 76 | .495 | **202** |
| 76 | .497 | **49** |
| 76 | .4975 | **8** |
| 76 | .4976 | **2** |

In particular, $A(6,\arccos(0.4976))\le 75$: a code meeting that stronger separation cannot even contain a 76-point subset. This is not a determination of the kissing number or the optimum angle. In particular, none of 73–76 is excluded or constructed. The [earlier pair-only certificate](https://github.com/mxym/math/blob/f42999e4c7698d6e9b9487b71423ca7c6e37dc70/research/euclidean-tensor-geometry/KissingSixNearContactDistribution.md) gave 88 at $.490$ and two at $.49125$ for 76 points. The genuinely different input here is the **entire three-point slack polynomial** from [Tomar's six-dimensional four-point certificate](https://doi.org/10.5281/zenodo.24093810), coupled to positive kernels around each possible anchor. The general idea of recovering distribution bounds from multipoint certificates is due to [Musin](https://arxiv.org/html/2309.13854v4); the underlying hierarchy and symmetry reduction are those of [de Laat, Leijenhorst and de Muinck Keizer](https://arxiv.org/html/2404.18794v2#S4).

**Geometric consequences.** The graph with edges $x\cdot y>.490$ has maximum degree at most 25 by the earlier projection certificate. Hence the 439 edges contain a matching of at least 17 edges (Vizing), and some vertex has at least 12 such neighbors. The 202 edges above $.495$ contain a matching of at least 8. If 75 points do not contain 36 disjoint pairs of product **below** $-1/2$, the [unique-antipode extension theorem](https://github.com/mxym/math/blob/5c34aa6bc59244f3ed2a33ea1b224ae6d5b7b2a0/research/euclidean-tensor-geometry/KissingSixSeventyFiveExtension.md) applies. Adding one vertex and then deleting its incident near contacts gives lower bounds **414** above $.490$, **376** above $.49125$, **177** above $.495$ and **24** above $.497$ for the original 75 points. These conditional bounds are separate from the unconditional 75-point table.

## 1. What the four-point certificate supplies

Write $N=|C|$, $L=\binom N2$, $H=\binom N3$, $M=7699/100$. If $q_j$ is the sum of the $j$th powers over unordered distinct pairs, set $v=(1,N,q_0,\ldots,q_{10})$. Let $F$ be the positive semidefinite trivial block, $a_1$ the singleton slack, and $R_2$ the pair slack, using exactly the [previous normalization and source files](KissingSixNearContactDistribution.md). Write $R_3(u,v',w)$ for the slack on a three-element subset whose off-diagonal Gram entries are $u,v',w$. Summing the certificate's equality over unions of index subsets of a code gives
\[
 v^T Fv + Na_1 + \sum_{\{x,y\}}R_2(x\cdot y) + \sum_{\{x,y,z\}} R_3(u,v',w)\le M-N.\tag{1}
\]
Each triangle occurs **once**: the ordered pairs of index sets have already been grouped by their union. We discard the nonnegative four-distinct-point slack and the other nonnegative representation energies, not part of $R_3$.

### A compact but rigorously controlled triangle polynomial

There are 15 original SOS matrix blocks and 45 dense/transform/polynomial files at union size three. Each contribution is $\sum_s g_s h_s^T(T A T^T)h_s$, with its original rational transformation, prefactors and polynomial vectors. The [source audit](verify_kissing_six_triangle_source.py) works from the original rationals; no fit to sampled triangles is used. Replace each dense entry of $A$ by its lower multiple of $10^{-34}$, transform the polynomial vectors exactly, and expand with integer arithmetic.

For each prefactor let $w_i$ be the coordinate polynomials of $T^T h_s$, and let $\|p\|_c$ be the sum of the absolute monomial coefficients. The contribution to the uniform error on $[-1,1]^3$ is at most $10^{-34}\|g_s\|_c(\sum_i\|w_i\|_c)^2$. Sum these bounds. Average the approximate polynomial over the six permutations (the actual $R_3$ is symmetric by the union identity), then floor every monomial coefficient on a $10^{-26}$ grid. Counting all 1,771 monomials before permutation compression gives a combined error less than $2\cdot10^{-23}$. The [snapshot](kissing-six-coupled-triple-data.json) stores 352 symmetric coefficient representatives, representing a polynomial $\widehat R_3$ of total degree at most 20. We do **not** assume the approximation stays positive; the error is charged explicitly. All 45 raw member digests are pinned.

## 2. Positive kernels on the triangle distribution

Let $(u,v',w)$ be the three products of a uniformly random unordered distinct triangle. A cyclic average, denoted $\mathrm{av}$, averages the three choices of anchor. An edge of this triangle selected uniformly has the uniform unordered-pair law of the entire code. A witness consists of nonnegative rational multiples of three types of inequalities $\mathbb E A\le B$.

* **Pair harmonic.** For a dimension-six normalized Gegenbauer polynomial $P_j$, use $A=-(N-1)\,\mathrm{av}\,P_j(u)$ and $B=1$.
* **Anchored harmonic.** Let $p$ be any supplied rational combination of Chebyshev polynomials and $k\ge0$. Put $Q_0=1$, $Q_1=w-uv'$, and
  \[
  Q_{k+1}=\frac{(2k+3)(w-uv')Q_k-k(1-u^2)(1-v'^2)Q_{k-1}}{k+3}.
  \]
  Use $B=\mathbf1_{k=0}p(1)^2$ and take $A$ to be $-(N-1)$ times
  \[
  \mathrm{av}\big[(N-2)p(u)p(v')Q_k(u,v',w)
        +(1-u^2)^k p(u)^2 +2\mathbf1_{k=0}p(1)p(u)\big].
  \]
  To see this, keep one point fixed and apply zonal positivity to the unit-normalized projections of the other points to its five-dimensional orthogonal complement, with weights $p(u)(1-u^2)^{k/2}$. This gives $p(u)p(v')Q_k$. The polynomial extends to degenerate projections by continuity; for $k=0$ the factor is 1. Now sum over anchors, allowing both other indices to vary over the **whole** code. Three distinct indices give the first term, two equal non-anchor indices the second, one index equal to the anchor the third, and all three equal the stated $B$. Division by $N$ yields the displayed multiplicities.
* **Four-point tangent.** For rational $z\in\mathbb Q^{13}$ put $b=2Fz$. From (1) and $(v-z)^T F(v-z)\ge0$ take
  \[
  A=L\,\mathrm{av}\left[R_2(u)+\sum_{j=0}^{10}b_{j+2}u^j\right]+H R_3(u,v',w),
  \quad B=M-N-Na_1-b_0-Nb_1+\tfrac12 z^Tb.
  \]
  When using the rounded source entries, add to $B$ the [pair/trivial block error](KissingSixNearContactDistribution.md), with multiplier one, and $2H\cdot10^{-23}$ for the triangle approximation. Positivity is invoked on the original exact $F$, not its rounding.

## 3. Certifying the discontinuous pair count

Write $m$ for the number of the three products strictly larger than $t$, so the desired pair count equals $L\mathbb E[m]/3$. For the rational nonnegative multipliers $\lambda_i$ it suffices to verify on every possible triangle that
\[
 \frac{Lm}{3} + \sum_i\lambda_i(A_i-B_i) \ \ge\ K-1+1/100 .\tag{2}
\]
Taking expectation and using $\mathbb E[A_i-B_i]\le0$ proves that the integer pair count is at least $K$.

The [Python driver](verify_kissing_six_coupled_triples.py) constructs the polynomial in (2) over exact rationals. The [Bernstein checker](verify-kissing-coupled-bernstein.js) separately checks the four cases $m=0,1,2,3$. By symmetry, the first $3-m$ coordinates lie in $[-1,t]$ and the last $m$ lie in $[t,1/2]$. Each closure includes its boundary; for an actual coordinate equal to $t$, use the case that counts it as **low**. On each rational box retain the true Gram constraint $1+2uv'w-u^2-v'^2-w^2\ge0$. Initial tensor Bernstein coefficients are computed with exact integer transformations. Dyadic roundings are always outward (down for the target, up for the Gram polynomial); on a boundary cell the verifier may certify the target minus a nonnegative dyadic multiple of the Gram polynomial. The multiplier is accepted only after every coefficient passes a bounded-exact-integer test. Ordering exclusions are used only within equal coordinate intervals. Thus neither sampling nor an optimizer is a premise.

**Replay.** With Python 3.9+ and standard Node, run `python3 verify_kissing_six_coupled_triples.py` in this directory. Optional arguments such as `75` or `76:0.4976` select rows. To rebuild the 352 coefficients, run `python3 verify_kissing_six_triangle_source.py proof_6_76.tgz` (or give `download` to stream the [767 MB source archive](https://github.com/tejasvi/kissing-numbers-lasserre/releases/download/v3/proof_6_76.tgz)). For the four original one-/two-point matrices run the earlier checker with the same archive. These are exact derivative checks, not a replacement for the author's full four-point verification. The original certificate and its rounded adaptations are credited to [Tejasvi Singh Tomar, v3 supplement, CC BY 4.0](https://doi.org/10.5281/zenodo.24093810).
