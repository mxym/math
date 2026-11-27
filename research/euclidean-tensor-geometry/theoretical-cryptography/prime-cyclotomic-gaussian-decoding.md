# Gaussian decoding at a prime-cyclotomic Voronoi cell

This note quantifies the gap between testing only the first few Euclidean Voronoi halfspace layers and the full, optimal Gaussian Decoding Problem (GDP) success probability. On the scaled canonical integer ring of prime cyclotomic conductor, the first layer gives the critical-window limit. The contribution of the first omitted layer has an explicit asymptotic at *every fixed layer*. There is no deterministic implication from an incomplete layer test, even on these lattices.

This is a statement about the Gaussian measure of a single geometric cell, with no public samples, key, modulus, implementation, or solver. It does not improve the Ring-LWE hardness reduction.

## Geometry and statement

Use ambient coordinate count $n$, so that the real dimension is $n-1$. Set $H_n=\{y\in\mathbb R^n:\sum_i y_i=0\}$, let $P_n$ be orthogonal projection onto $H_n$, and put $\Lambda_n=P_n\mathbb Z^n=A_{n-1}^*$. For $1\le j<n$ set $d_j=(n-j)/(2n)$. The origin's Voronoi cell $V_n$ is given by

$$
\sum_{i\in S}y_i\le |S|d_{|S|}\quad
  (\varnothing\ne S\subsetneq[n]).
\tag{1}
$$

Since $P_n{\bf1}_{S^c}=-P_n{\bf1}_S$, this is equivalent to testing both signs up to size $\lfloor n/2\rfloor$. Let $E_\ell$ be the event that these signed tests hold for $1\le |S|\le\ell$. In particular $E_1$ tests precisely the shortest-vector halfspaces. All statements for a first omitted size $k$ fix $k$ and take $n\to\infty$.

For i.i.d. standard normals $X_i$, let $Y=P_nX/(2u_n)$, where $u_n>0$, and set $\mu_n=2n\overline\Phi(u_n)$, $w_n=u_n^2\mu_n/n$. Assume $u_n^2=O(\log n)$ and $\mu_n\to\mu$ with $0\le\mu<\infty$. Define the bounded region in $\mathbb R^k$

$$
B_k=\left\{z_i\ge0:\ \sum_{i\in S} z_i\ge\binom{|S|}{2}\ (\varnothing\ne S\subsetneq[k]),\
                      \sum_{i=1}^k z_i<\binom k2\right\}.
$$

Then

$$
\begin{aligned}
\Pr[Y\in V_n]&\longrightarrow e^{-\mu},\\
\Pr[E_{k-1},\ Y\notin V_n]
 &= (1+o(1))\, \frac{2\,\operatorname{vol}_k(B_k)}{k!}\,e^{-\mu}w_n^k
        &&(k\ge2\text{ fixed}),\\
1-\Pr[Y\in V_n]&\sim\mu_n &&(\mu=0).
\end{aligned}
\tag{2}
$$

The volume is positive: all coordinates equal to $(k-1)/2-\delta$ for $0<\delta<1/2$ give a strict interior point. The paired-shortest discrepancy has coefficient $2\operatorname{vol}(B_2)/2!=1/2$; the first omitted triple layer has coefficient $2\operatorname{vol}(B_3)/3!=7/12$. In particular, if $2n\overline\Phi(b_n)=1$ and $u_n=b_n+t/b_n$ for fixed real $t$, then $\mu=e^{-t}$ and the full success tends to $\exp(-e^{-t})$. This follows directly from the usual normal tail ratio; it does not require an independence assumption on the centered coordinates.

For prime $p$, write $R=\mathbb Z[\zeta_p]$. The full canonical real lattice of $R$ is isometric to $\sqrt p\,\Lambda_p$: the $p$ images of $\zeta_p^j$ span $R$ integrally, sum to zero, and have Gram matrix $pI-{\bf1}{\bf1}^{\mathsf T}$. Thus (2) holds for GDP on $R$ with canonical perturbation standard deviation $\sqrt p/(2u_p)$ in each orthonormal real coordinate, or Gaussian parameter $g=\sqrt{2\pi p}/(2u_p)$ in the convention with density proportional to $\exp(-\pi\|y\|^2/g^2)$. The geometric statement on $\Lambda_n$ does not require $n$ prime.

## Why this is an optimal GDP success probability

Given a coset $y+\Lambda$, the conditional weights of its possible representatives under spherical Gaussian noise are proportional to the Gaussian densities there. This follows by disintegrating over a fundamental domain and summing the densities of its translates; boundary representatives occur with probability zero. The optimal decision is a closest representative to zero, and its success probability is exactly the Gaussian measure of the origin's Voronoi cell. This optimality does not posit that such a decision is efficiently computable on arbitrary inputs.

For (1), take a nonzero lattice vector $P_nz$, $z\in\mathbb Z^n$. Subtract $\min_i z_i$ from $z$ and write it as a sum of indicators of nested nonempty proper sets. For $S\subset T$, the dot product of their projected indicators is $|S|(1-|T|/n)\ge0$. If (1) holds, adding the associated inequalities gives $2\langle y,P_nz\rangle\le\|P_nz\|^2$. Conversely, each projected indicator is itself a lattice vector, giving (1). A projected set of size $j$ has squared length $j(1-j/n)$, minimized precisely at $j=1,n-1$. A sum of at least two projected indicators in a nested chain has squared norm at least the sum of their squared lengths, proving the shortest-vector assertion. Neither a shortest-vector description of the whole cell nor a facet-classification theorem is assumed.

For every $k\ge2$ and $n\ge2k$, a point can pass the first $k-1$ layers and fail layer $k$. Take $k$ coordinates equal to $a=(d_{k-1}+d_k)/2$ and the rest equal to $-ka/(n-k)$. All coordinate magnitudes are at most $a<d_{k-1}$, so all smaller signed averages pass. The positive $k$-set has average $a>d_k$.

## Proof of the asymptotics

Write $\sigma=1/(2u_n)$. The normal tail estimates $\overline\Phi(u)\sim \phi(u)/u$ and $\Pr(|X_i|>u)=2\overline\Phi(u)$ yield $u_n\to\infty$, $u_n^2/2\ge \log n-\tfrac12\log\log n-O(1)$, $\phi(u_n)/\sigma\sim w_n$, and $w_n=O(\log n/n)$. Under the assumed upper bound on $u_n^2$, $w_n$ is also bounded below by some inverse power of $n$ for all large $n$.

**Singleton limit.** For the uncentered $\sigma X$, the event with all absolute coordinates below $d_1$ has probability tending to $e^{-\mu}$, because the normal threshold $2u_nd_1=u_n(1-1/n)$ differs from $u_n$ by $o(1/u_n)$. The same limit holds for $Y$: $\overline X=O_{\Pr}(n^{-1/2})$, so a sandwich between uncentered thresholds $u_n\pm n^{-1/4}$ (widened by the $O(u_n/n)$ deterministic shift if needed) has the same limit. Here and below any threshold change $o(1/u_n)$ preserves normal tail ratios by the tail estimates.

If $\mu=0$, a singleton fails with probability $2\overline\Phi(u_n\sqrt{1-1/n})\sim\mu_n/n$. The probability that two distinct coordinates both fail in absolute value is $O((\mu_n/n)^2)$: their joint centered-Gaussian density is at most $(1-2/n)^{-1/2}$ times the product of the two uncentered $N(0,\sigma^2)$ densities. Bonferroni yields $1-\Pr(E_1)\sim\mu_n$. The density domination just used, in any $j<n$ coordinates, follows from covariance $\sigma^2(I_j-{\bf1}{\bf1}^{\mathsf T}/n)$, determinant factor $1-j/n$, and precision $\sigma^{-2}(I_j+{\bf1}{\bf1}^{\mathsf T}/(n-j))$.

**Large omitted layers.** Put $J=\lceil\log n\rceil$. For either sign and a set of size $j$, the sum is normal with variance $\sigma^2 j(1-j/n)$. The union bound over $J\le j\le n/2$ is at most

$$
2\sum_{J\le j\le n/2}
 \exp\left(j\{\log(en/j)-(u_n^2/2)(1-j/n)\}\right).
$$

The expression in braces is at most $1-\log j+(j/n)\log n+\frac12\log\log n+O(1)$. The concave function $\log j-(j/n)\log n$ takes its minimum on $[J,n/2]$ at an endpoint; the minimum is $\log\log n+o(1)$. Hence the entire bound is $\exp(-\Omega(\log n\log\log n))=o(w_n^k)$ for each fixed $k$.

**Intermediate omitted layers.** On $E_1$, if a signed $j$-set fails (1), all its coordinate deficits $d_1\mp Y_i$ are nonnegative and their sum is $<j(j-1)/(2n)$. In particular, each participating signed coordinate lies within $j(j-1)/(2n)$ of $d_1$. For $j\le J$, throughout this interval the one-coordinate density of $N(0,\sigma^2)$ is at most $Cw_n$, since displacements $O(J^2/n)$ change its log density by $O(u_n^2 J^2/n)=o(1)$. Joint density domination above and $\binom nj\le(en/j)^j$ bound the probability of any such set of size $j$ by $C_1(C_2 j w_n)^j$, with fixed constants. Summing from $k+1$ to $J$ gives $O((C_2 Jw_n)^{k+1})=o(w_n^k)$. Thus only signed $k$-sets contribute to the leading discrepancy.

**One signed $k$-set.** Fix the positive sign by symmetry and label the tested coordinates $1,\ldots,k$. The local conditions for their proper subsets and failing the full $k$ test are exactly $z_i=n(d_1-Y_i)\in B_k$. The joint density of these $Y_i$ is $(1+o(1))w_n^k$ uniformly on this bounded, rescaled region: the determinant factor tends to 1 and the extra quadratic form in the joint precision contributes $O(u_n^2/n)=o(1)$. The same holds for negative sign by reflection.

Conditional on these coordinates, the remaining $Y$ have law

$$
\sigma P_{n-k} X'+m{\bf1},\qquad m=-\frac{\sum_{i=1}^kY_i}{n-k},
$$

with $X'$ a fresh vector of i.i.d. standard normals. To see this, the Gaussian residual after subtracting the mean in the remaining independent coordinates is independent of their mean and of the first $k$ unprojected coordinates; the conditional mean is then forced by the zero-sum constraint. Uniformly on $B_k$, $m=O(1/n)$. Requiring all remaining coordinates to have magnitude at most $d_1$, or at most $d_1-\binom{k}{2}/n$, has limit $e^{-\mu}$ by the same singleton sandwich with $n-k$ normals and normalized shifts $O(u_n/n)$. The first condition is necessary for $E_{k-1}$. The second is sufficient for all mixed or remaining signed tests of size up to $k-1$: every coordinate deficit is nonnegative for each sign, and each remaining coordinate supplies a deficit $\ge\binom{k}{2}/n$ by itself. Negative tests on the positive cluster hold for large $n$. Therefore the conditional probability of satisfying $E_{k-1}$ tends uniformly to $e^{-\mu}$. Integrating over the region gives $(1+o(1))w_n^k n^{-k}\operatorname{vol}_k(B_k)e^{-\mu}$ for one signed set.

**Two signed $k$-sets.** Distinct signed events with opposite signs cannot share an index, for their required sign-specific intervals near $\pm d_1$ are disjoint for large $n$. Distinct events with the same sign involve at least $k+1$ indices. The $r$-coordinate density and interval estimates just proved give a bound $O_k((w_n/n)^r)$ per pattern, $k+1\le r\le2k$. There are $O_k(n^r)$ patterns. Thus all pair intersections total $O_k(w_n^{k+1})$. Bonferroni over the $2\binom n k$ events, together with the bounds for higher layers, gives the second line of (2). Applying it at $k=2$ gives the first and third lines; in the third, $w_n^2=o(\mu_n)$.

For the stated triple coefficient, the three-dimensional simplex of nonnegative coordinates with sum $<3$ has volume $27/6$. Cutting out one violated pair-sum constraint (pair sum $<1$) removes $7/6$. The intersection of two such constraints has volume $1/3$; the intersection of all three has volume $1/4$. For the last number, at first coordinate $x\in[0,1]$, intersect the square $0\le y,z\le1-x$ with $y+z<1$; its area is $(1-x)^2-\tfrac12(1-2x)_+^2$. Inclusion-exclusion gives $7/4$.

## What changes, and what does not, for the reduction

At the critical window $u_n\asymp\sqrt{\log n}$ the noise norm is typically $\sqrt n/(2u_n)$, whereas the Euclidean inscribed ball only has radius $\lambda_1(\Lambda_n)/2=\tfrac12\sqrt{1-1/n}$. This separates a deterministic radius test from the Gaussian measure of the actual decision cell. In fact, on this family the failure probability is negligible in $n$ (smaller than every inverse polynomial) **if and only if** $u_n^2/\log n\to\infty$. If that ratio diverges, the signed-set Chernoff bound in (1) is at most $2\sum_{j\ge1}(ne^{-u_n^2/4})^j$, which is negligible. If it does not diverge, along a subsequence a single coordinate already fails with probability $2\overline\Phi(u_n\sqrt{1-1/n})$ bounded below by an inverse polynomial. Thus constant success at the critical scale must not be substituted for the negligible failure required by the quantum reduction. This is a geometric constraint on even an idealized optimal rule, not an argument about reduction algorithms beyond their published hypotheses.

[Lyubashevsky–Peikert–Regev, §4](https://cims.nyu.edu/~regev/papers/ideal-lwe.pdf) distinguish the Euclidean Gaussian perturbation used in the quantum step from the canonical embedding $\ell_\infty$ promise in the classical step. [Peikert–Regev–Stephens-Davidowitz, Definition 2.13 and §6](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) call the former task GDP, formulate a more general elliptical step, and require that its oracle succeed with all but negligible probability. The present calculation is solely for the spherical special case on a selected ideal family: it neither replaces their worst-case BDD promise nor supplies the requisite oracle or algorithm on all ideals.

The permutohedral Voronoi geometry is classical; see the original exposition by [Baek–Adams–Dolson](https://dspace.mit.edu/entities/publication/827b1496-12e5-48ee-9ee7-b1accf89f71d). [McKilliam–Subramanian–Viterbo–Clarkson](https://arxiv.org/abs/1111.6334) study finite-dimensional Gaussian error probabilities via Voronoi moments on the primal root lattices $A_n$. The result here is the signed-layer discrepancy on the *dual* root lattices, including its first omitted layer coefficient; the cited references do not supply that formula. This is a scoped comparison, not an exhaustive priority claim.

The accompanying verifier checks integer-scaled toy geometries, explicit missing-layer witnesses, and the small-cluster constants. The limiting probabilities follow from the proof, not the finite checks.
