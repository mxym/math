# A strict separation between two central spectral gaps

In [Guo and Zhang, *Finite projective planes meet spectral gaps*](https://arxiv.org/html/2509.06247v2), Question 1 asks for two suprema: one over regular graphs of degree $d$, the other over graphs of minimum degree at least $d$. For infinitely many $d$ the second supremum is strictly larger than the first. A plane of order seven already separates them when $d=7$.

This observation excludes the suggested block-size-$d$ designs from attaining or approximating the larger supremum in these cases. It **does not compute either supremum**, identify a maximizing graph, or rule out design maximizers for the regular problem. A separate remark below considers three explicit interpretations of the authors’ Question 2.

## 1. The normalized gap

Let $G$ be finite, simple and connected, on at least three vertices, with adjacency and degree matrices $A,D$. Put $R=D^{-1/2}AD^{-1/2}$ and $g(G)=\min_{\lambda\in\sigma(R)}|\lambda|$. This equals the distance from $1$ to the spectrum of $I-D^{-1}A$, since $D^{-1}A$ is similar to $R$. For a family $\mathcal G$ let $g(\mathcal G)=\sup_{G\in\mathcal G}g(G)$. Write $\mathcal G_{=d}$ for graphs in which **every** vertex has degree $d$, and $\mathcal G_{\ge d}$ for those in which every vertex has degree at least $d$.

**Proposition.** If $d\ge3$, a projective plane of order $d$ exists and none of order $d-1$ exists, then

$$
g(\mathcal G_{=d})\le\frac{\sqrt{d-2}}{d}
<\frac{\sqrt d}{d+1}\le g(\mathcal G_{\ge d}).
$$

**Proof.** The left inequality is Guo–Zhang, Theorem 4. For the right inequality take the incidence graph of the order-$d$ plane. Its incidence matrix $M$ has $N=d^2+d+1$ rows and columns. Each row and column sums to $d+1$, and any two points lie on exactly one common line. Thus $MM^\top=dI+J$, where $J$ is the all-ones matrix. The eigenvalues of this Gram matrix are $(d+1)^2$ once and $d$ with multiplicity $N-1$. The bipartite adjacency with off-diagonal blocks $M,M^\top$ has eigenvalues equal to the signed singular values of $M$. Its graph is connected and $(d+1)$-regular, so $g(G)=\sqrt d/(d+1)$. Finally $d^3-(d-2)(d+1)^2=3d+2>0$ gives the strict middle inequality. ∎

**Which designs does this exclude?** A symmetric $2$-$(v,d,\lambda)$ design has a $d$-regular incidence graph. A nonsymmetric design has different numbers of points and blocks, so its bipartite adjacency has a zero eigenvalue, which persists under degree normalization. Indeed, for square incidence matrices the constant replication number is $d$ by double-counting incident point–block pairs. This covers the customary interpretation with or without symmetry. The proposition neither assumes nor proves that the larger supremum is attained.

**Witnesses.** The [Bruck–Ryser theorem](https://doi.org/10.4153/CJM-1949-009-2) excludes order $6$: it is $2\bmod4$ and the prime $3$ occurs to odd exponent. In contrast, points and lines of $\mathrm{PG}(2,7)$ are given by projective triples over $\mathbf F_7$ (lines use normal vectors), incident when the dot product is zero. Its 57 points and 57 lines have 456 incidences. For $d=7$ the squared comparison is $7/64>5/49$, or $343>320$.

For every integer $m\ge0$, $d=7^{6m+1}$ is a prime power, hence supplies $\mathrm{PG}(2,d)$. Since $(1+6)^{6m+1}\equiv7\pmod{36}$, its predecessor is $2\bmod4$ and is divisible by $3$ exactly once. Bruck–Ryser excludes that order, giving the stated infinite family.

**Relation to the source.** Immediately before Question 1, Guo–Zhang already use biplanes of degree higher than three in the minimum-degree-three class to beat the nonplane cubic threshold. For $d=3$ the order-two plane exists, so their example does not satisfy Question 1’s premise. The proposition uses their own regular bound and the same change of admissible degree; it does not contradict their theorems or establish a new general spectral estimate.

## 2. The unnormalized gap depends on the comparison class

Question 2 does not specify a family in which to optimize the distance from the mean of the spectrum of $L=D-A$. For a graph with $n$ vertices and $m$ edges let $h(G)=\min_{\lambda\in\sigma(L)}|\lambda-2m/n|$. The following comparisons concern the constraints named, not an unstated interpretation of the question.

For $1<a<b$, the eigenvalues of $L(K_{a,b})$ are $0,a,b,a+b$ with respective multiplicities $1,b-1,a-1,1$. The two parts’ coordinate-sum-zero spaces give the middle values and the two-dimensional quotient gives the others. The mean $\mu=2ab/(a+b)$ lies between $a$ and $b$ and is closer to $a$. Thus $h=a(b-a)/(a+b)$. In a plane incidence graph of order $q$, regularity instead gives $h=\sqrt q$. Compare the order-49 plane, of degree 50 and gap 7, with:

| Quantity held fixed | Competitor | Its gap |
| --- | --- | ---: |
| Maximum degree $50$ | $K_{20,50}$ | $60/7$ |
| Minimum degree $50$ | $K_{50,150}$ | $25$ |
| Average degree $50$ | $K_{30,150}$ | $20$ |

Each competitor beats the plane under that individual constraint. With no constraint, $K_{2k,6k}$ has $h=k$, so the gaps are unbounded. Among **regular** graphs of fixed degree $d$, by contrast, $L=dI-A$ and Guo–Zhang Theorem 1 gives plane extremality when a plane of order $d-1$ exists. Nothing here is asserted for joint constraints on the numbers of vertices and edges.

## Verification

This is an AI-assisted research draft with independent internal AI review, not external peer review, formal verification or a claim of priority. The analytic argument applies at all the stated parameters. From this directory run the finite checks with Python 3.10 or later, without optimization:

    python3 check.py
    python3 independent.py

The first checks all 3,249 Gram entries over the prime field. The second constructs the order-7 and order-49 planes by completing affine coordinate systems, checks the point degrees and every pair of distinct lines, and independently evaluates the comparisons.
