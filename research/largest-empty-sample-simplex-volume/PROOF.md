# The largest empty simplex with sample vertices

Let $K$ be a convex body of positive volume in fixed dimension $d\ge2$, and let $X_1,X_2,\ldots$ be independent uniform points of $K$. Let $T_n$ denote the maximum volume of a simplex with $d+1$ vertices among the first $n$ points and with none of these $n$ points in its interior. Let $P_n$ denote the corresponding maximum over convex polytopes with sample vertices, with no upper bound on their number. Then, almost surely,
$$
 \lim_{n\to\infty}\frac{nT_n}{|K|\log n}
 =\lim_{n\to\infty}\frac{nP_n}{|K|\log n}=d.
$$
In the plane this gives constant 2, already with only three vertices, for the polygonal-hole part of the question in Arizmendi–Salazar, §6 (their Theorem 1.3). The unrestricted empty-convex-body constant is *not* a new assertion here: Peres–Yang, arXiv:2610.09790v2, Theorem 1.3, gives that almost-sure upper bound and a matching lower bound without the sample-vertex restriction. We use their upper bound. The construction below combines their thin-target/second-moment approach with vertex localization in the spirit of Arizmendi–Salazar §5.

## Thin candidates

By scaling take $|K|=1$. Fix an interior ball $B(0,r)\subset K$, after translation. Write $a>0$ for a small target volume. In the hyperplane $x_d=0$ fix a nondegenerate $(d-1)$-simplex of $(d-1)$-volume $A$ in $B(0,r/4)$. Join this base to the apex $we_d$, with $w=da/A$. This gives a simplex of volume $a$ in a slab of width $w$. Copies rotated about 0 and then translated by $s\nu$, where $\nu$ is the rotated normal and $|s|\le r/4$, remain in the ball for small $a$.

For integer $N$ large take $a=(d-\varepsilon)\log N/N$, $0<\varepsilon<d$, and $\delta=w(\log N)^5$. Choose a maximal $\delta$-separated family of normals (angular metric) in a fixed spherical cap of radius $1/8$. It has at least $c\delta^{-(d-1)}$ members, since its $\delta$-balls cover the cap and each has area at most $C\delta^{d-1}$. For each normal take all translations at spacing $2w$ in the above interval. The resulting family has size
$$
 M\ge c w^{-1}\delta^{-(d-1)}.
$$
Different copies with the same normal are disjoint. For different normals making angle $\alpha$, the two slabs intersect within the ball in volume at most $Cw^2/\sin\alpha$: project onto the span of the normals, where the parallelogram has area $w^2/\sin\alpha$, and bound the $(d-2)$-dimensional fibers by the ball's corresponding bound (by 1 for $d=2$). In our cap $\sin\alpha\ge c\delta$. Thus any two distinct simplices $R,S$ have intersection volume $I_{RS}\le Cw(\log N)^{-5}$, so $NI_{RS}=O((\log N)^{-4})$.

## The vertex step

Put $t=d+1$. Fix a small $0<\rho<1/2$, independent of $N$. At each vertex $v_i$ of a candidate $R$ mark the copy $C_i=v_i+\rho(R-v_i)$. The $t$ copies are disjoint: their respective $i$-th barycentric coordinates are at least $1-\rho>1/2$. Each has volume $b=\rho^d a$. Remove them from $R$ to obtain the core $F$, of volume $f=a-tb$.

For any selection $x_i\in C_i$, the matrix of their barycentric columns relative to $R$ has each column within $2\rho$ in one-norm of the corresponding identity column. Its determinant gives the signed simplex volume ratio: in homogeneous coordinates its matrix multiplies the vertex matrix of $R$. Uniformly over candidates and all selections this determinant lies within $e(\rho)$ of 1, where $e(\rho)\to0$ as $\rho\downarrow0$, by continuity of the determinant at the fixed identity matrix. Take $\rho$ small enough that all these simplices have positive volume.

Call $R$ good for a block $m\le N$ if no point among the first $N$ lands in $F$, and each $C_i$ receives at least one of the first $m$ points. For every $m\le n\le N$, among all choices of one of the first $n$ points from each $C_i$, take a simplex of least volume. It is empty: any other sample point of the first $n$ in its interior belongs to $R$ and therefore to some $C_j$. Replacing the chosen vertex $x_j$ by this interior point preserves the selection constraints and multiplies its volume by the point's $j$-th barycentric coordinate relative to the selected simplex, strictly between 0 and 1. This contradicts minimality. Consequently $T_n\ge(1-e(\rho))a$ throughout the block whenever any candidate is good. This argument uses a possibly different minimizing simplex at different $n$; no monotonicity of $T_n$ is presumed.

## Occupancy on a block

Assume $m\ge\gamma N$ for a fixed $\gamma>0$. Conditional on avoiding $F$ until $N$, the first $m$ points remain independent uniform on $K\setminus F$; hence each candidate's goodness probability $p$ satisfies
$$
 (1-f)^N(1-t e^{-mb/(1-f)})\le p\le(1-f)^N.
$$
The conditional error is $O(N^{-c_1})$ for fixed parameters, since $mb\ge\gamma\rho^d(d-\varepsilon)\log N$. For the number $Z$ of good candidates, $\mathbb EZ=Mp\ge N^{\varepsilon}/(\log N)^{C}$ times a positive constant for all large $N$: use $f\le a$, $Na^2=o(1)$, and the family-size estimate.

For distinct candidates, both cores must be avoided, so their joint goodness probability is at most $(1-2f+I_{RS})^N$. Since $1-2f+I_{RS}\le(1-f)^2+I_{RS}$, its ratio to $p^2$ is at most
$$
 (1-O(N^{-c_1}))^{-2}
 \exp\{NI_{RS}/(1-f)^2\}
 =1+O(N^{-c_1}+(\log N)^{-4})
$$
uniformly. Expanding the variance and applying Chebyshev therefore gives
$$
 \Pr(Z=0)\le (Mp)^{-1}+O(N^{-c_1}+(\log N)^{-4}).
$$
All constants may depend on the fixed dimension, body, and parameters.

Fix $\eta>0$, take $n_j=\lfloor(1+\eta)^j\rfloor$, and apply this result with $m=n_j, N=n_{j+1}$. Some $\gamma>0$ works for every sufficiently large $j$; the failure probabilities are summable in $j$. By Borel–Cantelli, almost surely every sufficiently late block is good in the sense of having at least one good candidate. Throughout these blocks,
$$
 \liminf_{n\to\infty}\frac{nT_n}{\log n}
 \ge \frac{(1-e(\rho))(d-\varepsilon)}{1+\eta},
$$
using $n/N\ge n_j/n_{j+1}$ and $\log N/\log n\ge1$. Now send $\eta,\varepsilon,\rho\downarrow0$ along countable sequences. Finally $T_n\le P_n\le V^*_n$, where $V^*_n$ is exactly the unrestricted maximum of Peres–Yang Theorem 1.3, so its almost-sure upper bound supplies both limsups. Undo the volume normalization. ∎
