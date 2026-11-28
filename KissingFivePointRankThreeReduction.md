# The worst five-point kissing energy is already attained in three dimensions

For $f(t)=t^4-t^2/4$ and five unit vectors with pairwise scalar products at most $1/2$, put
$
 C(X)=\min_{w_i\ge0,\ \sum_iw_i=1}\sum_{i,j}w_iw_j f(x_i\cdot x_j).
$

**Theorem (global rank reduction).** The maximum of $C(X)$ in arbitrary Euclidean dimension equals its maximum in $\mathbb R^3$. In particular, if any five-point $60^\circ$ code has $C(X)>1/4$, some global maximizer with that property has rank **exactly three**. Its distance from the planar stratum is positive in the quantitative sense of the [uniform near-planar theorem](https://github.com/mxym/math/blob/a2019b76cbe115d92a9328a507ed8b66092ac749/research/euclidean-tensor-geometry/KissingFivePointUniformPlanarStratum.md).

This is a reduction of the unrestricted global question to the sphere $S^2$, not a determination of the three-dimensional maximum. It also does not assert that *every* maximizer has rank at most three. The known comparison is $1/4$ on all planar $60^\circ$ codes, by [sharp circle quadrature](https://github.com/mxym/math/blob/e50e33215d387d70ba4d59e325b223dcd8e46075/research/euclidean-tensor-geometry/SharpSpacingCircleQuadrature.md).

## 1. Gram domain and positive weights

All feasible Gram matrices lie in the compact convex set
$
 \mathcal E=\{G=G^\mathsf T\succeq0:\ G_{ii}=1,\ G_{ij}\le1/2\ (i\ne j)\};
$
conversely each is realized by five vectors in $\mathbb R^5$. For every such $G$, the entrywise matrix $F_{ij}=f(G_{ij})$ is positive semidefinite. One direct proof avoids any restriction on the signs of coefficients in combinations of points: for real $b_i$ put $T=\sum_i b_i x_i^{\otimes4}$. Then $b^\mathsf TFb=\|T\|^2-\|\operatorname{Tr}T\|^2/4$, where a trace contracts two indices on symmetric four-tensors. In dimension $d\le5$,
$
 (\operatorname{Tr}\operatorname{Tr}^* S)_{ij}
   =\big((d+4)S_{ij}+(\operatorname{tr}S)\delta_{ij}\big)/6
$
for a symmetric two-tensor $S$: the adjoint is the average over the six placements of the metric tensor in $S\otimes I$. Its largest eigenvalue as a composite operator is $(d+2)/3$ (trace direction), so $\|\operatorname{Tr}T\|^2\le(7/3)\|T\|^2$. This proves the claim.

For $\tau>0$ regularize **only the choice of weights**, putting
$
 C_\tau(G)=\min_{w\in\Delta_5}\left(w^\mathsf TFw+
                   \tau\sum_i w_i\log w_i\right),\qquad 0\log0=0.
$
The minimum is strictly convex in $w$ and has unique strictly positive minimizing weights: at a zero component the entropy decrease on moving a small mass into it dominates the bounded polynomial slope. Uniformly $C(G)-\tau\log5\le C_\tau(G)\le C(G)$. At each feasible $G$ the derivative of the optimized value in a feasible direction is the partial derivative holding its minimizing $w$ fixed. This follows directly by sandwiching the change using the two optimal vectors before and after; continuity of the unique optimal vector follows by compactness. In the symmetric Frobenius pairing the gradient entries are
$
 K_{ij}=w_iw_j f'(G_{ij}).
$
Thus at a global maximum $G$ of $C_\tau$, the same $G$ maximizes the linear functional $\langle K,\cdot\rangle$ on $\mathcal E$, by taking right derivatives along all feasible line segments.

## 2. A five-cycle and a rank obstruction to its stress

Suppose $C_\tau(G)>1/4$. Join $i,j$ by a strong edge if $G_{ij}<-1/2$. This graph has no triangle, since the squared norm of the sum of three such vectors would be negative. It also has no independent triple: on an independent triple, all three absolute scalar products are at most $1/2$, so equal weights on the triple give $C(G)\le(3f(1)+0)/9=1/4$. A triangle-free graph on five vertices without an independent triple is a five-cycle: each vertex has at most two neighbors, and applying the same reasoning to the complementary graph gives degree at least two. Label this strong cycle in order, indices modulo five. The five remaining pairs are its chords $(i,i+2)$.

The *contact* chords (scalar product $+1/2$) form a matching. In fact, if two chords share a vertex, their other ends are joined by a strong edge. Two unit vectors at angle $60^\circ$ to a third have mutual angle at most $120^\circ$, contrary to that strong edge. Thus at least three chords are not contacts.

The linear semidefinite program from §1 is strictly feasible ($G=I$ satisfies all inequalities strictly). Its optimality conditions give a diagonal matrix $D$, symmetric nonnegative off-diagonal multipliers $U$ supported on the contacts, and a stress matrix $S\succeq0$ satisfying
$
 K=D+U-S,\qquad SG=0 .
$
Here the multiplier normalization can be absorbed into $U$. Complementarity gives $\langle S,G\rangle=0$, equivalent to $SG=0$ for two PSD matrices. In particular $S_{ij}=-w_iw_j f'(G_{ij})$ at every strong edge and noncontact chord.

For $u<-1/2$ we have $-f'(u)>1/4$. For $-1/2\le u\le1/2$ we have $-f'(u)\le1/4$: check the two endpoints and the only interior stationary points $\pm1/\sqrt{24}$ of the cubic. Thus $S\ne0$. Suppose its rank were one, $S=ss^\mathsf T$. Set $q_i=s_i/w_i$, which is legitimate because the entropy minimizer has no zero weights. Every strong edge satisfies $q_iq_{i+1}>1/4$; by connectivity the $q_i$ all have the same nonzero sign. Every noncontact chord satisfies $0<q_iq_{i+2}\le1/4$.

Among at least three noncontact chord starts, there are two consecutive indices $i,i+1$ on a five-cycle. Multiplying those two chord inequalities bounds $q_iq_{i+1}q_{i+2}q_{i+3}$ by $1/16$; multiplying the two strong inequalities at starts $i,i+2$ makes exactly the same product strictly greater than $1/16$. This contradiction proves $\operatorname{rank}S\ge2$, whence $SG=0$ implies $\operatorname{rank}G\le3$.

## 3. Removing the entropy

Let $M=\max_{\mathcal E}C$. A planar regular pentagon gives $M\ge1/4$; if equality holds the rank-reduction assertion already follows. Otherwise for all sufficiently small $\tau>0$, $\max C_\tau\ge M-\tau\log5>1/4$. Each regularized maximizer then has rank at most three by §2. Take a convergent subsequence as $\tau\downarrow0$. The rank-at-most-three locus is closed and $C_\tau\to C$ uniformly, so the limit attains $M$. Since every planar code has capacity $1/4$, its rank is exactly three.

**Further context.** The choice of the degree-four mixed kernel is important: on the strong edges its negative derivative exceeds every value allowed on a noncontact chord. The rank argument uses this separation, not a generic bound on extreme points of the elliptope. The entropy is needed to avoid presuming that the unregularized optimal weights are all positive. Run `python3 verify-kissing-five-point-rank-reduction.py` for exact five-vertex graph counts, the product obstruction for every contact placement, and rational tensor controls.
