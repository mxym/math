# Large simple faces in arbitrary polytopes with small local degree excess

**Yongxian Zhang.** AI-assisted proof development; internally reviewed, no priority claim.

A polytope need not be simple in edges to have many simple faces. We give an explicit moment-of-degree criterion for finding them. This transfers the known simple-polytope [cube–simplex theorem of De Loera–Fang–Guo–Lu–Zheng](https://arxiv.org/html/2609.00397v1) to arbitrary polytopes of dimension \(d\) and maximum vertex degree \(d+o(d)\); the theorem also allows some much larger degrees if the relevant average remains small. No general case without a degree restriction is claimed.

Let \(P\) be a convex \(d\)-polytope, \(N=f_0(P)\), and \(3\le r\le\lfloor d/2\rfloor\). Put
\[
 D_r(P)=\sum_{v\in V(P)}
       \left[\binom{\deg_P(v)}r-\binom dr\right],\qquad
 \mu_r(d)=\tfrac12\left[
     \binom{\lfloor d/2\rfloor}r+\binom{\lceil d/2\rceil}r\right],
 \qquad \gamma_r=\frac23+\frac1{3(r-2)}.
\]
Here a face is simple intrinsically: the degrees in that face, not in the whole \(P\), equal its dimension. The number \(s_r(P)\) of simple \(r\)-faces satisfies
\[
\boxed{\quad s_r(P)\ \ge\ N\mu_r(d)-\gamma_r D_r(P).\quad}
\tag{1}
\]
Without any external excess-gap result, the same proof gives (1) with coefficient \(1\) instead of \(\gamma_r\).

## 1. Budget for nonsimple corners

Fix \(v\), write \(Q_v=P/v\) for its \((d-1)\)-dimensional vertex figure, and put \(D_v=\binom{\deg_P(v)}r-\binom dr\). The vertices of \(Q_v\) correspond to the edges at \(v\). Each \((r-1)\)-face \(H\) of \(Q_v\) uses one or more affinely spanning \(r\)-subsets of these vertices. Such a subset cannot be used by two distinct \((r-1)\)-faces: their intersection would contain an affine \((r-1)\)-simplex, contradicting the dimension of an intersection of distinct faces of the same dimension.

More precisely, a face \(H\) with \(r+t\) vertices uses at least \(1+3t\) such subsets. Choose an affine basis \(B\) of \(r\) vertices. An extra vertex \(x\) has at least three nonzero affine coordinates in \(B\); otherwise three distinct extreme points would be collinear. Exchanging \(x\) for any of these at least three basis vertices yields a different affine basis. Bases made with different extra vertices are all different. This proves the claim even when the face has affine dependencies of other kinds.

Every \((d-1)\)-polytope has at least \(\binom dr\) faces of dimension \(r-1\), since the simplex minimizes face numbers. An elementary induction counts the faces in a facet plus those containing a vertex outside the facet, using that vertex figure, and adds the two binomial bounds by Pascal's identity. Hence
\[
 \sum_{\substack{F\ni v\\\dim F=r}}(\deg_F(v)-r)\ \le\ D_v/3 .
\tag{2}
\]
Indeed, \(F/v\) is the corresponding \((r-1)\)-face and has \(\deg_F(v)\) vertices. If \(n_v\) is the number of these faces whose corner at \(v\) is nonsimple, then \(n_v\le D_v/3\). Also at most \(D_v+n_v\le4D_v/3\) of the \(r\)-subsets at \(v\) fail to be the vertex sets of simplex \((r-1)\)-faces: the number that succeed is exactly the number of simplex faces of that dimension in \(Q_v\), at least \(\binom dr-n_v\).

## 2. Count faces from both extremes

Take a generic linear objective, so all vertex values are distinct. Let \(a_v\) and \(b_v\) count the ascending and descending edges at \(v\). Every \(r\)-subset of ascending edges that corresponds to a simplex face of \(Q_v\) gives a distinct \(r\)-face of \(P\) with minimum at \(v\): these \(r\) rays generate the tangent cone of that face at \(v\), so all nonzero directions in this cone increase the objective. The descending case counts maxima. The two sets of tested \(r\)-subsets at \(v\) are disjoint, and each \(r\)-face has one minimum and one maximum. Therefore
\[
 2f_r(P)\ \ge\
 \sum_v\left[\binom{a_v}r+\binom{b_v}r\right]-\tfrac43 D_r(P).
\]
The sum of the two binomial coefficients is smallest at a balanced split of a fixed total: discrete successive differences of \(\binom{x}r\) are \(\binom{x}{r-1}\) and are nondecreasing. Since \(a_v+b_v=\deg_P(v)\ge d\), we obtain \(f_r(P)\ge N\mu_r(d)-\tfrac23 D_r(P)\). Keeping the actual degree in each balanced split gives the sharper first term \(\sum_v\mu_r(\deg_P(v))\), both here and in (1).

Summing (2) over \(v\) shows that the sum of the *intrinsic* excess degrees of all \(r\)-faces is at most \(D_r(P)/3\). Each nonsimple \(r\)-polytope has excess degree \(\sum_{w\in V(F)}(\deg_F(w)-r)\) at least \(r-2\), by the [Excess Theorem of Pineda-Villavicencio, Ugon and Yost](https://arxiv.org/abs/1703.10702). Thus at most \(D_r(P)/(3(r-2))\) faces are nonsimple. Subtracting proves (1); using only the trivial excess lower bound of \(1\) gives the self-contained coefficient \(1\).

## 3. Consequences and scope

* Write \(\bar D_r=D_r(P)/N\). A simple \(r\)-face exists whenever \(\gamma_r\bar D_r<\mu_r(d)\). For fixed \(r\) and maximum degree \(d+o(d)\), \(\bar D_r=o(d^r)\) and \(\mu_r(d)\sim d^r/(2^r r!)\), so this criterion holds. In fact all but an \(o(1)\) fraction of the \(r\)-faces are simple: at most \(N\bar D_r/(3(r-2))\) are nonsimple, while \(f_r(P)\ge N(\mu_r(d)-2\bar D_r/3)\).
* If maximum degree is at most \((1+\alpha)d\) with a fixed \(\alpha\ge0\) satisfying \(\gamma_r[(1+\alpha)^r-1]<2^{-r}\), the same existence conclusion holds for all sufficiently large \(d\). The exact moment criterion, rather than the maximum, is what is needed.
* For any fixed \(\ell,k\), choose \(r\ge f_s(\ell,k)\) using the cited cube–simplex theorem in the simple class (trivial cases \(k=1\) or \(\ell=1\), Kalai's bound for \(k=\ell=2\), and the result for \(k\ge3\) also imply the remaining \(k=2\) cases). An extracted simple \(r\)-face has the required simplex or cube, which remains a face of \(P\). This proves the unrestricted-in-combinatorial-type degree-controlled subclass, not merely degenerate instances of edge simplicity.
* A simple-face dimension growing with \(d\) follows for a uniform degree bound \(d+C\) with \(C\ge1\) and \(M=d/C\to\infty\). For sufficiently large \(M\), take \(r=\lfloor\log_2 M-\log_2\log_2 M-2\rfloor\). Indeed \(\bar D_r\le C\binom{d+C-1}{r-1}\), whereas \(\mu_r(d)\ge\binom{\lfloor d/2\rfloor}r\). Their ratio is bounded above by
\[
    \frac{r2^r}{M}\,
    \frac{(1+1/M)^{r-1}}{(1-(2r-1)/d)^r}.
\]
The first factor is at most \(1/4\), and the second tends to \(1\) as \(M\to\infty\), since \(r=O(\log M)\), \(d\ge M\) and \(r^2/d\to0\). This verifies the criterion. A bounded excess \(C\) thus gives simple faces of dimension \(\log_2 d-\log_2\log_2 d-O(1)\).
* For a genuinely non-edge-simple family, take the product of the octahedron with the \((d-3)\)-cube for \(d\ge4\). Every vertex has degree \(4+(d-3)=d+1\), so there are no ambient simple vertices. Edges parallel to the cube factor are incident to four facets from the octahedral vertex and \(d-4\) cube facets, hence exactly \(d\) facets rather than \(d-1\). The large simple faces in this example are also visible directly via products; its role is to distinguish the hypothesis from edge simplicity, not to assert a new conclusion for this familiar product.

The ordinary excess-gap theorem is cited above. The newer [low total excess degree](https://arxiv.org/abs/2405.16838) results study a different parameter, \(\sum_v(\deg_P(v)-d)\), and bounded regimes in that total. Even maximum excess one at every vertex can make that total equal to \(N\), exponentially large in \(d\). Bounded primary-literature searches did not identify the basis-counting moment criterion or its simple-face consequence.
