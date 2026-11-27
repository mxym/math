# Narrow lattice-Gaussian covariance from tilted Delaunay cells

For a fixed full-rank Euclidean lattice \(L\) in its real span \(V\), let \(X_{t,c}\) on \(L\) have masses proportional to \(\exp(-t\|x-c\|^2)\), with precision \(t>0\) and arbitrary center \(c\in V\). The precision parameter tends to infinity in the narrow limit. Write
\[
\mathcal C_L(t)=\sup_{c\in V}\|\operatorname{Cov}(X_{t,c})\|_{\rm op}.
\]
For a center \(v\), let \(S(v)\) be the set of closest lattice points to \(v\). It is the vertex set of a Delaunay cell, possibly of dimension zero or a proper face. For finite nonempty \(S\subset V\), let \(P_{S,h}\) assign each \(x\in S\) probability proportional to \(e^{\langle h,x\rangle}\), where \(h\in V\).

**Theorem.** The set of all subsequential covariance limits of \(X_{t,c_t}\) as \(t\to\infty\), allowing arbitrary varying centers, is exactly
\[
\left\{\operatorname{Cov}(P_{S(v),h}):v,h\in V\right\}.
\tag{1}
\]
This set is compact. In particular
\[
\mathcal C_L(t)=\mathcal C_L^\infty+O_L(e^{-\kappa_L t}),
\qquad
\mathcal C_L^\infty=\max_{v,h}\|\operatorname{Cov}(P_{S(v),h})\|_{\rm op},
\tag{2}
\]
for some \(\kappa_L>0\) and an implicit constant depending only on the fixed lattice. The maximum on the right is attained. This convergence does not assume the centers stay away from Voronoi boundaries.

For the usual Euclidean scales of the classical lattices,
\[
\mathcal C_{\mathbb Z^n}^\infty=\frac14,\qquad
\mathcal C_{A_n}^\infty=\frac12,\qquad
\mathcal C_{D_n}^\infty=\frac12\ (n\ge2),\qquad
\mathcal C_{A_n^*}^\infty=
\frac{\lfloor(n+1)^2/4\rfloor}{4(n+1)}.
\tag{3}
\]
When both \(A_n\) and \(A_n^*\) are rescaled so that the shortest nonzero vector has length one, the constants are \(1/4\) and \(\lfloor(n+1)^2/4\rfloor/(4n)\), respectively. The dual's worst narrow covariance thus grows linearly in the rank even at fixed shortest-vector normalization.

## 1. A local finite-support reduction, uniform over centers

Covariance does not change when \(c\) and the lattice sample are translated by the same lattice vector. We may restrict \(c\) to a compact fundamental region. Fix \(v\) in that region and put \(S=S(v)\). At \(v\), every lattice point outside \(S\) has a strictly positive squared distance gap to \(S\), with a positive minimum over the outside points by discreteness. Choose a small neighborhood of \(v\) so that on the neighborhood the squared distance from any outside point exceeds the minimum squared distance to \(S\) by at least some \(\delta>0\). Here one first handles a finite bounded set by continuity; faraway points have a gap that grows quadratically in their norm, locally uniformly.

More explicitly, in this neighborhood the Gaussian mass of outside points, divided by the mass of a closest point in \(S\), and with each outside term multiplied by \(1+\|x\|^2\), is \(O(e^{-\kappa t})\) for some \(\kappa>0\) and all \(t\ge1\). The finite nearby part uses the uniform gap. Beyond a sufficiently large radius the gap is at least \(\delta/2+\|x\|^2/8\), so the far part is bounded by an \(L\)-dependent Gaussian moment sum times \(e^{-t\delta/2}\). The mass ratio gives a uniform bound for the corresponding normalized moments. Conditional on \(X_{t,c}\in S\), the law is *exactly* \(P_{S,2t(c-v)}\): expansion at \(v\) leaves the same constant \(\|x-v\|^2\) for every \(x\in S\). Boundedness of \(S\) now gives an \(O(e^{-\kappa t})\) operator-norm error in covariance. A finite cover of the compact fundamental region makes this upper bound uniform for all \(c\), with constants depending on \(L\).

Here are two usual finite-set facts, with their application to \(S(v)\).

- The closure of the exponential tilts on a finite set of vertices consists of the same tilts on its exposed faces, including the full set. For a sequence of tilt vectors first project onto the span of the affine differences. A bounded subsequence there has a finite-parameter limit. Otherwise pass to a subsequence whose unit directions converge to a unit vector in that span. All vertices outside its maximizing proper face lose their mass, as the relative logarithmic weight compared with any maximizing vertex tends to minus infinity. The conditional laws on the face are still exact tilts, and one repeats in smaller affine span. Conversely every finite tilt on an exposed face is approached by adding an increasingly large multiple of an exposing functional.
- A face of \(\operatorname{conv}(S(v))\) exposed by \(h\) is itself a closest-point set: take \(v+\epsilon h\) for a sufficiently small \(\epsilon>0\). The old outside gap persists, and within \(S(v)\) the nearest sites are precisely the maximizers of the linear functional. The argument also applies to faces of faces.

There are only finitely many distinct nearest sets with centers in a compact fundamental region, since these sets lie in a common bounded ball. Translations of the region add only translates of those sets and do not change covariance under tilting. The two facts above show that the union of their tilt covariance sets is already closed, hence compact. By the uniform finite-support reduction, every limit lies in this union. For any chosen \(S(v),h\), the centers \(c_t=v+h/(2t)\) are eventually in the neighborhood of \(v\), and give covariance \(\operatorname{Cov}(P_{S(v),h})+O_{L,v,h}(e^{-\kappa t})\). This proves (1). Choose one attaining pair for the operator norm on the compact union and use that pair for the lower bound in (2), and the uniform reduction for the upper bound. A fixed nearest pair with equal tilt weights contributes one quarter of the squared pair distance as an operator norm. More generally, the diameter of a nearest set gives an upper bound of one quarter its squared diameter by the scalar bounded-range variance inequality in every unit direction. The calculations below sharpen that upper bound when a cell is not a simplex.

## 2. Integer and type-\(A\) root lattices

A nearest set for \(\mathbb Z^n\) is a product of singletons and pairs of consecutive integers, so any tilt is a product with coordinate variances at most \(1/4\). At a coordinate half-integer an unbiased pair attains \(1/4\).

Put \(N=n+1\), \(H=\{x:\sum_{i=1}^N x_i=0\}\), and \(A_n=H\cap\mathbb Z^N\). Its Voronoi cell around zero is precisely
\[
\max_i c_i-\min_i c_i\le1 \qquad(c\in H).
\]
Indeed, a larger range violates the constraint from some root \(e_i-e_j\), and if the range is at most one then \(\langle c,z\rangle\le\sum_i z_i^+=\tfrac12\sum_i|z_i|\le\tfrac12\sum_i z_i^2\) for all \(z\in A_n\). If the range is strictly less than one, zero is unique. At range exactly one, equality for a lattice vector requires every nonzero coordinate to be \(\pm1\), with the \(+1\)'s only at coordinates attaining \(\max_i c_i\) and the \(-1\)'s only at those attaining \(\min_i c_i\). In that union of coordinate sites, translate by adding 1 on each low site. The set of lattice vectors with equality becomes the set of all zero-one vectors with exactly as many ones as there are low sites; all other sites are fixed. For a center not in the cell around zero, first translate by any closest lattice point.

Thus the nontrivial tilted law is a weighted fixed-size subset: weights are products of positive site weights. Its covariance matrix on the active coordinates has nonpositive off-diagonal entries and row sum zero. For the off-diagonal sign, fix distinct sites \(i,j\) and let \(e_\ell\) denote the elementary symmetric sum of degree \(\ell\) over the other positive site weights, with out-of-range values zero. The \(2\)-by-\(2\) inclusion table of \(i,j\) has unnormalized weights \(e_k,w_i e_{k-1},w_j e_{k-1},w_iw_j e_{k-2}\). Its covariance sign is the sign of \(e_ke_{k-2}-e_{k-1}^2\), nonpositive by Newton's inequality. Row sum zero follows from the fixed total. Every diagonal variance is at most \(1/4\), so each absolute row sum is at most \(1/2\), bounding the operator norm. The center \((e_1-e_2)/2\) gives exactly the closest pair \(0,e_1-e_2\), attaining \(1/2\).

A check against a plausible shortcut: for **a fixed direction**, the longest projected Delaunay edge need not bound the limiting directional variance. For even \(N\), a center with \(N/2\) high sites at \(1/2\) and \(N/2\) low sites at \(-1/2\) gives the uniform \(N/2\)-subset under zero tilt. On \(H\) its covariance is \(N/(4(N-1))\) times the identity. Along a unit vector having half its entries \(1/\sqrt N\) and half \(-1/\sqrt N\), the largest projected root edge has length \(2/\sqrt N\), giving only \(1/N\) after squaring and dividing by four. All hypersimplex edges are swaps of one selected and one unselected site: two subsets differing by at least two swaps have their midpoint shared with another pair off their segment. Thus considering every Delaunay edge does not remove this discrepancy.

## 3. The type-\(D\) root lattices

Let \(D_n=\{z\in\mathbb Z^n:\sum_i z_i\text{ even}\}\). At a center with half-integer ties in some coordinates, the nearest set uses the closest integer in each untied coordinate and one of two adjacent integers in each tied coordinate. One can always satisfy the even parity constraint among these choices. Hence the set is a translated parity subset of a binary cube in the tied coordinates.

If there are no ties, first take the unique closest point \(z\) of \(\mathbb Z^n\). If it has even sum, the nearest \(D_n\) point is unique. Otherwise parity must be corrected by increments of odd total. Changing a single coordinate by one toward its closer alternative costs \(1-2|c_i-z_i|>0\) in squared-distance increase. A correction with more than one changed coordinate costs strictly more than the least such single-coordinate cost, and a change of absolute size at least two on a coordinate cannot minimize it. The tied minimizing choices thus consist of one flip in each of the coordinates with largest residual absolute value. If that value is nonzero, there is only one sign for each such coordinate, and all the resulting sites are mutually separated by \(\sqrt2\). If it is zero, both signs occur at every coordinate, giving the translated crosspolytope \(\{\pm e_i\}\). The singleton and one-sign cases satisfy the bound \(1/2\) directly by the diameter inequality.

For a parity subset of a cube, put the tied sites in spin coordinates \(s_i\in\{-1,1\}\), so their original coordinates equal \((1+s_i)/2\) up to translation. The tilted law is a product with means \(m_i=\tanh h_i\), conditioned on \(\prod s_i=\varepsilon\) of either parity. By flipping signs one may assume \(0\le m_i<1\) while changing \(\varepsilon\) if necessary. Put \(q_i=\prod_{j\ne i}m_j\), \(r_{ij}=\prod_{\ell\ne i,j}m_\ell\), \(P=\prod_j m_j\). The indicator of the conditioning is \((1+\varepsilon\prod s_i)/2\). Taking expectations with it gives the spin covariance entries
\[
V_{ii}=\frac{(1-m_i^2)(1-q_i^2)}{(1+\varepsilon P)^2},
\qquad
V_{ij}=\frac{\varepsilon(1-m_i^2)(1-m_j^2)r_{ij}}{(1+\varepsilon P)^2}\quad(i\ne j).
\tag{4}
\]
For any list \(0\le x_j\le1\) with product \(q\) one has
\[
\sum_j(1-x_j^2)\prod_{\ell\ne j}x_\ell\le1-q^2.
\tag{5}
\]
For the induction step appending \(x\), the left side is at most \(x(1-q^2)+(1-x^2)q=(x+q)(1-xq)\le1-x^2q^2\). The initial empty list gives zero. Applying (5) to the list with \(i\) removed shows that the off-diagonal absolute row sum in (4) is at most \(V_{ii}\). Thus the spin covariance norm is at most \(2\max_i V_{ii}\le2\); converting to zero-one coordinates gives \(1/2\).

It remains to bound covariance of a tilt on the crosspolytope. For the tilt vector \(h\) put \(A_i=\cosh h_i,\ B_i=\sinh h_i\), \(P=\sum_i A_i\). The covariance is
\[
V=\operatorname{diag}(A_i/P)-BB^{\mathsf T}/P^2.
\]
If every \(A_i\le P/2\), the claimed upper bound follows from the diagonal matrix. Otherwise let \(A=A_1>P/2,\ S=P-A\), and \(\lambda=P(A-S)/2>0\). For every \(i\ge2\), let \(D_i=P(P/2-A_i)\ge\lambda\), since \(A_i\le S\). Multiplying \(\tfrac12 I-V\) by \(P^2\), the problem is positivity of \(\operatorname{diag}(-\lambda,D_2,\ldots,D_n)+BB^{\mathsf T}\). Minimizing over all coordinates except the first in its quadratic form shows this holds if
\[
B_1^2\ge\lambda\left(1+\sum_{i\ge2}B_i^2/D_i\right).
\]
For clarity, the minimum at first coordinate \(x\) of \(\sum_{i\ge2}D_i y_i^2+(B_1x+\sum_{i\ge2}B_i y_i)^2\) equals \(B_1^2x^2/(1+\sum_{i\ge2}B_i^2/D_i)\) by completing the square or differentiating. The displayed right side is at most \(\lambda+\sum_{i\ge2}B_i^2\le(A^2-S^2)/2+S^2-(n-1)\). Since \(B_1^2=A^2-1\), their difference is at least \((A^2-S^2)/2+n-2\ge0\), as desired.

Finally \((e_1+e_2)/2\) has exactly the two nearest \(D_n\) sites \(0,e_1+e_2\). Their equal-weight covariance attains \(1/2\). This finishes \(D_n\) including \(n=2\).

## 4. The dual \(A_n^*\)

Use again \(N=n+1\) and \(H=\mathbf 1^\perp\), with orthogonal projection \(P\) onto \(H\). Then \(A_n^*=P\mathbb Z^N\) since having integral differences between coordinates is exactly being dual to all \(e_i-e_j\). Write \(u_S=P\mathbf1_S\) for nonempty proper \(S\subset\{1,\ldots,N\}\). Every lattice vector has a representative in \(\mathbb Z^N\) with minimum coordinate zero. Decompose that representative into its nested nonempty proper integer threshold sets; its projection is the sum of the associated \(u_S\)'s. For nested nonempty proper sets \(S\subseteq T\), one has \(\langle u_S,u_T\rangle=|S|(N-|T|)/N>0\). Consequently the Voronoi inequalities \(\langle c,u_S\rangle\le\|u_S\|^2/2\) alone suffice: for a sum of at least two layers the inequality obtained by adding them is strictly stronger than the required one by the positive cross terms. If two lattice points are both nearest to any center, their difference must be one \(u_S\), by translating one of the points to zero and applying this observation. Thus every nearest set has squared diameter at most
\[
\max_{1\le k<N} k(N-k)/N=\lfloor N^2/4\rfloor/N.
\]

For every \(S\), the midpoint \(u_S/2\) has just \(0,u_S\) as closest sites. Indeed
\[
\langle u_S,u_T\rangle=|S\cap T|-|S||T|/N\le |T|(N-|T|)/N=\|u_T\|^2,
\]
with equality only if \(S=T\). This follows by replacing the intersection size by \(\min(|S|,|T|)\) and checking the two size orderings; both inequalities can be equal only for identical sets. Multi-layer vectors give a strict inequality as above. Choose \(S\) of size nearest \(N/2\), so the equal-weight pair gives the maximum diameter upper bound. The same decomposition shows that the shortest squared length of \(A_n^*\) is \((N-1)/N\): a single-layer singleton gives it, and each layer contributes at least that much to the squared norm, with strictly positive cross terms if there is more than one layer. Along with \(\lambda_1(A_n)^2=2\), this proves the normalized comparison.

## Scope and references

[Regev–Stephens-Davidowitz, *An Inequality for Gaussians on Lattices*](https://arxiv.org/abs/1502.04796) relates shifted lattice theta masses, heat kernels and moment inequalities. The result here compares covariance at the true mean in the narrow-width limit, uniformly over all moving centers; positions near the boundaries of Voronoi cells cannot be ignored in that comparison. The classical Delaunay descriptions for root lattices appear for example in [Koca et al., *Explicit Construction of the Voronoi and Delaunay Cells of \(W(A_n)\) and \(W(D_n)\) Lattices and Their Facets*](https://arxiv.org/abs/1804.05836); the proof above derives the needed closest-point sets directly. The covariance calculation is not a claim to discover those polytopes.

With canonical trace scaling, standard prime-conductor cyclotomic integer lattices and their trace-dual geometries are respectively proportional to \(A_n^*\) and \(A_n\); see [van Woerden, §3](https://math.leidenuniv.nl/scripties/BachVanWoerden.pdf). Formulas (1)–(3) concern the abstract unwrapped Gaussian with a varying Euclidean center at a fixed lattice. They do not assert a dimension-uniform convergence rate, anything at prescribed finite width, or a cryptographic exploitation or hardness implication.

Replay with `node verify-delaunay-gaussian-covariance.js`. The last run passed 194,586 exact and 252 numerical checks. These include weighted subset and parity covariances, exact principal minors for crosspolytope covariance bounds, and a direct finite-lattice check of the tilted pair law on each of the four lattice families.
