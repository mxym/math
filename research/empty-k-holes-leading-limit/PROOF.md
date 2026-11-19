# Leading constants for empty convex polytopes in random point sets

Fix integers \(d\ge2\), \(k\ge d+1\) and a full-dimensional compact convex body \(K\subset\mathbb R^d\) of volume one. For a set of \(n\) independent uniform points in \(K\), a \(k\)-hole is an **unordered** subset of \(k\) points in convex position whose hull contains no other sample point in its interior. The samples are in general position almost surely. Write \(H_{d,k}^K(n)\) for the number of such subsets.

**Theorem.** The limit \(\lim_{n\to\infty}n^{-d} E H_{d,k}^K(n)\) exists and is finite and positive for every such \(d,k,K\). Formula (3) below describes it. The count and its limit are invariant under nonsingular affine transformations, with the uniform law transported to the new body, so volume one is only a normalization.

This is the all-dimension/all-size **existence** question in the Open problems paragraph of Balko, Scheucher and Valtr, [*Tight bounds on the expected number of holes in random point sets*](https://arxiv.org/pdf/2111.12533), p. 6 of the PDF, not their separate question about the numerical constant for empty tetrahedra in a tetrahedron. Those authors prove the order \(\Theta(n^d)\), and all planar limits were known, as were all simplex-size limits by Reitzner and Temesvari. No shape independence or closed-form evaluation in higher dimensions is claimed.

## Choosing an anchor in a fixed projection

Let \(\pi:\mathbb R^d\to\mathbb R^{d-1}\) forget the last coordinate. For a full ordered tuple of \(k\) points select the set of \(d\) points whose projections span a \((d-1)\)-simplex of largest volume. This set is unique almost surely: two distinct label sets give two squared determinant polynomials whose difference is not identically zero. Indeed one label occurs in only one set, and varying its projection normally to the affine span of the other \(d-1\) projections of that set makes its determinant nonconstant when those others are in general position. Projected uniform points have an absolutely continuous joint law. The maximum determinant is positive almost surely.

By exchangeability it suffices to integrate the part for which labels \(1,\ldots,d\) are selected and multiply by \({k\choose d}\). There is no ordering factor within that set: we use its given label order. Write its points as \(b_1,\ldots,b_d\in K\); the \(d\times(d-1)\) matrix \(B\) has columns \(b_2-b_1,\ldots,b_d-b_1\); put \(J=|\det(\pi B)|>0\). For each of the \(m=k-d\) other points use coordinates
\[
 x_i=b_1+B u_i+\frac{h_i}{n J}e_d
 \qquad(u_i\in\mathbb R^{d-1},\ h_i\in\mathbb R).
 \tag{1}
\]
The absolute determinant of this full affine change is \(1/n\) for each point, even for arbitrarily small \(J>0\). In the new space the anchors are \((0,0),(e_1,0),\ldots,(e_{d-1},0)\). Denote the ordered configuration of these anchors and the \((u_i,h_i)\) by \(D(u,h)\), its \(d\)-hull volume by \(U(u,h)\), and the indicator of its convex position by \(I(u,h)\). Both convex position and the hull scale are exact: the old indicator is \(I\), and the old volume is \(U/n\).

Denote by \(A(u)\) the indicator that \(0,e_1,\ldots,e_{d-1}\) form the unique largest projected simplex among the horizontal coordinates of \(D\). This depends neither on \(h\) nor on \(n\), since \(\pi x_i=\pi b_1+(\pi B)u_i\). In particular \(A(u)=1\) implies \(|(u_i)_j|\le1\) for all \(i,j\): replace \(e_j\) in the standard simplex by \(u_i\) and compare its absolute determinant to one. Also,
\[
 U(u,h)\ge \frac{\max_i|h_i|}{d!},
 \tag{2}
\]
by taking the simplexes formed by the anchors and one extra point.

## The limit

Conditional on the first \(k\) points, the chance the remaining \(n-k\) independent points avoid their hull is \((1-|\operatorname{conv}(x_1,\ldots,x_k)|)^{n-k}\); boundary points have probability zero. Thus, after (1), the exact expected count is
\[
 {n\choose k}{k\choose d} n^{-m}
 \int_{K^d}\int A(u) I(u,h)\,
 \prod_{i=1}^m {\bf1}_K\left(b_1+Bu_i+\frac{h_i}{nJ}e_d\right)
 (1-U(u,h)/n)_+^{n-k}\,du\,dh\,db
\]
for \(n>k\). Here and below the inner integral is over \(\mathbb R^{m(d-1)}\times\mathbb R^m\), and \(db=db_1\cdots db_d\). The positive part outside the admitted domain is harmless; whenever all physical points lie in \(K\), their hull has volume at most one.

For almost every anchor tuple all anchors are interior to \(K\) and \(J>0\). Their hyperplane \(E=b_1+\operatorname{im}B\) therefore meets \(\operatorname{int}K\). Its section satisfies \(E\cap\partial K=\partial_E(K\cap E)\): a supporting plane to \(K\) through any point of \(E\cap\partial K\) cuts \(E\) properly since \(b_1\) is interior, and gives a supporting hyperplane in \(E\). The converse follows from openness of \(\operatorname{int}K\). This relative boundary has \((d-1)\)-measure zero as the boundary of a full-dimensional convex body within \(E\). Since \(u\mapsto b_1+Bu\) is an affine isomorphism onto \(E\), for almost every \(u\) and each fixed \(h\) all physical membership indicators converge to \({\bf1}_K(b_1+Bu_i)\).

As \(n\to\infty\), the binomial avoidance factor converges to \(e^{-U}\). For \(n\ge2k\) the integrand is bounded by
\[
 {\bf1}_{[-1,1]^{m(d-1)}}(u)\exp\!\left(-\frac{\|h\|_\infty}{2d!}\right).
\]
This is integrable, independently of the anchors, by (2) and the volume growth of cubes in \(\mathbb R^m\). Thus dominated convergence gives the finite limit
\[
 \boxed{\displaystyle
 \frac{{k\choose d}}{k!}
 \int_{K^d}\int A(u)I(u,h)e^{-U(u,h)}
        \prod_{i=1}^m{\bf1}_K(b_1+Bu_i)\,du\,dh\,db .}
 \tag{3}
\]
Indeed \(n^{-d}{n\choose k}n^{-(k-d)}\longrightarrow 1/k!\). Positivity follows from the strictly positive \(\liminf n^{-d} E H^K_{d,k}(n)\) in Balko–Scheucher–Valtr, Theorem 1. This is an application of their lower bound, not a new proof of it.
