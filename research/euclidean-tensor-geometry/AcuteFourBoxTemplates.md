# Ten-site templates from an orthogonal four-dimensional box cannot be made acute by small perturbation

**Theorem.** Let \(a,b,c,d>0\), let \(Q=\{0,a\}\times\{0,b\}\times\{0,c\}\times\{0,d\}\subset\mathbb R^4\), and let \(S\subset Q\) contain ten sites. There is a neighborhood of the labelled configuration \(S\) in \((\mathbb R^4)^{10}\) containing no acute configuration. Consequently the same holds for any subset of the vertices of \(Q\) of size at least ten. This is sharp: every such box has a nine-vertex subset admitting acute configurations arbitrarily close to it.

This is an intrinsic-dimensional local exclusion, not proof that no ten-point acute set exists in \(\mathbb R^4\). It is also distinct from asking for the largest acute subset of the cube without perturbation, as discussed in [Harangi](https://doi.org/10.1137/100808095). [Gerencsér and Harangi](https://arxiv.org/abs/1709.03411) successfully perturb a lower-dimensional cube using an extra axis; the box here already fills the ambient space. No priority claim for the local classification is made.

The companion [verify-acute-four-box-templates.py](verify-acute-four-box-templates.py) uses only integer arithmetic and prime-field elimination. It enumerates all \(\binom{16}{10}=8008\) subsets up to the full cube symmetry group (coordinate permutations and bit flips). It finds fifty orbits, covered by the following disjoint certificate types (taken in this order).

| Type | Orbits |
|---|---:|
| Contains a full-intrinsic-dimensional product with a segment | 23 |
| Contains a spanning centrally symmetric family of pairs | 6 |
| Contains a 3-by-3 product of triangles in orthogonal coordinate planes | 1 |
| Full-rank positive right-angle stress for boxes | 16 |
| Positive right-angle stress with one explicitly integrated flex | 3 |
| Full-rank midpoint comparison | 1 |

Although a nonsquare box may not have all the unit-cube symmetries, permuting coordinate roles only permutes the positive lengths, and flipping a bit corresponds to a box isometry. The arguments below apply to every choice of lengths on each representative.

## The geometric certificates

The segment product test groups distinct pairs of vertices with the same oriented difference. Their bases are constant on the coordinates in the support of that difference, hence their differences are perpendicular to the segment direction. In each recorded case the bases have affine dimension three (a nonzero minor modulo 101 is a real lower-bound certificate; the support leaves at most three dimensions). The triangle-product test finds the Cartesian product of two three-site subsets of separate two-coordinate faces, each of affine dimension two. An orthogonal product filling the ambient space has no nearby acute configuration, by the [Cartesian product rigidity proof](AcuteCartesianProductRigidity.md).

The central test groups distinct pairs with equal sums. They are disjoint within a sum group, and the test finds a group whose diagonals span dimension four. Suppose the perturbed pairs are \(m_i\pm v_i\), with midpoint diameter \(D\). Four-point acuteness implies for every \(i\ne j\)
\[
|(m_i-m_j)\cdot v_i|+|(m_i-m_j)\cdot v_j|<\|m_i-m_j\|^2;
\]
see [the four-point calculation](AcuteHypersimplexObstruction.md). For any diameter-realizing difference \(m_i-m_j\) and any \(k\), decompose it via \(m_k\), and obtain \(|(m_i-m_j)\cdot v_k|<2D^2\). If the directions span the ambient space, then \(\min_{\|u\|=1}\max_k|u\cdot v_k|=\eta>0\). The displayed bound implies \(D>\eta/2\), impossible near the equal-midpoint base. Positive diagonal scaling preserves span rank, and the widths and midpoints vary continuously.

## A local rigidity lemma for right-angle stresses

Suppose \(F_1,\ldots,F_s\) are continuously differentiable real functions in \(N\) variables, and a smooth \(k\)-dimensional embedded submanifold \(M\) through \(x_0\) satisfies \(F=0\). Suppose also that \(DF(x_0)\) has rank \(N-k\) and there are coefficients \(\lambda_i>0\) such that \(\sum_i\lambda_i DF_i(x_0)=0\). Then every nearby point satisfying \(F_i\ge0\) for every \(i\) lies in \(M\).

Indeed, if \(p_\nu\to x_0\) were counterexamples, take their closest points \(q_\nu\) on a fixed compact local manifold patch. Eventually these are in its interior and tend to \(x_0\). The normalized displacement \(u_\nu=(p_\nu-q_\nu)/\|p_\nu-q_\nu\|\) is orthogonal to the tangent there. Pass to a limit \(u\), a unit vector orthogonal to \(T_{x_0}M\). Difference quotients and \(F(q_\nu)=0\) give \(DF_i(x_0)u\ge0\). The positive stress forces every one of these to vanish. But the rank and the inclusion \(T_{x_0}M\subseteq\ker DF(x_0)\) give equality, contradiction.

Each \(F_i\) below is the inner product of the two vectors at one designated originally right angle. Thus if \(M\) is forced, some right angle remains, ruling out all acute perturbations. The checker explicitly constructs its gradient rows at the unit box, verifies that their given positive integer-weighted sum is zero, and verifies a suitable lower rank bound modulo 101. At a box with general positive side lengths, each coordinate column of the gradient is scaled by the corresponding length, because it is linear in baseline coordinate differences. Every originally right angle remains right under this scaling: its two \(0/1\) difference vectors have disjoint supports. Therefore the exact row stress and rank remain valid at arbitrary positive lengths.

## The sixteen box-rigid orbits

Use all initially right angles. They vanish on the family of translations and rotations of the same subset of orthogonal boxes with four variable side lengths. This is locally a smooth embedded family of dimension \(4+6+4=14\). Indeed a tangent motion has affine differential \(\Omega+\operatorname{diag}(\sigma)\) in the physical axes, where \(\Omega\) is skew; the vanishing of its effects on a spanning set implies that the translation and both summands are zero. Ten distinct cube vertices affinely span four dimensions: any proper affine hyperplane has at most eight cube vertices by solving for a coordinate with a nonzero coefficient. Thus the checked rank lower bound 26 is exact, since all rows vanish on the 14-dimensional family.

## The three one-flex orbits

Use binary numeric IDs \(0,\ldots,15\) in increasing lexicographic coordinate order. At each of these representatives, enlarge the box family by one parameter, preserving a particular set of 72 right angles.
- At \(S=(0,1,2,3,4,5,6,7,8,11)\), shift sites 8 and 11 by \((0,bt,0,0)\).
- At \(S=(0,1,2,3,4,7,12,13,14,15)\), shift sites 4 and 7 by \((0,bt,0,0)\).
- At \(S=(0,1,2,3,4,9,12,13,14,15)\), replace sites 4 and 9 by \((r,b,0,t)\) and \((a-r,0,0,d-t)\), with \(r^2-ar+t^2-dt=0\) on the smooth branch \(r(0)=0\); this exists because \(a>0\).

In each case also allow all the original box translations, rotations and widths. The new tangent is independent of ordinary box motions for all positive \(a,b,c,d\). In all three cases site 0 is fixed by the added motion, so any hypothetical coinciding ordinary affine velocity has zero translation. For the first orbit, the fixed eight sites span the last three coordinate directions, hence its linear part \(\Omega+\operatorname{diag}(\sigma)\) would vanish on those axes and by skew symmetry could only move points along the first axis. This cannot be the stated second-axis shift. In the other two orbits the fixed eight sites span \((a,b,0,0)\) and the last two axes. Thus the ordinary affine velocity would have a \(2\times2\) linear part in the first two axes annihilating \((a,b)\). In the second orbit the velocity of site 4, initially \((0,b,0,0)\), is a nonzero second-axis vector; this forces the off-diagonal entry of that block to be zero. A diagonal block annihilating \((a,b)\) is zero, a contradiction. In the third orbit the velocity of site 4 has nonzero fourth coordinate, also impossible. The family is therefore locally a smooth submanifold of dimension 15.

For completeness the checker selects the zero angles by polynomial identity tests, not by numerical tolerances. Each numerator is homogeneous quadratic in the four side lengths, checked on the ten inputs consisting of every coordinate unit vector and every sum of two distinct coordinate unit vectors. For the first two cases these polynomials have degree at most two in \(t\), and three distinct \(t\) values suffice. For the last case the equation is parameterized by \(t=(a\ell+d)/(1+\ell^2)\), \(r=\ell t\); at \(\ell=-d/a\) one has \(r=t=0\) and a nonzero \(t\) derivative. After multiplying each point by \(1+\ell^2\), each dot product has degree at most four in \(\ell\); five slope values suffice. For each of the resulting 72-row systems, the checker verifies a rank lower bound of 25 and strictly positive stress. Dimension 15 gives the matching rank upper bound, so the local lemma applies.

## Last orbit: midpoint comparison without a stress

In representative \((0,1,2,4,9,10,11,12,13,14)\), group unordered pairs with coincident baseline sums, and compare any two pairs within a group. For perturbed positions record the differences \(\Delta=p_i+p_j-p_k-p_l\), and project each on both of its original full pair diagonals. The map \(L\) collects the 15 vector differences, and \(B\) collects the 30 scalar projections. The checker verifies \(\operatorname{rank}_{101} B=20\) at the unit box. Meanwhile each one-coordinate scalar version of \(L\) has rank at most five: all scalar affine evaluation vectors on these ten sites lie in its kernel and span dimension five. Thus \(\operatorname{rank} L\le20\). Since \(B\) consists of linear combinations of rows of \(L\), their ranks are equal, hence their kernels are equal. Under positive coordinate scaling the columns of \(B\) scale accordingly and the rank of \(L\) is unaffected, so this remains true for every box.

Let \(D=\max\|\Delta\|\) and let \(\varepsilon\) be the maximal point displacement. If the perturbed configuration is acute, the four-point inequality gives \(D>0\), and the norm of each projection on its baseline diagonal is at most \(D^2+2\varepsilon D\). The kernel equality gives \(D\le C(D^2+2\varepsilon D)\) for a finite constant \(C\) fixed by the original box. But \(D\le4\varepsilon\), a contradiction for sufficiently small \(\varepsilon\).


## Sharpness at nine sites

Take all eight vertices of the facet with first coordinate \(a\), and the opposite corner \(p=(0,0,0,0)\). Move \(p\)'s other three coordinates by arbitrarily small positive amounts into the strict interior of their coordinate intervals, keeping its first coordinate zero. At any facet center \(y\) and for any other facet vertex \(z\), the dot product \((p-y)\cdot(z-y)\) is strictly positive: every differing facet coordinate makes a positive contribution, while the others contribute zero. Angles centered at \(p\) between facet points were already strictly acute before moving \(p\) (the first coordinate contributes \(a^2>0\) and the other contributions are nonnegative), so they remain acute for sufficiently small displacement. All mixed triangles are now acute.

The facet vertices form a nonobtuse set in their three-dimensional affine span. Perturb them into the fourth dimension one at a time using the centroid-and-height version of the [Gerencsér–Harangi construction](https://arxiv.org/abs/1709.03411): move the current site inward toward the facet centroid by \(O(t^2)\) and orthogonally by \(t\), with small enough coefficient of \(t^2\). For fixed-site middle angles the centroid term makes formerly right angles strict, and at the moved site its squared height dominates; choose successive displacements small enough to preserve all previously acute triangles, including those involving \(p\). This gives nine acute points arbitrarily close to the named nine box vertices.
