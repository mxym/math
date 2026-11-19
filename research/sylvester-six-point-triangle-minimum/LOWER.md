# Six random points in a planar convex body: the sharp triangle lower bound

For a compact convex body \(K\subset\mathbb R^2\) of positive area, let \(p_6(K)\) be the probability that six independent uniform points are all vertices of their convex hull. A parallel shake along vertical lines replaces the chord \([\ell(x),h(x)]\) by \([0,h(x)-\ell(x)]\). The shaken body is convex, since its width function \(h-\ell\) is concave.

**Theorem.** Every parallel shake weakly decreases \(p_6\). Consequently
\[
p_6(K)\ge p_6(\text{triangle})=91/900,
\]
with equality precisely for triangles. This establishes the lower extremum for six points; no result on the upper extremum or on all sample sizes is needed. The polynomial-sign portion below is an exact computer-assisted proof, not a floating-point experiment.

## 1. Slices and their curvature

It suffices by rotation to shake vertically. Order the six abscissas as \(x_0<\cdots<x_5\); ties and zero-width slices have probability zero. The marginal law of each abscissa has density \(W(x)/|K|\), \(W=h-\ell\), and is unchanged by shaking. Conditional on the ordered abscissas, the six ordinates are independent and uniform on the corresponding intervals. In this section all abscissas are fixed. Write \(w_L=W(x_0),w_R=W(x_5)\). Subtract the affine interpolant of the two lower endpoint heights; this does not affect convex position. Let \(L(x)\) denote the affine interpolant of \(w_L,w_R\) at \(x_0,x_5\).

At the six abscissas the upper and lower boundaries after this normalization are
\[
 L(x)+\sum_{i=1}^4 u_i G_i(x),\qquad -\sum_{i=1}^4 v_i G_i(x),
\quad G_i(x)=\frac{(\min(x,x_i)-x_0)(x_5-\max(x,x_i))}{x_5-x_0}.
\]
Indeed use piecewise-linear interpolation on the five intervals; at \(x_i\), \(G_i\) has left slope minus right slope equal to 1 and the other tents have no jump there. Both \(u_i,v_i\) are nonnegative by concavity of the upper envelope and convexity of the lower one. A shake replaces the pair \((u,v)\) by \((u+v,0)\), with the endpoint widths unchanged.

## 2. Conditional volume polynomial

Let \(\alpha,\beta\) be independent uniform random variables on \([0,1]\). Given the extreme ordinates \(y_0=\alpha w_L,\ y_5=\beta w_R\), subtract the line joining these points. Above it the four available heights are given by the affine interpolant of \((1-\alpha)w_L,(1-\beta)w_R\) plus \(\sum u_i G_i\); below it the positive heights are the affine interpolant of \(\alpha w_L,\beta w_R\) plus \(\sum v_iG_i\). They are nonnegative. A subset of the four middle points can appear on the upper chain, the others on the lower. The six points are in convex position exactly when the upper subsequence forms a strict concave chain and the lower one, reflected across the horizontal baseline, also forms a strict concave chain. Boundary coincidences are null.

Here is the [Marckert comb recurrence](https://arxiv.org/pdf/1511.03658), Propositions 16–17, in the notation implemented in the verifier. Its output is a volume, before division by the four common widths. For a list \(S=(a,\ldots,c)\) of indices and height data \(H\) on it, define \(B(S)=1\) if there are no interior indices. Otherwise, with \(m=|S|-2\),
\[
 B(S)=\sum_{j\in S\setminus\{a,c\}}
 \frac{H_j-[(x_c-x_j)H_a+(x_j-x_a)H_c]/(x_c-x_a)}{m}
 B(S_{\le j})B(S_{\ge j}).
\tag{1}
\]
At the two original end indices set \(H_0=H_5=0\); interior \(H_j\) are the positive heights for the chosen side. In the subproblems the values of \(H\) remain the same, so subtraction of the endpoint chord in each factor already accounts for the interiors being shifted by an affine function. To see the volume identity, for independent points uniform below a concave profile above a chord, condition on which of the \(m\) vertical height fractions relative to that chord is largest. It is uniform among the \(m\) indices; conditional on its value \(s\) and index \(j\), the other fractions are independent uniforms on \([0,s]\). The affine vertical rescaling that removes \(s\) preserves convex chains. After requiring the left/right points above the two new chords to \(j\), the resulting positive height ranges are independent; dividing by the old heights gives exactly (1) for unnormalized volumes. Zero heights follow by continuity or direct zero volume.

The desired numerator \(F(u,v,w_L,w_R)\) is the sum over the 16 splits of the product of the two comb volumes, averaged over \(\alpha,\beta\). Its denominator is the product of the widths at \(x_1,\ldots,x_4\), the same before and after shaking. Each term from (1) is homogeneous of degree four in endpoint widths and curvatures. For the linear factor with endpoints \(a,c\) and apex \(j\), its curvature coefficient before division by \(m\), at site \(i\), is zero unless \(a<i<c\), and otherwise equals
\[
\frac{(x_{\min(i,j)}-x_a)(x_c-x_{\max(i,j)})}{x_c-x_a}.
\tag{2}
\]
This follows by subtracting the interpolant from \(G_i\): the residual is the tent on \([x_a,x_c]\) with the same unit slope jump. The coefficients of the two endpoint-height variables for that side are respectively \(\mathbf1_{a=0}(x_c-x_j)/(x_c-x_a)\) and \(\mathbf1_{c=5}(x_j-x_a)/(x_c-x_a)\). This is because the original outer endpoint heights were set to zero in the comb instead of the corresponding affine values. The endpoint average is just the beta integral \(\mathbb E[\alpha^a(1-\alpha)^b]=a!b!/(a+b+1)!\), independently at each end.

## 3. Exact finite coefficient check

The following computational lemma is established by the supplied complete program **lower_exact.py**. It uses arbitrary-precision integer arithmetic including the interpolation (NumPy object arrays only).

**Lemma.** Write \(g_i=x_i-x_{i-1}>0\), \(1\le i\le5\), and
\[
D=(x_5-x_0)\!\prod_{0\le a<c\le5,\ c-a\ge2}(x_c-x_a).
\]
After multiplying \(F(u,v,w_L,w_R)-F(u+v,0,w_L,w_R)\) by \(4!(5!)^2D\), every monomial coefficient in the ten shape variables is a polynomial with nonnegative integer coefficients in the five gaps. Each shape monomial containing both an upper and a lower curvature variable has a nonzero coefficient polynomial.

Here are the bounds making this a finite verification. Each pair of endpoints \(a,c\) in a comb recursion occurs at most once per tree. A non-global pair cannot occur in both trees, as it has at least one interior **endpoint** that would belong to both sides of the split. Thus \(D\), which repeats only the global pair, clears every span denominator, including spans with skipped sample indices. The product of the subtree sizes of any tree with \(m\) vertices divides \(m!\), by the root recursion and the integrality of the binomial coefficients. For both trees the two factorials divide \(4!\) in product. At each outer endpoint the beta denominator divides \(5!\). Thus the displayed multiplier clears all remaining denominators. For a monomial with \(e\) curvature variables counted with multiplicity, its scaled coefficient is homogeneous of degree \(11+e\le15\) in the gaps: \(D\) has degree 11 and each curvature factor (2) has net degree 1 whereas the endpoint factors have degree 0. Therefore it suffices to set \(g_5=1\); homogenization later introduces only one power of \(g_5\) per monomial and preserves signs.

The verifier expands (1)–(2) at each node \(g_i=1+t_i\) for \(1\le i\le4,\ t_i\ge0,\ \sum_i t_i\le15\), \(g_5=1\). It expands the shaken polynomial by assigning each curvature occurrence to either label in \(u_i+v_i\), including all multiplicities, and subtracts. There are \(\binom{19}{4}=3876\) nodes. To recover monomial coefficients on this unisolvent grid, take successive forward differences of order \(j\) along each coordinate divided by \(j!\). This gives the mixed Newton coefficients in the basis \(\prod_i\prod_{q=1}^{j_i}(g_i-q)\); expanding each factor then gives ordinary powers. The first difference pass uses only componentwise lower nodes, and the basis conversion stays in the lower set \(\sum_i j_i\le15\). All divisions and shape term counts are explicitly checked. There are 715 shape monomials of total degree four; the 247 without both colors cancel at every node. Across the remaining 468 polynomials, the full count is **253751 positive coefficients, 1560217 zero, none negative**. The largest coefficient is 1402444800. Every one of the 468 polynomials is nonzero at all gaps equal to one. Since all gaps are positive, each such coefficient is strictly positive for every abscissa sequence. This proves the lemma and the conditional shaking inequality. In particular the gap is strict whenever some \(u_i>0\) and some \(v_j>0\), as the monomial \(u_i^2 v_j^2\) then contributes. Integrating the conditional inequality proves shaking monotonicity for every planar convex body.

## 4. Global minimum and equality

For a convex polygon presented by its extreme vertices, if there are more than three, take any diagonal joining two nonadjacent vertices and shake parallel to that diagonal. In coordinates where the chord lines are vertical, both endpoints of the diagonal have the same **interior** abscissa; otherwise they would both be in the same supporting edge. The new lower graph is flat; its upper width graph can break only at old vertex abscissas and has at most one vertex at each interior abscissa. At the two extreme abscissas, the number of vertices (one for a point, two for an edge) is unchanged. Thus there is at least one fewer vertex and no loss of area. Iteration terminates in a nondegenerate triangle. All triangles are affinely equivalent. For arbitrary \(K\), approximate it by inscribed polygons of areas tending to its area. Their uniform laws converge in total variation to its uniform law, hence so do their sixfold products. The triangle lower bound passes to the limit.

If \(K\) is not a triangle, choose four distinct extreme points in cyclic order and take the chord joining two opposite points of that quadrilateral. Their segment does not lie in a common supporting line, since the other two points are on opposite sides. In coordinates along the shake just used, its two endpoints are upper and lower boundary extremes at a common interior abscissa \(s\). Choose any interior abscissas \(x_0<s<x_5\). The upper boundary at \(s\) is strictly above the chord of its heights at \(x_0,x_5\), and the lower one strictly below its analogous chord, because each endpoint at \(s\) is extreme. These strict comparisons persist for six ordered abscissas in open neighborhoods with one middle abscissa sufficiently close to \(s\). Their joint density is positive there, and for all such choices both curvature lists have a positive entry. The strict conditional gap thus has positive integral. Hence \(p_6(K)>p_6(K^{\rm shake})\ge p_6(\text{triangle})\). Finally, the numerical value follows from Valtr's known triangle formula \(p_n=2^n(3n-3)!/((n-1)!^3(2n)!)\), not from a new evaluation of that probability.
