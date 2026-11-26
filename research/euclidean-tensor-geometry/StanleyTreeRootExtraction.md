# Rooting a tree from modular information in its chromatic symmetric function

**Yongxian Zhang.** AI-assisted proof development; no external peer review claimed.

Stanley's conjecture that the chromatic symmetric function distinguishes all trees remains open; see [Orellana–Tomba](https://arxiv.org/abs/2611.18940). We give a reconstruction criterion allowing repeated weights at internal vertices of the core, unlike the multiplicity-isolation criterion in [arXiv:2608.18179](https://arxiv.org/abs/2608.18179). The new step is to recover rooted pieces and their adjacency from two layers of the unrooted cut polynomial. Branch-factor reconstruction of rooted trees is due to [Aliste-Prieto, de Mier and Zamora](https://arxiv.org/abs/2002.08186); below is its positive-weight version.

The leaf-hub and distance-two arguments in Sections 4–5 give two further criteria. In particular, the leaf-hub criterion does not assume properness.

## 1. Cut data and a rooted factorization

A tree \(T\) on \(N\) vertices determines the unsigned cut polynomial
\[
U(T)=\sum_{F\subseteq E(T)}\prod_{C\in\operatorname{comp}(T-F)}x_{|C|}.
\]
It is read from \(X_T\) in the power-sum basis by changing the coefficient sign of a monomial with \(b\) parts by \((-1)^{N-b}\). For weighted trees replace sizes by sums of positive integer vertex weights. A tree is proper if each nonleaf is adjacent to a leaf. For proper trees with \(N\ge3\), setting \(x_1=0\) in \(U(T)\) forces every pendant edge to stay. It gives the full weighted cut polynomial of the core \(W\) induced by nonleaves, each weight equal to one plus its number of original pendant leaf neighbors. The unique maximum ordinary degree monomial gives the weight multiset of \(W\), and the weighted core recovers the original proper tree. Properness itself is recognized among trees on \(N\ge3\) by there being no 1 in the leading star-basis leaf-component partition: a part 1 is exactly an isolated nonleaf when all internal edges are deleted. See [Gonzalez, Orellana and Tomba](https://arxiv.org/abs/2507.15986) for the leading-partition theorem.

For a positively weighted tree \(B\) rooted at \(r\), write \(R(B,r;z,x)\) for its unsigned cut polynomial with the root-component factor replaced by \(z^{\text{weight}}\). This recovers the rooted weighted tree. Indeed its lowest \(z\) exponent equals the root weight \(w\), and deleting the root gives branches \(B_i\), rooted at their former neighbors \(r_i\). Independent cuts of those branches and their attachment edges give
\[
z^{-w}R(B,r;z,x)=\prod_i\bigl[U(B_i;x)+R(B_i,r_i;z,x)\bigr].
\]
For branch total weight \(a_i\), the factor is monic linear in \(x_{a_i}\): only the uncut branch contributes that variable, and the root-marked part has no such variable. Thus it is irreducible over the integer polynomial ring. Unique factorization recovers a multiset of factors (with positive normalization); their positive-\(z\) terms are the child rooted cut polynomials. Recurse. In particular every such rooted polynomial is monic in \(z\), its degree being total branch weight.

A single distinguished vertex whose containing components can be recognized from their weights can therefore root the whole core: replace the recognized factor by \(z^{\text{weight}}\) in each monomial. For example, if all other core weights are divisible by \(d\ge2\) and the distinguished weight is not, this recognition is by residue. Another sufficient condition is that the distinguished weight exceed the sum of all others.

## 2. Several indistinguishable residues

**Theorem.** Let \(T\) be proper. Suppose that for some \(d>h\ge2\), precisely \(h\) weights of \(W\) are \(1\bmod d\) and all others are \(0\bmod d\). Suppose the marked vertices induce a connected subtree \(J\). Delete its edges; let \(B_i\) be the component containing mark \(i\), rooted at that mark. Let \(f_i(Y)=\sum_{s\ge1}[z^s]R(B_i,i;z,x)Y_s\), considered as linear forms over \(\mathbb Q(x)\).

If \(h=2\), then \(X_T\) determines \(T\) among all trees. For \(h\ge3\) this also holds if the \(f_i\) are pairwise nonproportional and no \(f_k\) belongs to the span of two other \(f_i,f_j\). In particular, distinct total weights of \(B_i\) suffice (the forms have distinct largest index and coefficient 1).

**Proof.** In each core cut component the weight residue is exactly its number of marks, since \(d>h\). Both \(d\) and the number of marks may be chosen from the known weight multiset. The least number of edges that must stay to keep all marks together is the number of edges of their Steiner subtree, the union of the unique paths between them. Thus, if \(W\) has \(k\) vertices, the largest ordinary monomial degree among terms with a residue-\(h\) component equals \(k-\lvert E(\operatorname{Steiner}(J))\rvert\). It equals \(k-h+1\) exactly when the marks induce a connected subtree. This detects the connectivity hypothesis even for another tree with the same invariant.

Now use two disjoint collections of monomials of \(U(W)\).

- In the layer with \(h\) residue-1 components, every edge of \(J\) is cut. Remaining cuts are arbitrary in the \(B_i\). Replace a variable \(x_s\) of residue 1 by \(Y_s\), retaining residue-0 variables as \(x_s\). The result is \(P(Y)=\prod_i f_i(Y)\). Factor \(P\) over \(\mathbb Q(x)\) and normalize each factor so its largest-index coefficient is 1. This recovers the rooted polynomials and therefore the rooted weighted \(B_i\). For \(h=2\) they can simply be joined by their roots, even if identical.
- In the layer with one residue-2 component and \(h-2\) residue-1 components, exactly one edge of \(J\) stays. Replace the doubly marked factor by 1 and the singly marked factors by \(Y_s\) as before. If the surviving edge joins \(i,j\), then the two marked root components fuse, while the unmarked components do not change. Its contribution is
\[
f_i(\mathbf1) f_j(\mathbf1)\prod_{k\notin\{i,j\}}f_k(Y).
\]
The scalar \(f_i(\mathbf1) f_j(\mathbf1)\) is nonzero, since the rooted cut polynomials have positive coefficients.

To detect edge \(\{i,j\}\), restrict this second polynomial to the linear subspace \(f_i=f_j=0\). All other potential pair contributions vanish. The product over \(k\notin\{i,j\}\) is nonzero on that subspace: no remaining factor vanishes identically there, by the span assumption, and the subspace has an integral-domain coordinate ring over \(\mathbb Q(x)\). Thus the restriction is nonzero exactly for an edge. This identifies the entire marked subtree and how to glue the recovered pieces. All hypotheses used are detected by the cut data, the final linear-form condition by the recovered factors themselves. ∎

For a diameter-six example not covered by multiplicity isolation, take a core with center \(r\), neighbors \(a,b,c\), one further leaf attached to each of \(a,b\), and no other vertices. Give \(r,a\) weight \(d+1\) and every other core vertex weight \(d\), for any \(d\ge3\). The two equal marked weights occur on distinct nonleaf core vertices. The theorem still recovers the expanded tree. It also yields families of unbounded diameter, with repetitions permitted in every branch. The proof does not handle disconnected indistinguishable marks or all equal core weights in general.


## 3. The core specialization alone is insufficient in general

For any \(d\ge4\), the two weighted paths
\[
(d+1,d,d+1,2d+1,d),\qquad (d+1,2d+1,d,d+1,d)
\]
are not reversals of one another, but have identical weighted cut polynomials. Indeed let \(\beta=(d+1,d)\); the sequences are \((1,2)\circ\beta\) and \((2,1)\circ\beta\) in the composition product of [Billera–Thomas–van Willigenburg](https://arxiv.org/abs/math/0405434). Here \(\beta^{\odot 2}=(d+1,2d+1,d)\) merges the boundary parts of two copies; the sequences concatenate \(\beta\) and \(\beta^{\odot2}\) in opposite orders. Their theorem identifies the multisets of partition sizes of all coarsenings, exactly the polynomials of the paths. The equal-residue marker pattern uses three disconnected marks in both cases. Exact enumeration also checks the identity for \(4\le d<100\).

This is a limitation of \(x_1=0\), **not** a pair of trees with identical full chromatic symmetric functions. In fact the expansions here are proper caterpillars and their full invariants distinguish them by [Aliste-Prieto–Zamora](https://www.sciencedirect.com/science/article/pii/S0012365X13004433) (see their proper-caterpillar theorem). Independently, direct exact enumeration of the two layer identities in Section 2 agreed on 24 small weighted core examples, including both distinct and repeated arm weights. Neither enumeration is a premise of the proof.

## 4. A leaf-hub coordinate change, including nonproper trees

For any tree with at least three vertices the leading star-basis partition determines the multiset of orders of the components obtained by deleting internal edges; thus L, the maximum number of pendant leaf neighbors of any one vertex, is determined. Denote by c a vertex attaining L, remove its L leaf neighbors, and call the remaining rooted tree H, with m=n−L and R(H;z)=Σ_{k=1}^m z^k f_k(x). Independent retention of i of the L removed edges gives the identity
 U(T)=Σ_{k=1}^m f_k(x) Σ_{i=0}^L binom(L,i) x_1^{L-i} x_{k+i}.
If every component of T−c has order at most L, then every component other than the root in every forest of H has order at most L. Consequently no f_j contains x-index >L. Reading the linear coefficient of x_{L+k}, descending k=m through 1, recovers f_k by subtracting the terms with j>k already known. Terms with j<k cannot reach index L+k; the j=k term requires all L pendant edges selected, hence coefficient 1. No properness used. This gives injectivity among trees satisfying the component-size promise for some maximum-leaf-count vertex c, even if the promise is not intrinsically recognized in general.

Stronger outside-class guarantee: whenever L≥n/2, every rival tree with same CSF has the same L by the leading partition and automatically each component of T−c has size ≤ n−L−1≤L. Thus each such tree is distinguished among *all* trees, not just the subclass. Nonproper diameter-six examples follow by taking a center with two length-three paths and attaching enough extra leaves to it. For instance take seven extra leaves, then n=14, the center's L=7; the interior vertices at distance one have no leaf neighbors, so proper-tree reconstructions do not apply. Without any leaf bound, the same descending inversion recovers f_k for every L+k>m (and in fact L+k>m−1): all f_j x-indices at most m−1, so this is an always-determined partial rooted profile (from any c attaining L).



Define \(H_j=\sum_{i=0}^{L}\binom L i x_1^{L-i}x_{j+i}\). With weight \(wt(x_s)=s\), \(H_j\) is homogeneous of weight \(L+j\) and is \(x_{L+j}\) plus lower-index variables. Thus \(x_1,\ldots,x_L,H_1,\ldots,H_m\) are triangular polynomial coordinates. In the inverse substitution each \(x_{L+j}\) is \(H_j\) plus lower-index \(H\)'s and low variables, and its coefficients in this affine-linear relation are polynomials in low variables. Before substituting, \(U=\sum_j f_j(x)H_j\) has positive coefficients when the \(H_j\) are formal independent variables. If any \(f_j\) uses a high variable \(x_{>L}\), take maximal total high degree (counting both \(H_j\) and \(x_{>L}\)); at that degree take largest lex exponent with high variables ordered by descending index and treating \(x_{L+i}\) as index \(i\). On substitution that leading exponent is preserved, its coefficient remains a nonzero sum with positive coefficients, and others at its degree can only decrease lex exponent. Nothing of lower degree produces that exponent. Hence the transformed \(U\) has \(H\)-degree at least two. Conversely if all \(f_j\) use only \(x_{\le L}\), \(U\) is linear in \(H\). Existence of a high variable in any \(f_j\) is exactly existence of a component of \(T-c\) of size \(>L\): cut off and retain that branch to obtain a corresponding forest, and any unrooted forest component belongs to one branch. Linearity in \(H\) detects the component-size condition solely from the CSF, with \(c\) any vertex attaining the known \(L\); coefficient of each \(H_j\) reconstructs \(f_j\). Thus the full bounded-branch family distinguishes among all trees, not just the subclass.

Numerical threshold regardless of component sizes: if \(n<2L+3\), a monomial of weighted degree \(n\) cannot contain two distinct \(H\)-indices (weights \(L+1\) and \(L+2\) already sum to \(2L+3\)). Every monomial of \(f_j(x(H))H_j\) contains \(H_j\), so its unique \(H\)-index recovers its source summand even if this variable is powered. Dividing by \(H_j\) recovers \(f_j\). Thus \(L\ge\lceil(n-2)/2\rceil\) suffices. At \(n\ge2L+3\), this unrestricted linear extraction has a homogeneous kernel \(f_1=H_2 x_1^{n-2L-3}\), \(f_2=-H_1 x_1^{n-2L-3}\), others zero; this does not give rooted tree invariant collisions.


For a nonproper diameter-six family, take a center with two length-three arms and attach at least three leaves directly to it. All components off the center have at most three vertices, so the first criterion applies even when the center has fewer than half the vertices as leaf neighbors. Exact enumeration on all 1,440 labeled trees of orders 3 through 6 checked the class-detection identity and the inversion on all 660 instances satisfying either sufficient condition.

## 5. Two identical modular tags at distance two

Suppose exactly two core weights have residue 1 modulo d≥3 and all others residue 0. They are marked vertices; in any core forest the components containing both, one, or no marks have respective residues 2,1,0. The maximum number of components in the together sector is k−dist where k is number of core vertices, because exactly their path must be retained for the shallowest together forest. Hence distance two is detectable. Let a−b−c be this path. Deleting its edges produces rooted arms with polynomials L,M,R at a,b,c; denote their total weights l,m,r, and middle unrooted polynomial U_M. All weights positive. The together sector, replacing its residue-2 variable with z^{weight}, is C(z)=L(z)M(z)R(z). In the separate sector replace residue-1 variables with z^{weight}, y^{weight} averaged over the two assignments (identical weights need no extra counting): this gives 
 A(z,y)=sym[L(z)R(y)(M(z)+M(y)+U_M)].
This follows by considering respectively which of the two path edges are deleted.

The highest y exponent in A is m+max(l,r). At x_i=0 its coefficient is (1/2)z^{min(l,r)} if l≠r, or z^l if l=r, so the inequality promise is detectable (x_i refer only to ordinary unmarked component variables). Orient l<r. The full coefficient of this top y power is exactly L(z)/2: attaining this size requires cutting a−b, retaining b−c and all internal edges in the middle and large endpoint arms, and leaves the small endpoint arm unconstrained. Thus L is known, and P=C/L=MR. Subtract sym[L(z)P(y)] from A. Linearize z^i y^j→Y_iY_j to obtain the product of the two linearizations of R and D=L(M+U_M). Factoring over Q(x) yields these as two unordered factors, each canonically normalized by coefficient 1 at its highest index. They have no assignment ambiguity: if swapping the factors gave R'=D and R=L(M'+U_{M'}) with P=M'R', then P=MR implies M U_{M'}=M' U_M. Comparing z-degrees and monic leading coefficients gives U_M=U_{M'} and M=M', thus R=R'. Compute M=P/R under the (unique, or identical) valid assignment; check D/L=M+U_M. Each arm is then reconstructed by rooted factorization, and attaching the path gives the tree. All tags, distance and endpoint inequality are CSF-detectable from the same invariant, so same-CSF rivals are covered. Equal endpoint-side sizes are handled next.

A tiny diameter-six weighted core example: path a−b−c with root weights 4,3,4, and attach at a one terminal weight 3 and at c two terminal weight 3. Take d=3. Endpoint arm masses are 7 and 10, and middle mass is 3. The expanded proper tree has diameter six and repeated nonleaf core weights, with its two marks at distance two.


### Equal endpoint weights

The equal-endpoint case uses a leading coefficient in the variable for the total middle mass. For equal end totals u, the top separated y exponent is \(u+m\) and its coefficient is \((L(z)+R(z))/2\), by the same extreme-cut argument (both endpoint cuts now attain the maximum). Thus \(S=L+R\) and \(m\) are known. Let \(v=x_m\) and \(h=\deg_v C\). The rooted middle \(M\) is independent of \(v\) because its positive-weight root always occupies a component; \(U_M=v+U_<\) with \(U_<\) independent of \(v\). Hence \(h=\deg_v L+\deg_v R\). Write \(L_*,R_*\) for the leading coefficients of \(L,R\) in \(v\). Then
\[
 [v^{h+1}]A(z,y)=\operatorname{sym}(L_*(z)R_*(y)),\qquad [v^h]C(z)=L_*(z)M(z)R_*(z).
\]
The first equality comes only from the full connected middle component in \(U_M\); all other terms have degree at most \(h\). Setting \(y=z\) and dividing recovers \(M\), since the product of nonzero polynomials is nonzero. Compute \(LR=C/M\), and recover unordered \(L,R\) as the two roots of \(t^2-St+LR\) over the field \(\mathbb Q(x_1,x_2,\ldots,z)\). Unordered endpoints are sufficient at distance two. Together with the unequal cases, this proves all proper trees having exactly two modulo-\(d\) residue-1 core weights, all others residue-0, and marker distance two, distinguished even among all ordinary trees. The class is CSF recognizable via properness/weights and maximal together length, and nonadjacent markers are genuinely covered.

## 6. General bridge inversion: recognizable paths and stars

Let a bridge of \(T\) split it into rooted trees \((P,a)\) and \((B,b)\), the roots being its endpoints. Write \(p=|P|\), \(m=|B|\), and
\[
R(P,a;z)=\sum_{i=1}^p A_i(x)z^i,\qquad
R(B,b;z)=\sum_{j=1}^m F_j(x)z^j.
\]
For \(1\le j\le m\) define
\[
G_j=x_j U(P)+\sum_{i=1}^p A_i(x)x_{i+j}.
\]
Deleting the bridge gives the first term, and retaining it joins the two root components, giving the second. Thus \(U(T)=\sum_j F_j(x)G_j\). Each \(A_i\) contains only low variables \(x_{\le p}\), and \(A_p=1\). Consequently \(x_1,\ldots,x_p,G_1,\ldots,G_m\) are triangular coordinates: \(G_j=x_{p+j}\) plus a polynomial in lower-index variables, affine-linear in the high variables \(x_{>p}\) over the low-variable ring. The inverse is likewise affine-linear and triangular. These substitutions preserve weights \(wt(x_i)=i,\ wt(G_j)=p+j\). The algebraic identity also works for positively integer-weighted trees by replacing sizes by masses.

**Exact degree and inversion.** In the new coordinates, the total degree of \(U(T)\) in the \(G\)'s is \(1+\nu\), where \(\nu\) is the maximum number of pairwise disjoint connected vertex sets of size \(>p\) in \(B-b\). Indeed every unmarked component of a cut contributes an old high variable exactly when it has that size, and any such collection of disjoint connected sets can be simultaneously cut off as components. Before substituting, \(\sum_j F_j(x)G_j\) has nonnegative coefficients when the \(G_j\) are treated as independent symbols. At maximum total high degree select the lexicographically largest high-index profile, taking \(x_{p+i}\) and \(G_i\) to have the same index. The inverse substitution has leading term \(G_i\) with coefficient 1 for each \(x_{p+i}\); its other terms lower degree or lower the lexicographic profile at that degree. Thus the selected positive coefficient survives and no higher degree can appear.

In particular, \(U(T)\) is linear in the \(G\)'s exactly when every branch of \(B-b\) has size at most \(p\). In that case its coefficient of \(G_j\) is \(F_j\). This recovers the rooted \(B\) by Section 1 and then \(T\) by joining \(P\) back. It suffices that the same rooted piece \(P\) is known to exist in every tree with the given \(X_T\); its location need not be known or unique. The degree test then establishes the branch promise in every rival. Even without that promise, if \(p+m\le 2p+2\), no monomial of weight \(p+m\) can contain two distinct \(G\) indices. Every term of \(F_j(x(G))G_j\) contains \(G_j\), so its unique index identifies the source summand; dividing by \(G_j\) inverts the transform.

**Recognizable pieces.** The twig-length multiset is recoverable by [Crew, Theorem 3](https://arxiv.org/pdf/2106.04417), so a twig of edge length at least \(p\) certifies a pendant \(p\)-vertex path rooted at its endpoint toward the bridge. An end-\(p\) subpath and the next edge give the requisite split. For \(p\ge2\), a center-rooted pendant \(p\)-vertex star exists precisely when some degree-\(p\) vertex has \(p-1\) leaf neighbors. This is recognized by the leaf-adjacency sequence of [Liu–Tang, Theorems 3.4 and 4.9](https://arxiv.org/html/2411.18972v2), using the recovery of the generalized degree sequence from \(X_T\) in [Aliste-Prieto–Martin–Wagner–Zamora](https://arxiv.org/abs/2402.10333). These recognition results are prior work; the bridge inversion is the additional step.

For \(p\ge4\) take a center joined to two \(p\)-vertex endpoint-rooted paths and at least two more \(p\)-vertex path arms, each rooted at the internal vertex separating subpaths of lengths \(1\) and \(p-2\). The diameter is \(2p\), every vertex has at most one leaf neighbor, and the center and the internally rooted arms supply at least three branching vertices. A terminal path arm is recognizable and every other arm has size \(p\), so the new criterion reconstructs the tree. This family is nonproper and fails the leaf-hub criterion of Section 4. A diameter-six example uses two \(3\)-vertex end-rooted arms and at least two \(3\)-vertex middle-rooted arms. The central vertex has no pendant leaf neighbors, and each maximum-leaf hub is a middle-rooted arm whose remaining branch is larger than 2. The new criterion applies at the center via a recognized pendant path.

**The maximum-leaf threshold improves to \(n\le2L+4\).** Use the notation of Section 4, and choose a hub realizing the maximum number \(L\) of leaf neighbors. Write \(d\) for its other neighbors; the pair \((L+d,L)\) is CSF-detectable by the leaf-adjacency sequence. If \(d=0\), the tree is a star. If \(d=1\), the hub and its leaves form a recognized pendant star with \(p=L+1\), so the distinct-index rule applies for \(n\le2L+4\). If \(d\ge2\), each of the \(d\) branches after removing the hub and its leaves has at least two vertices. The largest has at most \(n-L-2d+1\le L+1\) vertices. Every \(f_j\) of Section 4 thus uses only \(x_{\le L+1}\); in the transformed coordinates its only possible high variable is \(H_1\). Each resulting monomial of \(f_jH_j\) is uniquely routed to its \(H\) index greater than 1 if present, and to \(H_1\) otherwise. Dividing by the routed factor recovers the \(f_j\). This uses a tree support constraint, so it is compatible with the earlier non-injectivity for arbitrary weighted-homogeneous coefficients.

Exact integer checks of the bridge formulas, degree test and inversions were also run on 14,089 oriented bridge splits, with all 10,895 eligible inversions agreeing. The proof does not depend on those checks. Neither this nor the other criteria determine arbitrary diameter-six trees.
