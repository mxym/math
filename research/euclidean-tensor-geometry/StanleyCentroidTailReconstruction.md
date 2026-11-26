# Reconstructing trees from the large-component part of their chromatic symmetric function

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

For each fixed \(B\), all sufficiently large trees whose centroid branches have at most \(B\) vertices are distinguished by their ordinary chromatic symmetric function, even among all trees. A sharper bound depends on how many different rooted branch types actually occur. The argument does not require a recognizable pendant piece, distinct internal weights, or properness. General Stanley tree reconstruction, and the unrestricted diameter-six case, remain open.

## 1. Recovering a segment of the centroid-rooted invariant

Let \(T\) have \(n\) vertices. Its unsigned cut polynomial \(U(T)\) is the sum of the products of \(x_{|C|}\) over components of all spanning forests. It is determined by \(X_T\) by the power-sum expansion. A centroid is a vertex \(c\) such that all components of \(T-c\) have at most \(n/2\) vertices. Let \(B\) be the maximum such component size. This integer is intrinsic to \(U(T)\): orient edges away from any centroid. For each edge its away-side component lies in one centroid branch and has at most \(n/2\) vertices, and attachment edges attain the largest branch size. Thus \(B\) is precisely the largest smaller part among the two-component monomials of \(U(T)\). See [Aliste-Prieto–de Mier–Zamora, §4](https://arxiv.org/pdf/1509.09210) for centroid edge labels. When \(B<n/2\), the centroid is unique. [Orellana–Scott, Theorem 5.8](https://arxiv.org/html/1308.6005#S5) reconstructs single-centroid trees from *edge-labeled* two-cut data, not from the unlabelled ordinary \(X_T\).

Write \(R(T,c;z)\) for the rooted cut polynomial, replacing the factor of the component containing \(c\) by \(z^{|C|}\). In any cut, each component not containing \(c\) lies in a centroid branch and has size at most \(B\). Hence every factor \(x_j\) with \(j>B\) is unique in its monomial and necessarily the root component. Replacing such a factor by \(z^j\) in just these terms recovers \(R(T,c;z)\) for exponents \(j>B\). Put \(t=1/z\), \(L=n-B-1\). The normalized rooted series \(P_T(t)=z^{-n}R(T,c;z)\) is consequently known modulo \(t^{L+1}\). The same tail and branch bound hold for every tree with the same ordinary \(X_T\).

For an isomorphism type \(A\) of a rooted branch of order \(s\), set
\[
Q_A(t)=t^s\bigl(U(A)+R(A;1/t)\bigr).
\]
Then \(Q_A\) has constant term 1, degree \(s\) in \(t\), and depends on \(x_s\) exactly by the summand \(t^s x_s\). This last assertion holds because the whole branch is the only unmarked component of order \(s\), appearing once in \(U(A)\). Attachment-edge factorization gives
\[
P_T(t)=\prod_A Q_A(t)^{m_A},
\]
with \(m_A\) the multiplicity of \(A\) at the centroid. The branch-factor reconstruction is the result of [Aliste-Prieto–de Mier–Zamora](https://arxiv.org/abs/2002.08186): \(U(A)+R(A;z)\) is monic linear in \(x_s\), and its positive-\(z\) terms reconstruct the rooted branch. In particular the \(Q_A\) of a fixed size are distinct.

## 2. Two quantitative sufficient conditions

**Theorem.** Suppose \(B<n/2\). Let \(r_s\) be the number of distinct rooted branch types of order \(s\) actually present at the centroid. The ordinary \(X_T\) determines \(T\) among all trees if
\[
L=n-B-1\ \ge\ 4\max_{1\le s\le B} s r_s.
\]
For a separate uniform bound, let \(a_s\) count all rooted tree types of order \(s\), and \(D_B=\sum_{s=1}^B s a_s\). Then \(L\ge D_B\) also suffices.

For the first bound, compare \(T\) with any rival of the same \(X_T\) and descend through \(s=B,B-1,\ldots,1\), dividing out the matched larger factors (they are power-series units). Smaller factors are independent of \(x_s\). Specialize \(x_1,\dots,x_{s-1}\) to fixed rational values that make all polynomials
\[
P_A(t)=Q_A(t)|_{x_s=0}
\]
of order-\(s\) rooted types distinct. This is possible: their pairwise differences are nonzero polynomials before specialization, and there are finitely many types. All have constant term 1 and degree at most \(s\). Write \(u_A=1/P_A\). The \(x_s^k\) coefficient of the formal logarithm of the remaining product, for \(k\ge1\), is
\[
(-1)^{k+1}t^{sk}\sum_A m_A u_A^k/k ,
\]
where the sum is over order-\(s\) types. Therefore these moments agree through order \(L-sk\) whenever \(sk\le L\). The zeroth moment also agrees: it counts order-\(s\) branches, given by the leading \(t^s x_s\) term of the logarithm. If \(r_s=0\), the same count shows absence in the rival (here \(L\ge s\), since \(L\ge4B\) from the order-\(B\) type).

Fix the \(r=r_s>0\) types \(A_1,\ldots,A_r\) in the target. Use the polynomial in \(u\) with power-series coefficients
\[
W(u)=\prod_{i=1}^r (u-u_{A_i})^2.
\]
The target's weighted sum of \(W(u_A)\) is zero. Its rival must have equal sum modulo \(t^{L-2rs+1}\), by the moment agreements, since the coefficients of \(W\) have no negative powers. If the rival contains a type not on the list, every nonzero product \(W(u_A)\) starts with a strictly positive real coefficient and valuation at most \(2rs\): each difference of inverses has the same valuation as the difference of their degree-\(\le s\) denominators. Such terms cannot cancel one another at their first nonzero valuation. The degree bound \(L\ge4rs\) is therefore enough to exclude every extra type. Now omit one factor from \(W\) to annihilate all known types but one. The same truncated-moment comparison shows that this one's multiplicity is equal: its surviving product has valuation at most \(2(r-1)s\) and nonzero leading coefficient. This finishes the induction. The branch multiset reconstructs the whole tree by attaching its roots to the centroid.

For the uniform bound, if \(P_T\) and the rival normalized series agree through order \(L\), the difference of their logarithmic derivatives is \(O(t^L)\). It is a rational function whose denominator can be taken as \(\prod_A Q_A\) over all branch types of size at most \(B\), so it has degree at most \(D_B\) and constant term 1. The numerator has degree at most \(D_B-1\) because each log derivative is a sum of proper fractions \(m_A Q'_A/Q_A\). If \(L\ge D_B\), the numerator vanishes. The normalized series have constant term 1, hence are equal in characteristic zero. The rooted branch-factor theorem recovers the tree.

## 3. A diameter-six application with repeated branch sizes

For a radius-three center, each branch is a rooted height-at-most-two tree. At order \(s\) it is specified by the partition of \(s-1\) into sizes of the stars hanging from its root. In particular \(r_s\) can be far smaller than the total number of rooted trees. The moment proof does not assume the rival has height at most two at its centroid.

Here is an explicit family not requiring a large leaf hub or a recognizable pendant anchor as in [the bridge theorem](./StanleyTreeRootExtraction.md#6-general-bridge-inversion-recognizable-paths-and-stars). Use branches of order 16, each with three child stars (their orders include their centers). Take one copy of the branch \((3,5,7)\) and two copies of \((4,5,6)\), and repeat this three-branch package \(k\) times at a common center. For \(k\ge3\), \(L=48k-16\ge128=4\cdot16\cdot2\); the theorem reconstructs this tree from \(X_T\). It is nonproper, diameter six, and has terminal twigs of edge length one. All vertices with pendant leaf neighbors lie far from a centroid and have a branch much larger than their leaf count.

For comparison the three competing order-16 branches \((3,6,6),(4,4,7),(5,5,5)\), repeated \(k\) times, have the same multiset of child star sizes. This produces the same degree data, leaf adjacency data, edge endpoint degree counts and unordered one-edge split data, but different branch arrangement and a nonisomorphic tree. The new reconstruction uses the ordinary chromatic symmetric function beyond these local summaries; it does not claim uniqueness from those summaries.

## 4. Linear thresholds from the first inverse moment

At each descending size \(s\), once larger factors are removed, let \(P_A(t)=Q_A(t)|_{x_s=0}\) for size-\(s\) branches. Section 2 shows that the ordinary invariant determines the first inverse moment \(\sum_A m_A/P_A(t)\) through order \(L-s\), since it is \(t^{-s}\) times the \(x_s\) coefficient of the logarithm of the remaining product. Two specializations extract enough information from this moment alone.

### Height at most three at a high-degree centroid

**Theorem.** If \(n\ge3B\), the maximum degree \(d\) is greater than \(B\), and the centroid has eccentricity at most three, the tree is distinguished among all trees by \(X_T\). The degree condition is automatic if \(n\ge B^2+2\). Without it, the reconstruction still distinguishes within the class with centroid eccentricity at most three.

First certify the height in any rival. Every vertex other than the centroid \(c\) has degree at most \(B\): its branch has at most \(B\) vertices and only its attachment edge can lead outside. Thus \(d>B\) identifies \(c\) by degree, and the edge endpoint degree counts of [Liu–Tang, Theorem 4.4](https://arxiv.org/html/2411.18972v2#S4.SS2) give \(H=\sum_{v\sim c}(\deg(v)-1)\). These counts are recoverable from \(X_T\) by [Aliste-Prieto–Martin–Wagner–Zamora](https://arxiv.org/abs/2402.10333) and Liu–Tang. Let \(k_e\) be each smaller cut side, and \(E=\sum_e(k_e-1)\). Since \(B<n/2\), the \(k_e\) are exactly the sizes of the sides away from \(c\). Edges with away endpoints at depth one contribute \(n-1-d\) to \(E\). Depth-two sides partition the vertices of depth at least two and occur \(H\) times, contributing \(n-1-d-H\). Therefore
\[
E-2(n-1-d)+H=\sum_{e\text{ with away endpoint at depth }\ge3}(k_e-1).
\]
This nonnegative sum vanishes precisely when every vertex has depth at most three: a depth-four vertex forces its depth-three ancestor to have a nontrivial away side. The left side is the same for every rival. Further, \(n-1\le dB\) at the centroid proves the automatic threshold.

Every branch is now a rooted height-two tree, with child stars at its root. For \(s\ge2\), set \(x_1=0\) in the order-\(s\) moment and work modulo \(t^s\). The unrooted term \(t^s U(A)\) plays no role. A child star of order \(i\ge2\) contributes normalized attachment factor \(1+t^i x_i\), since cutting an edge in the child star isolates a leaf and the fully cut attachment gives \(t^i x_i\). A singleton child contributes 1. If \(a_i\) counts the children of order \(i\ge2\), this gives
\[
P_A(t)^{-1}\big|_{x_1=0}\equiv\prod_{i=2}^{s-1}(1+t^i x_i)^{-a_i}\pmod{t^s}.
\]
Here \(\sum_i i a_i\le s-1\); the unrecorded singleton children number \(s-1-\sum_i i a_i\). For each exponent vector \(\alpha\) with \(\sum_i i\alpha_i\le s-1\), the coefficient of \(t^{\sum i\alpha_i}\prod x_i^{\alpha_i}\) gives the sum of products \(\prod_i\binom{a_i+\alpha_i-1}{\alpha_i}\) with the common sign removed. For \(\alpha_i=0\) this factor is 1. Triangular polynomial change of basis in each coordinate replaces these by \(\prod_i\binom{a_i}{\alpha_i}\) without increasing the weighted degree. These moments determine multiplicities by descending weight: the product is zero unless \(a_i\ge\alpha_i\) for every \(i\), and equals 1 at \(a=\alpha\). Since \(L-s\ge s-1\) under \(n\ge3B\), all required moments are known. Size-one branches come from the \(t x_1\) coefficient after larger sizes have been removed. Descending across all sizes reconstructs the tree.

For a nonproper diameter-six example take 17 branches of order 16 attached at their roots to one center. Include all seven triples of child-star orders summing to 15 with every order at least 3, and fill the other positions with repeats. Here \(n=273\), \(B=16\), \(d=17\) and \(L=256\); the bound in Section 2 depending on the number of types would ask for \(L\ge448\).

### Signed specialization and nearly-star branches

**Theorem.** Suppose \(B\ge2\) and \(n\ge3B-1\). If each centroid branch is either a path rooted at an endpoint or has at most one nonroot vertex that is not a leaf, the tree is distinguished among all trees. The types can be arbitrarily mixed.

For a branch of order \(s\ge2\), set all \(x_i=-1\) for \(i<s\) and \(x_s=0\). Let \(\ell(A)\) be its number of nonroot leaves. Group the rooted terms by the root component \(S\). The signed sum over cuts in its complement is zero if that complement contains an edge: toggling such an edge changes the parity of the component count. Otherwise the complement consists of original nonroot leaves, since it is independent and each vertex must have one neighbor in the connected \(S\). Every subset of nonroot leaves is allowed. Thus the normalized rooted factor specializes to \((1-t)^{\ell(A)}\). Also \(U(A)\) vanishes at all \(x_i=-1\) by the same parity cancellation; replacing \(x_s=-1\) by 0 removes its unique uncut term, leaving 1. It follows that
\[
P_A(t)=(1-t)^{\ell(A)}+t^s
\]
at the specified values. Through order \(s-2\) the first inverse moment therefore gives \(\sum_A m_A\binom{\ell(A)+j-1}{j}\) for \(0\le j\le s-2\). These polynomials in \(\ell\) have exact degrees \(0,\ldots,s-2\) and form a basis on the \(s-1\) possible values \(1,\ldots,s-1\). Hence the full leaf-count histogram of each size \(s\) is distinguished at its descending reconstruction step. The precision is available since \(L-s\ge s-2\).

The target's histogram restricts its rival to \(\ell\in\{1,s-2,s-1\}\). For \(\ell=1\) there is only the endpoint-rooted path and for \(\ell=s-1\) only the center-rooted star. Sizes two and three are thereby settled. For \(s\ge4\), subtract the known types' unspecialized inverse contributions. In a remaining branch with \(\ell=s-2\), the sole off-root nonleaf is adjacent to the root, and its away side has size \(k\in[2,s-1]\). For each \(2\le k\le s-2\), the coefficient of \(t^k x_k\) of the remaining unspecialized moment is minus the count of branches with this away size: a term linear in \(x_k\) in the inverse comes from a single detached component, and only that one edge can have away size \(k\ge2\). Determine the \(k=s-1\) count from the total. This reconstructs all branches at size \(s\), so one can divide them out and descend.

For example, for each \(B\ge7\) attach one branch of order \(B\) for each off-root star order \(k=3,\ldots,B-2\), filling with singleton children at each branch root. This gives \(n=1+B(B-4)\ge3B-1\), diameter six, and centroid degree \(B-4<B\). The high-degree hypothesis is not needed here.

The identities were also checked exactly on finite labeled-tree and branch-mixture examples. Neither criterion treats arbitrary diameter-six trees.

## 5. Certifying the centroid height without a degree hypothesis

**Theorem.** If \(n\ge 3B\) and the centroid has eccentricity at most three, then \(X_T\) distinguishes \(T\) among all trees. In contrast to Section 4, there is no maximum-degree hypothesis. The first inverse moment sees weight \(s\) in each descending branch size \(s\le B\), using one extra unrooted coefficient shell at the boundary.

We give a nonnegative certificate in the first inverse moment. Fix \(s\ge2\) and put \(N=s-1\). For a rooted branch \(A\), orient its \(N\) internal edges away from its root and write \(k_e\) for the size of the away side. Set \(y_j=t^j x_j\) for \(1\le j\le N\). These monomials encode every term of \(P_A\) because each factor is normalized by the total size. The ordinary-degree-one part of \(P_A\) is
\[
J_A=\sum_e y_{k_e}.
\]
Its degree-two part has two contributions. The rooted part, denoted \(F_A\), counts cuts of two internal edges, with the monomial for the two detached sizes. The unrooted part, denoted \(D_A\), counts single-edge cuts into two pieces of total size \(s\); the term \(x_s\) itself has already been removed. Thus the degree-one and degree-two terms of \(1/P_A\) are \(-J_A\) and \(J_A^2-F_A-D_A\).

Define \(f(a)=a-s\). On a quadratic monomial \(y_a y_b\) use the weight \(W(a,b)=f(a)+f(b)\) if \(a+b\le s\), and zero otherwise. Let \(\mathcal W\) denote the resulting linear functional on quadratic polynomials. On \(D_A\) its value is \(-sN\), since all \(N\) cuts give two sizes totaling \(s\). Consider
\[
\mathcal H(A)=
\mathcal W\bigl(J_A^2-F_A-D_A\bigr)-sN
-\sum_e W(k_e,k_e)
-(N-1)\sum_e f(k_e)-\sum_e(k_e-1).
\]
The last sum counts ancestor–descendant pairs of different edges, since an away side of size \(k_e\) contains \(k_e-1\) internal edges. We claim \(\mathcal H(A)\ge0\), with equality exactly when \(A\) has rooted height at most two.

Indeed subtraction of the diagonal term removes the repeated edge pairs in \(J_A^2\); the next term subtracts \(f(k_e)+f(k_{e'})\) for each unordered distinct pair. If the edges are incomparable under ancestry, their away sizes \(a,b\) have \(a+b\le N\) and the detached sizes are precisely \(a,b\), so the net contribution is zero. If they are nested, let \(a\) be the ancestor's size and \(b<a\) the descendant's size. The detached sizes are \(a-b,b\). The net before the final subtraction of 1 per nested pair is
\[
2W(a,b)-W(a-b,b)-f(a)-f(b)
=\begin{cases}
b,&a+b\le s,\\
4s-2a-b,&a+b>s.
\end{cases}
\]
If \(b=1\), only the first case is possible and this equals 1. If \(b\ge2\), the value is strictly greater than 1 in either case, using \(a\le s-1\) in the second case. Thus \(\mathcal H(A)=0\) precisely when every descendant edge in a nested pair has away size 1. This is equivalent to rooted height at most two: the second edge on any length-three path from the root has an ancestor edge and an away side with at least two vertices.

To reconstruct, descend through branch sizes as before. The first inverse moment is known through weight \(L-s\ge s\) under \(n\ge3B+1\). If \(n=3B\), this is still true for \(s<B\), and at \(s=B\) the only needed unavailable coefficients are the quadratic shell \(a+b=B\). There \(W(a,b)=-B\), so only their sum is needed. Let \(g=[t^B x_B]\log P_T(t)\), the number of order-\(B\) branches. It is already known from the tail, and \(g\le2\). To recover the missing sum in \([x_B]\log P_T\), take the sum of coefficients of \(x_B^2 x_a x_b\) in \(U(T)\) for \(a\le b,\ a+b=B\). A cut with one \(B\)-component containing the centroid contributes exactly once to \([t^{2B}x_B x_a x_b]P_T(t)\), even though the two \(B\)-components have equal sizes. A cut with both \(B\)-components off the centroid can occur only when \(g=2\), and then these are exactly its two entire order-\(B\) branches. Cutting their two attachments leaves a rooted remainder of order \(B\), and cutting one of its \(B-1\) edges produces the components \(a,b\). Hence the undesired contribution is exactly \(B-1\) if \(g=2\), and zero otherwise. Subtract it to get the needed raw coefficient sum. Passing from \(P_T\) to \(\log P_T\) requires only lower-weight terms in the nonlinear correction, which are already known. Dividing by \(t^B\) recovers the order-\(B\) moment shell. The argument is only needed for \(B\ge2\); size one needs just the linear count.

The moment's constant coefficient counts branches of order \(s\), its linear coefficients give the sum of the \(J_A\), and its quadratic part through weight \(s\) supplies the first term of \(\sum_A m_A\mathcal H(A)\). All other terms depend only on the count and linear coefficients. The target has sum zero, so every rival branch of size \(s\) has height at most two by nonnegativity. The child-star moment recovery in Section 4 now applies to both target and rival. Remove the matched factors and proceed to the next size. The case \(s=1\) is read from the linear count as before.

For instance, at a common center attach two branches of order 9 with child-star orders \((3,5)\) and \((4,4)\), and one branch of order 8 with child-star orders \((3,4)\). Then \(n=27=3B\), the maximum degree is 5, and the centroid has eccentricity three. The earlier degree test fails, the earlier support-size bound needs \(L\ge72\) whereas \(L=17\), and these branches have two nonroot nonleaves. This theorem handles the example and arbitrary mixtures of height-two branches at the stated threshold. The weight identity and equality condition were independently checked on 18,248 rooted labeled trees of orders two through seven, and the two shell cases on explicit trees. These finite checks are not needed for the proof. Unrestricted diameter-six reconstruction is still open.
