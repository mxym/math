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
