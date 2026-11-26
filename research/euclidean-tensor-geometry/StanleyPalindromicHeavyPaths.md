# Untagged variable-order path skeletons

**Yongxian Zhang.** AI-assisted proof development and mathematical checking; no external peer review claimed.

**Theorem.** Let a nonempty heavy skeleton be a path. Suppose its block orders in path order form a palindrome, all are divisible by a common \(g\ge3\), and all lie in \([s,2s-1]\) for an integer \(s\ge h+2\), where \(h\) is the heavy cutoff. Then the ordinary chromatic symmetric function determines this variable-order path and the nonroot leaf count of its rooted block at every position. In particular it reconstructs the entire unrooted tree at cutoff \(h=2\), even when its ornamented path is not symmetric and orders and rooted types repeat at interior vertices or both ends.

From the top heavy layer one reads the multiset of rooted-tail factors and their orders even in any CSF-equal rival. Set all \(x_i\) with \(i\le h\) to zero; the surviving unmarked forests leave all blocks intact and give the weighted skeleton cut polynomial. For at least three blocks, a one-edge split has smaller side of weight \(<2s\) exactly when it cuts off a single skeleton leaf. Indeed each block has order at least \(s\) and each single block has mass \(<2s\). The observed two such edges certify that the rival skeleton is a path. For two blocks the skeleton is automatic.

Write \(N\) for the whole order. The proper prefix masses form a set \(J\subseteq (0,N)\), which is invariant under \(a\mapsto N-a\) because the order word is palindromic. The unmarked split multiset therefore contains each pair \(\{a,N-a\}\), \(a<N/2\), either zero or two times, and a middle pair \(a=N/2\) at most once. Because proper prefix masses in any weighted path are strictly increasing, the rival must have both \(a\) and \(N-a\) as proper prefix masses in the twice-occurring case. Hence the mass set \(J\), and the entire block order word given by its successive differences with endpoints 0 and \(N\) added, are known.

Let \(P_a,Q_a\) be the total nonroot leaves in the prefix and suffix of mass \(a\in J\), and \(L\) the total number of these leaves, given by the coefficient of \(x_{N-1}x_1\). Put \(S_a=(P_a+Q_a)/2\), \(D_a=P_a-Q_a\). Then \(D_{N-a}=D_a\), \(S_{N-a}=L-S_a\), and reversal negates all \(D_a\).

Mark a component by cutting exactly one pendant leaf in it, so its indexed mass decreases by one and it contributes a factor \(x_1\). In the following coefficients where total low weight is 1 or 2, no root of a block can appear in a low component: if it did, its entire block would stay in low components, whose total weight is \(<g\le s_v\). Each intact skeleton component initially has order divisible by \(g\); since the total deficit is at most 2, the residue of each large output size modulo \(g\) identifies the number of leaves detached from it (0, 1, or 2). All designated large factors are \(>h\) by the bound \(s\ge h+2\); each marked one loses only one. Thus the desired cuts are counted without contamination, even on a variable-order spine.

For \(a\in J,\ a\le N/2\), the coefficient of \(x_1 x_{a-1}x_{N-a}\) is \(P_a+Q_a\). The coefficient of \(x_1^2 x_{a-1}x_{N-a-1}\) is \(P_a(L-P_a)+Q_a(L-Q_a)\), except at \(a=N/2\), where twice this coefficient gives the displayed expression. So \(S_a,D_a^2\) are known.

For distinct \(a,b\in J\cap(0,N/2]\), put \(c=N-a-b>0\). A prefix of mass \(a\) and a suffix of mass \(b\) are disjoint, and the remaining nonempty interval has mass \(c\ge s\). If \(c\in J\), each permutation of the three lengths is possible: masses of the first and last determine unique two cuts because both belong to the reversal-invariant \(J\), and their sum is \(<N\). Let \(C_{ab}\) be \([x_1^2 x_{a-1}x_{b-1}x_c]U\), doubled if the marked masses are equal in the corresponding choice of labels. As in the equal-order argument, after removing its baseline \(C_{ab}^{(0)}\) calculated at all \(D=0\), it satisfies
\[
2(C_{ab}-C_{ab}^{(0)})+D_a^2+D_b^2=D_c(D_a+D_b)-D_aD_b.
\]
This follows by pairing the six formal orders with their reversals: a mark in the middle, if its left and right edge masses are \(u,v\), uses \(L-S_u-S_v+(D_v-D_u)/2\). Cycling the marked pair reconstructs \(D_aD_b\), including when \(c=a\) or \(c=b\).

If \(c\notin J\), it must be in the middle, and the only two orders are \((a,c,b)\) and \((b,c,a)\). The coefficient with the two endpoint parts marked is then
\[
[x_1^2 x_{a-1}x_{b-1}x_c]U =P_aQ_b+P_bQ_a=2S_aS_b-\tfrac12D_aD_b.
\]
So the product is recovered in either case. The pair products and magnitudes determine the \(D\) vector up to overall sign; take successive differences of \(P_a=S_a+D_a/2\) over the known sequence of prefix masses, including 0 and \(N\), to reconstruct the nonroot leaf counts. At \(h=2\), the number of length-two arms is \(s_v-1\) minus the nonroot leaf count, and the remaining leaves are singleton branches. These counts determine the rooted block, proving full reconstruction.

**Example.** Order words over \(\{6,9\}\) that are palindromes and use both sizes meet the hypotheses with \(h=2,g=3,s=6\). Every occurrence can independently choose any number of this block's allowed length-two arms. The orders are not distinct, any pair of equal orders can have distinct or equal full types, and no leaf tags or centroid separation are present.


## Extension: full rooted block series on a palindromic, variable-order path

Under the same palindromic and order-band hypotheses, replace \(g\ge3\) and \(s\ge h+2\) by \(g>2d\) and \(s\ge h+2d+1\), for any integer \(d\ge1\). Then the ordinary chromatic symmetric function recovers each normalized rooted cut series through order \(d\). If \(d\ge D_h=\sum_{j\le h}j b_j\), where \(b_j\) counts the rooted \(j\)-vertex types, this gives the full tree at any cutoff \(h\) by the [bounded-branch long-tail argument of the leaf-tagged proof](StanleyLeafTaggedHeavySkeleton.md). No modular tags on individual vertices are needed.

Write \(A_v(t)\) for the normalized rooted block series, \(T(t)=\prod_v A_v(t)\), and \(P_a(t),Q_a(t)\) for the products over the prefix and suffix of mass \(a\in J\), now series rather than scalar counts. In this section all initially extracted data are through order \(2d\). For \(1\le k\le2d\), the coefficient of \(x_{a-k}x_{N-a}\) with only low factors elsewhere gives \([t^k](P_a+Q_a)\). Indeed no root can lie in the low factors (low weight \(k<g\)), and exactly one component can have an order not divisible by \(g\), so it lost all \(k\) vertices from its original mass \(a\). The high cutoff is respected even at the smallest mass by the bound on \(s\). Similarly \([x_{N-k}]\) with only low factors elsewhere gives \([t^k]T\). Constant terms are known. At the central cut \(a=N/2\) the one-shortened coefficient still counts both choices of side to shorten.

The identities \(P_{N-a}=T/Q_a\) and \(Q_{N-a}=T/P_a\) then give both the symmetric inverse
\[
U_a=\tfrac12(P_a^{-1}+Q_a^{-1})
     =\frac{P_{N-a}+Q_{N-a}}{2T}
\]
and the square of the antisymmetric inverse
\[
\Delta_a^2=\left(\tfrac12(P_a^{-1}-Q_a^{-1})\right)^2
          =U_a^2-\frac{P_{N-a}+Q_{N-a}}{T(P_a+Q_a)} .
\]
These are computed in the coefficient field \(\mathbb Q(x_1,\ldots,x_h)((t))\), with the displayed denominators all units.

For distinct \(a,b\in J\cap(0,N/2]\), let \(c=N-a-b\), which is the mass of the interval between the corresponding disjoint end segments, so \(c\ge s\). For every \(1\le k\le2d\), extract the coefficient of \(x_ax_bx_{c-k}\) with only low factors elsewhere. It counts exactly two spine cuts with intact components of masses \(a,b,c\), and marks only component \(c\) with that deficit, by divisibility and the root bound. If \(c\in J\), both endpoint placements of \(c\) are allowed and each admits two orders of \(a,b\), hence subtract \(2[t^k](P_c+Q_c)\). If \(c\notin J\), no subtraction is needed. The remainder is
\[
[t^k]T\left(\frac1{P_aQ_b}+\frac1{P_bQ_a}\right)
= [t^k]\,2T(U_aU_b-\Delta_a\Delta_b).
\]
In this display, \([t^k]\) acts on the full product to its right. The constant term of the middle-placement expression is 2. This recovers every mixed product \(\Delta_a\Delta_b\) through order \(2d\).

The squares and mixed products recover all \(\Delta_a\) through order \(d\) up to simultaneous sign. If all squares vanish through order \(2d\), all \(\Delta_a\) vanish through order \(d\). Otherwise choose an index whose square has minimal valuation \(2e\le2d\). Its series square root determines \(\Delta_a\) up to sign through order \(2d-e\), using the known leading coefficient up to sign and characteristic zero. Divide each mixed product by this anchor of valuation \(e\). Since every other nonzero antisymmetric series has valuation at least \(e\), the error from truncating the anchor is \(O(t^{2d+1})\) before division, so the quotient is determined through \(2d-e\ge d\). For each selected mass \(a\le N/2\), invert \(U_a+\Delta_a\) and \(U_a-\Delta_a\) to recover \(P_a,Q_a\), and recover the remaining prefix products by taking complements in \(T\). Divide successive prefix products along the known mass sequence to obtain each \(A_v\) through order \(d\). The global sign choice only reverses the path.
