# Thirteen triangle fibers of the K6 disjointness pattern are impossible

Write \(E(K_6)\) for the fifteen two-element subsets of \(\{0,1,2,3,4,5\}\). Suppose that for each of thirteen of these indices there is a distinct, disjoint graph triangle in an SRG(99,14,1,2). Suppose triangles indexed by intersecting pairs have no cross-edges, and triangles indexed by disjoint pairs are joined by a perfect matching. **Such thirteen triangles cannot occur.** In particular neither fourteen nor all fifteen can occur. There is no symmetry or rank hypothesis.

A perfect matching of abstract \(K_6\) for which all three indices are present gives a literal nine-site grid: its three fibers have nine internal and nine cross-edges, so the [nine-site equality case](../../conway-99-involution/grid-density-gap/README.md) gives the rook grid, with every exterior vertex adjacent to exactly one of its sites. This automatically supplies the required grid condition from just the pairwise fiber hypotheses.

## Contact patterns

Work either with one or two missing indices, collected in \(M\), and let \(m=|M|\). The two missing indices may be incident or disjoint. An exterior vertex meets at most one site of each real triangle: two sites on the same triangle already have their unique common neighbor. Its set of contacted indices must meet **each present perfect matching** in exactly one member. The [small standard-library checker](partial-k6.py) tests every one of the at most \(2^{14}\) subsets of the present indices. Exactly the following \(6+m\) patterns pass, for each of the three cases:

* an ordinary type \(a\) (\(0\le a\le5\)) hits the present indices containing \(a\);
* an exceptional type \(e\in M\) hits the present indices disjoint from \(e\).

Each exceptional type has exactly three vertices. Choose two disjoint present indices \(f,g\) whose complement is its prescribed missing \(e\); such a partition of the four other abstract points exists in all three cases. On the nine pairs of sites of \(f,g\) there are 15 common-neighbor slots, three adjacent pairs and six nonadjacent. The two fibers supply 12 slots via their internal edges, six each. No other present fiber supplies one, since the only index disjoint from both is absent. Only the exceptional type \(e\) hits both, each such vertex consuming one slot.

Let \(N_a\) count ordinary vertices of type \(a\). If \(f=ab\) is present and disjoint from \(j\) missing indices, each of its three sites has inner degree \(2+6-j\), hence the exterior supplies \(18+3j\) contacts to that fiber. The exceptional types supply exactly \(3j\), so \(N_a+N_b=18\). The graph of present indices on six abstract points is connected and contains a triangle, yielding \(N_a=9\) at every point.

## Integral rows at a single exterior vertex

Let \(S\) be the index set contacted by that vertex. At a present fiber \(f\), summing its three common-neighbor quotas gives \(6-1_{f\in S}\). Of these, \(2\cdot1_{f\in S}\) pass through the fiber itself, and one passes through each contacted fiber disjoint from \(f\). Thus the exterior neighbors of the vertex must supply
\[
 b_f=6-3\,1_{f\in S}-|\{g\in S:g\cap f=\varnothing\}|.
\]
Write \(n_a\) and \(n_e\) for its numbers of exterior neighbors of ordinary and exceptional types. They sum to \(14-|S|\), and for every present \(f=ab\) satisfy
\[
 n_a+n_b+\sum_{e\in M:e\cap f=\varnothing} n_e=b_f.
\]

Call a point **untouched** when it lies in no missing index. On these integral rows the following two inequalities suffice: every vertex of any untouched ordinary type has at least one exceptional neighbor, and every exceptional vertex has at most one neighbor in **each** untouched ordinary type. The checker enumerates all integer choices \(0\le n_e\le14-|S|\) for the at most two exceptional types. The remaining equations give pair sums \(n_a+n_b\) on the present edges; subtracting three pair sums around an available abstract triangle uniquely recovers each \(2n_a\). It checks integrality, nonnegativity, the total degree and every original equation. The numbers of rows for the ordinary types in order \(0,\ldots,5\) followed by the listed missing types are:

| Missing indices | Integral row counts | Required edges to exceptional types | Available edges |
|---|---|---:|---:|
| 01 | 3,3,2,2,2,2; 2 | 36 | at most 12 |
| 01,23 | 8,8,8,8,6,6; 5,5 | 18 | at most 12 |
| 01,02 | 10,8,8,6,6,6; 4,4 | 27 | at most 18 |

Indeed if there are \(u\) untouched types, their \(9u\) vertices need at least \(9u\) edges to the exceptional vertices, of which there are only \(3m\) with at most \(u\) such neighbors each. Since \(m\le2\) and \(u>0\), this is impossible.

Here is also an analytic reading of the small integral-row obstruction. For an ordinary source of type \(i\) set \(z_e=n_e-1_{i\in e}\). For an exceptional source of type \(h\) set \(z_e=n_e+1_{h=e}-1_{e\cap h=\varnothing}\). Substitution in the equations above gives, for every present \(ab\),
\[
 \left(n_a-\sum_{e\ni a}z_e\right)+
 \left(n_b-\sum_{e\ni b}z_e\right)=3-\sum_e z_e.
\]
Thus both parenthesized quantities are the same integer \(k\) at every abstract point. For an untouched ordinary source this makes \(\sum n_e=3-2k\) a nonnegative odd integer. For an exceptional source, \(\sum z_e\ge0\), since \(h\) contributes at least one and there is at most one other missing index. Therefore \(k\le1\), and \(n_a=k\) at every untouched point. These arguments prove precisely the inequalities used in the table.

## A global consequence for pentagons of good prisms

A good prism is one contained in a nine-site grid; the three parallel triangles in each grid form a block. Count unoriented **Berge pentagons**: five distinct triangles \(T_0,\ldots,T_4\) and five distinct such blocks, with consecutive triangles lying in their associated block (indices cyclic), the count taken up to dihedral order. Two distinct blocks through a fixed triangle have their other lines pairwise anticomplete by one-domination, as explained in [the bad-prism count](bad-prisms.md). Thus consecutive triangle marks have inner product \(-2\) and all other pairs have inner product \(+1\), being distance two through distinct blocks.

For a concrete labeling one may use abstract points 1 through 6 instead. Label the five triangle marks successively **12, 34, 15, 23, 45**. The Gram rule is exactly the one for \(v_{ab}=\sqrt3(1_{ab}-\mathbf1_6/3)\): 4 on the diagonal, \(-2\) for disjoint indices, \(+1\) for incident indices. Hence all inner products of any linear combinations computed with these model vectors are also correct for the actual marks. For each good edge of the cycle its grid supplies a third triangle with mark the negative of the two original marks' sum, so the five new lines have the complementary labels **56, 26, 46, 16, 36**. The new line \(U_i\) for edge \(T_i,T_{i+1}\) has inner product \(-2\) with \(T_{i+3}\), so these two triangles form a prism. If this **secondary prism** is good, its third line has the remaining complementary two-subset. The five possible newly supplied indices are all distinct and are exactly the five not listed so far. With any three good secondary prisms there would be thirteen distinct triangle fibers of the forbidden type. Indeed all distinct model lines have inner product \(+1\) or \(-2\), giving actual disjoint triangles with zero or three cross-edges. Thus **at least three of the five secondary prisms are bad**. In particular with all prisms good, the incidence graph of triangles and their parallel-triple blocks has no cycle of length ten. Combined with the [rook-array four-cycle obstruction](bad-prisms.md), its girth is at least twelve.

There is also an unconditional count. Let \(N_5\) be the above number of Berge pentagons and \(B\) the number of bad prisms. Orient a specified charged bad secondary prism into its end \(U\) (the edge-completing line) and its cycle vertex \(T\). A grid through \(U\) fixes the unordered pair of adjacent cycle vertices \(T_0,T_1\); distinguish their order by any fixed labeling. The two other cycle vertices must be in two distinct grids through \(T\). Assign these two grids in order to \(T_0,T_1\). Each can supply at most one appropriate line, because its assigned target triangle is anticomplete to \(T\), lies outside the grid, and can match at most one of the other two parallel lines. Thus at most \(g_U g_T(g_T-1)\) pentagons charge a specified orientation. Each endpoint of a bad prism has at most four grids, as proved in [the bad-prism count](bad-prisms.md), giving at most 96 per unoriented bad prism. Counting the at least three distinct charged secondary prisms of each pentagon proves \(N_5\le32B\). No bound here excludes an entire rank or proves graph nonexistence.
