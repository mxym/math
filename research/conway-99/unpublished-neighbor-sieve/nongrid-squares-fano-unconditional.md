# Nongrid double-covered squares are unit even in the presence of Fanos

This removes the Fano-free hypothesis from [the nongrid double-square and Hoffman-weighted bounds](doubly-covered-square-short-mark.md). No rank, symmetry, or absence of other shells is assumed.

Let \(P_{\rm pr}\) count induced triangular prisms, \(G\) rook grids, \(Q_2\) induced squares covered by a prism in both directions, and \(B_1\) bad prisms whose three rung caps induce exactly one edge. Let \(S_{\rm edge}\) count the original eligible unit charge-one cost-23 fields with exactly one positive edge, counting each positive-charge field once. Then
\[
 B_1=2(Q_2-9G),\qquad Q_2-9G\le S_{\rm edge}.
\]
In particular with no eligible extra unit fields, not only is every double-covered square in a grid: every bad prism has an independent cap triple. The bound also holds when \(S_{\rm edge}\) is counted in any marked extension (the constructed fields lie in the original class).

## Exact graph correspondence

An induced prism has two triangular faces and three matching edges (rungs). Each rung has a unique cap, outside the prism, adjacent to precisely its two endpoints in the prism: adjacency to another point in either triangle would give two common neighbors to the corresponding prism face edge. The three caps are distinct. If all three cap edges are present, the prism lies in a unique rook grid, while two cap edges would give a forbidden 17-edge nine-set by the [density gap](../../conway-99-involution/grid-density-gap/README.md). Hence bad prisms have either zero or one cap edge.

Take a bad prism with one cap edge, and adjoin its two joined cap sites. The result \(K\) is an induced rook grid with one vertex deleted, on eight sites and fourteen edges. Its degree-four sites form the square consisting of the two capped rungs and the two associated face edges. The four degree-three sites form two disjoint edges, one the uncapped rung and one the joined pair of caps, with no other edges among them. Swapping the row and column roles of \(K\) gives the second prism on that doubly covered square. It too is bad: a grid containing it would contain both prism directions, which are unique because triangle caps are unique. Its cap triple has at least one edge and consequently exactly one. Conversely every nongrid doubly covered square determines exactly this \(K\) and its two prisms. No third prism direction exists at a square. Each good grid has nine double-covered squares, and distinct grids share no square. This proves the count. The two degree-three edges of \(K\) have distinct caps outside \(K\). Each of these caps sees exactly the two endpoints of its own edge and none of the other six sites of \(K\), by the cap isolation just proved in its corresponding bad prism and its unique cap against that prism's endpoints.

## Unit and recovery, with no Fano hypothesis

Write \(A\) for graph adjacency, \(D=3I-A\), and \(d_i=D e_i\) for the ordinary charge-one mark. Define the integer
\[
 u=-D1_K-\mathbf1.
\]
It has \(Au=-4u-2\mathbf1\), sum \(-11\), and cost \(u\cdot u=23\). Indeed \(D+J/9\) squares to seven times itself, and the centered part of \(u\) has squared norm \(7(3\cdot8-2\cdot14+64/9)=196/9\); its constant part adds \(11/9\). As in the [original mark argument](doubly-covered-square-short-mark.md#consequences-and-current-scope), the physical vector is \(y=-\sum_{i\in K}u_i\) in the site marks, and \(y-u_0=-\sum_{i\in K}(u_i-u_0)-9u_0\) belongs to the original graph lattice. The charge-one label is therefore eligible in every marked extension. On \(K\) the label is degree minus four, so every entry of \(u\) is at least \(-1\). The four degree-three sites have value \(-1\), making two negative edges whose outside caps both have value \(+1\).

If \(u_i\ge2\), then \(u-d_i\) is neutral with squared norm \(42-14u_i\), using \(u\cdot d_i=7u_i+2\). For \(u_i\ge3\) this is either negative or zero; zero gives the ordinary mark, which has no positive unit coordinate and cannot be our \(u\). For \(u_i=2\), \(f=u-d_i\) has norm 14 and \(f_i=-1\). Use the [norm-14 characterization](../short-support-packing/README.md): its two seven-site sign sides are independent, and each exterior vertex meeting them sees precisely one of each side (equivalently, the saturated same-sign pair slots allow at most one, and the neutral equation makes the two numbers equal). The negative sites of \(u\) are then exactly the other six negative sites of \(f\) and the ten support-exterior neighbors of \(i\). There are no edges within the first set or between these two sets: a vertex of the second set already sees the negative Fano site \(i\). Every negative edge of \(u\) is therefore an edge in \(N(i)\), with unique cap \(i\) of value 2. This contradicts the two literal negative edges of \(K\) whose caps have value 1. Thus \(u\) is unit.

For a unit charge-one cost-23 field, its positive and negative sites have sizes six and seventeen. The equation gives cross degrees \(6+d_P\) and \(2+d_N\), respectively, so \(e_N=e_P+1\). The negative sites consume at least \(17+4e_N\) positive pair slots, since \(\binom{2+d}{2}\ge 1+2d\). The pair capacity is \(30-e_P\). Hence \(e_P\le1\) and \(e_N\le2\). The two degree-three edges of \(K\) are therefore the two negative edges, and \(e_P=1\).

For an explicit recovery, take one endpoint of each negative edge; their two common neighbors are their square corner (value zero) and a second site (value \(+1\)). The value of the latter follows because it is outside \(K\) and already has two neighbors in \(K\), and \(u\) is unit. The four square corners are recovered in this way. Their other common neighbors are distinct, since repetition sees at least three sites of \(K\). Thus the single field \(u\) recovers \(K\) and its square. No claim is made that every one-edge unit field is a square mark.

## Weighted Hoffman companion

Let \(C\) be an actual eligible Hoffman 22-coclique, and let \(D_k\) count these squares with \(|C\cap K|=k\). The angle with \(c=-1_C\) is \(u\cdot c=7k-10\) exactly as in the earlier theorem. The preceding unconditional unit conclusion restores its entire proof of \(D_0=0\), the square-corner restriction at \(k=1\), and
\[
 D_1+D_2+2D_3\le S_C,
\]
where \(S_C\) counts eligible unit cost-23 charge-one labels in the same extension. The only additional place where the prior proof invoked Fano-freeness was for \(u'=c-u\) at \(k=3\). This charge-one cost-23 label has entries at most 1. Any charge-one cost-23 label \(b\) has no entry at most \(-2\): adding \(d_i\) at such a coordinate gives charge two and cost \(50+14b_i\le22\), while the coordinate sum \(-22\) forces cost at least 22 with all coordinates nonpositive in the equality case. At equality the translated \(i\)-th coordinate is \(+1\), impossible. Therefore \(u'\) is unit regardless of Fano presence. Its positives are independent because \(C\) meets both of the two negative edges of \(u\), making it distinct from every square mark, and subtraction from a fixed \(c\) is injective. No bound is claimed for an ineligible coclique.

## Local rung versus total prism-face count

This related local statement concerns a triangle \(T\), not its individual vertices. Write \(f_T\) for its number of prism mates (the transversal triangles in its cubic wing), \(g_T\) for grids through it, \(B_1(T)\) for its one-cap-edge bad prism mates, and \(r(e)\) for prisms with graph edge \(e\) as a rung. For every \(e\subset T\), \(r(e)\) is the number of common transpositions of the two physical mate involutions after identifying their two wings along the inter-wing matching. Each uses two transverse edges in that matching. A transversal triangle in the wing is precisely a fixed index of the third return; its three mates are the three caps of its prism with \(T\).

If a common transposition uses two fixed indices, the corresponding six wing sites are two transversal triangles joined by two physical mate edges. The third mate is forced, since otherwise their six-site shore has a cut of size two entirely in one physical mate matching, [impossible](arbitrary-wing-thin-cuts.md). Thus the transpositions of this kind are exactly the grid components: \(g_T\) for each \(e\). A common transposition using exactly one fixed index is precisely the unique joined pair of caps of a one-cap-edge bad prism mate, counted once over the three edges of \(T\). The other transpositions use two nonfixed transverse edges. There are \(3(12-f_T)\) nonfixed transverse edges, so
\[
 \sum_{e\subset T}r(e)
 \;\le\;3g_T+\frac{3(12-f_T)+B_1(T)}2 \;\le\;18-f_T+2g_T.
\]
In fact the unused budget counts the incidences of wholly uncovered squares on the three edges of \(T\): the four-cycle consisting of \(e\) and the two transverse endpoints has one prism direction exactly when its transverse edge is in a transversal triangle, and the other exactly when that edge is aligned with its two mates. Hence both directions missing is precisely an unused edge. This local inequality is not presented as an improvement to the already stronger global prism bound.


## Exact identification of five-site three-edge shores

Let \(C_5\) count actual **nontrivial bonds with a five-site shore** in the cubic triangle wings, with the base triangle specified; no orientation sign for the other shore is used. A bond is a cut within one connected wing component into two connected nonempty shores, and nontrivial here excludes a singleton on either side. Then, with no rank/Fano hypothesis,
\[
 C_5=4(Q_2-9G)=2B_1\le4S_{\rm edge}.
\]

To see that every such bond gives the same eight-site shape, write the counts of the five-site shore in its three physical wings. The sum of the lower bounds on crossed inter-wing matching edges is twice the difference between the maximum and minimum counts, so they differ by at most one. Hence their values are \(1,2,2\). Name the small-wing site \(u\) and its root \(p\). The odd single site in its physical mate matching requires a boundary edge, and the two unequal inter-wing size pairs require one edge each. This exhausts the budget of three. Therefore the two larger wing pairs are mate edges, and their inter-wing matching lies wholly inside the shore. They form a square, say with matched pairs \(v,w\) and \(v',w'\), where \(v,v'\) and \(w,w'\) are the mates. Site \(u\) sees one site in each larger wing inside the shore. These two sites must be one of the matched pairs, since opposite corners of the square already have two common neighbors within it. Take them to be \(v,w\).

Write the other two roots \(b,c\), with \(v,v'\) in the wing of \(b\) and \(w,w'\) in the wing of \(c\). The eight sites of \(T\) and the shore are exactly the punctured grid \(K\): its central square is \(b,c,w,v\), the two extension edges are \(pu\) and \(v'w'\), and its four full lines are the two triangles of the rooted square's row directions and the two of its column directions. If this \(K\) lay in a rook grid, the missing site \(x\) would belong to the wing of \(p\) and would absorb all three boundary edges (the mate edge of \(u\) and the transverse edges of \(v',w'\) into the small wing). In that grid the six sites outside its root line form an entire wing component, so the complementary shore would be a singleton. Thus any nontrivial bond of this size gives a nongrid \(K\), and its label is exactly the unit square mark proved above.

Conversely take a nongrid \(K\) and remove any of its four full lines \(T\). The other five sites are in \(W(T)\), since each has exactly one neighbor on \(T\). They induce the connected triangle-square sharing one edge, with six edges, hence have cubic boundary of size \(3\cdot5-2\cdot6=3\) within the wing. The three outside boundary endpoints are distinct: each is in the small physical wing, already sees its root in \(T\), and if two boundary edges met there, the label \((A-3I)1_K-1\) would have value at least \(+2\) there, contrary to the unit proof. The other shore within the affected component is connected: if it had multiple components, each would need at least two crossing edges since no wing has a bridge, invoking the [thin-cut theorem](arbitrary-wing-thin-cuts.md). The three distinct endpoints also make that other shore nonsingleton. All four choices of full line are distinct bonds, and recovering \(K\) from the base triangle and five-site shore is literal union. Conversely in each bond its root triangle is one of the four full lines of \(K\). This is the asserted exact correspondence, not merely a reuse limit of four per field. In particular a separate lower bound on \(C_5\) can spend square marks, but one must not add \(C_5/4\) and \(Q_2-9G\) as two independent shell charges.


## Disjointness of five-site shores at a fixed triangle

Distinct five-site shores at one triangle are disjoint, and at most one wing edge joins two of them. There is no rank hypothesis. Suppose two five-site shores \(X,Y\) intersect, and put \(I=X\cap Y\), \(O=W\setminus(X\cup Y)\) inside the affected component (the two shores then belong to the same component). Write \(d(Z)\) for edge boundary size. The cut identity
\[
 6=d(X\setminus Y)+d(Y\setminus X)+2e(I,O)
\]
forces the two equal difference sizes to be 1 or 3: a two-site set in a cubic graph has boundary at least four, and a four-site set does too since a five-edge diamond and \(K_4\) are forbidden. Hence \(I\) has size 4 or 2 and \(d(I)\ge4\). The other identity
\[
 6=d(I)+d(O)+2e(X\setminus Y,Y\setminus X)
\]
forces the union's cut size at most two. It is nontrivial as the component has at least twelve sites: its order is a multiple of six, and order six would give a singleton complementary shore for either five-set. It is therefore a two-cut, since there is no wing bridge. Such a shore has size divisible by six by [cut balance](arbitrary-wing-thin-cuts.md); the union size eight is impossible, and size six is impossible by [the no-six-site-shore theorem](no-six-site-wing-two-cut.md).

For disjoint \(X,Y\) their ten-site union has boundary \(6-2e(X,Y)\), so two connecting edges would yield an impossible ten-site two-cut, and three would give a union of whole cubic wing components of order ten (wing component orders are multiples of six). With the original charge-one cost-23 marks \(u_X,u_Y\) of \(T\cup X,T\cup Y\), the raw product is exactly \(2-7e(X,Y)\). Indeed the two eight-sets meet in \(T\), and their directed cross-adjacency count is \(6+5+5+e(X,Y)\): these are respectively the edges in the ordered triangle, the contacts of each shore to its roots, and the edges between shores. Thus their physical centered Gram has diagonal \(28/9\), and off-diagonal \(1/9-e(X,Y)\). In particular one may contract the distinct five-site shores at a fixed triangle into degree-three vertices with simple pairwise adjacency.
