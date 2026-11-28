# At least twenty-four edges in a rank-six intersecting Ryser counterexample

**Theorem.** A finite intersecting six-partite six-uniform hypergraph with covering number six has at least **24 distinct edges**. There is no upper bound on the active part sizes in the hypothesis.

This extends the [previous 23-edge necessary condition](RyserSixTwentyThreeEdges.md), which rules out at most 22 edges and bounds maximum degree by eight if there are 23. The theorem does not rule out 24 edges, settle the rank-six conjecture, or apply without partiteness. Historical context is the separate \(\tau\ge5\) extremal-edge problem of [Abu-Khazneh–Pokrovskiy](https://arxiv.org/abs/1409.4938), the [linear intersecting setting](https://arxiv.org/abs/1508.00951), and the [2026 large-rank counterexamples](https://github.com/openai/math/tree/main/preprints/A-Counterexample-to-Rysers-Covering-Conjecture-September-23-2026); none is this 23-edge exclusion.

Suppose for contradiction there are 23 edges. We use the following consequences proved in the previous certificate: the active parts have at least six vertices, vertex degrees lie in \([2,8]\), any two vertices leave at least nine edges uncovered, each edge contains at most one degree-two vertex and at least three vertices of degree at least four, distinct edges intersect in at most four vertices, and no two vertex stars are nested. These are all available without an upper bound on part size.

Write \(D\) for the edges containing a degree-two vertex, \(A=23-|D|\) for the number of other edges, and call two distinct edges **ordinary**, **medium**, or **high** according as their intersection has size \(1,\ 2\text{ or }3,\) or \(4\). Let \(L\) count medium pairs, let \(l_3\) count those of size 3, and let \(h\) count high pairs. A row is called good if it has no medium partner, bad otherwise.

## 1. Pair transportation and the exact profile enumeration

Let \(S=\sum_v\binom{d(v)}2\), \(B=\sum_{v<w}\binom{c(v,w)}2\), where \(c(v,w)\) is vertex codegree. Double counting at each edge pair gives
\[
 E=S-253=L+l_3+3h,\qquad 2E-B=L.
\tag{1}
\]
For two parts with degree profiles \(a,b\), their codegree table has row and column sums \(a,b\). Its entry at degrees \(x,y\) obeys
\[
 \max(0,x+y-14)\le c\le
 \begin{cases}0&x=y=2,\\ \min(x,y)-1&\text{otherwise}.\end{cases}
\tag{2}
\]
The lower bound uses the nine uncovered edges; the upper bounds use the degree-two edge condition and star nonnesting.

For each pair of part profiles, minimize \(\sum\binom c2\) with **both** margins, not merely one at a time. After starting at each lower bound, the cell offers one-unit increments with consecutive costs \(c,c+1,\ldots\). This is exact integer min-cost transportation. The checker verifies margins, original objective, and absence of negative cycles in the residual network for every accepted table. Absence of such a cycle certifies optimality because a flow difference with zero divergence decomposes into residual cycles. Infeasibility, when necessary, is certified by a cut or a negative residual margin.

Enumerate the 80 part patterns (partitions of 23 into at least six degrees between 2 and 8 with the largest two summing to at most 14), and unordered multisets of six such patterns. Impose the earlier incidence bounds on degree 2 and on degrees at least 4 and the necessary \(S\ge253\). For a profile let \(B_*\) be the sum of its 15 pair transportation minima. Of 229202 enumerated profiles after these bounds and pair feasibility, exactly 576 have \(F=2E-B_*\ge0\); the largest \(F\) is 13. Hence \(L\le F\le13\). All these counts, as well as the short degree-profile lists used below, are exact checks supplied with this note.

## 2. Private mates, and the effect of at most two medium pairs

If a vertex has degree two on an edge \(e\), its other edge (the **mate** of \(e\)) meets \(e\) only there. Indeed removing any vertex \(v\) from the six-element cover \(e\) must leave an uncovered edge meeting \(e\) only at \(v\).

**A high pair cannot have both endpoints in \(D\).** Its two degree-two vertices cannot be in a common coordinate, by the mate property. If they occur at the two different coordinates where the edges differ, the mate of the first edge must meet the second in the opposite differing coordinate, acquiring two degree-two vertices, impossible. If they occur at the same differing coordinate, only the two mates can avoid all four common vertices and still meet both edges: an edge using neither degree-two vertex would need both distinct values of the other differing coordinate. The four common vertices plus a common vertex of the two mates then give a five-cover. This also proves the analogous fact for intersection \(r-2\) and a putative cover number \(r\) in any \(r\)-partite intersecting \(r\)-uniform family with \(r\ge4\).

Here is a useful comparison for any high pair \(e,f\) differing in coordinates \(i,j\). A third edge that is not medium with either has intersection sizes in \(\{1,4\}\) with both, and these sizes differ by at most two, so they are equal. If it uses \(e_i\), it must use \(f_j\), and conversely; likewise \(e_j,f_i\) occur together. Each of these cross pairs of vertices has equal counts on ordinary-or-high third edges. Consequently the difference of their vertex degrees is exactly the difference of their contributions from exceptional third edges (medium with at least one endpoint). If both vertices have degree two and neither has exceptional contributions, the one required cross edge would contain two degree-two vertices. We will use this comparison repeatedly.

**For \(L\le2\), the graph of high pairs is triangle-free and has maximum degree at most two.** Use Hamming distance on the six coordinates (a high pair is at distance 2). No three edge rows agree in four fixed coordinates: if three did, their values in both remaining coordinates would be pairwise distinct, since intersection 5 is forbidden. A private witness for one row at the first remaining coordinate would be forced to use the two different values of the other coordinate in order to meet the other rows.

Suppose a maximal high clique \(C\) has size at least three. Fix a row and list the two differing positions for each other row. These pairs of positions are distinct; they must intersect pairwise (disjoint pairs give distance 4), and if they meet in one place, the changed values at that place must agree. Thus these position pairs form either a star or the three pairs of a triangle. A third row outside \(C\) with no medium relation to \(C\) must meet **every** row in \(C\) once: if it were high to one and ordinary to another, distance 5 would violate the triangle inequality, and being high to all violates maximality.

In the star case, if \(|C|=k\) then the rows share \(6-k\) coordinates; in each of the \(k\) varying coordinates one row has a minority value and all others a common majority value, with different minority rows in the different coordinates. An outside row meeting each clique row once either uses one fully common vertex or uses all the minority vertices. Otherwise a majority block of \(k-1\) matches cannot be completed by the missing singleton, which is only available in that same coordinate. For \(k\le5\), the fully common vertices plus one minority vertex cover the clique and all such outside rows, using at most four vertices. For \(k=6\), two values in any varying coordinate suffice. In the triangular case there are four clique rows, three fully common coordinates, and three varying coordinates whose matching blocks are the three different partitions into two pairs. Two blocks in different varying coordinates intersect, so an outside row meeting every clique row once must use a fully common vertex. The three common vertices cover all these rows. In all cases there are at most two exceptional outside rows, which are covered by one further vertex, contradiction. This proves triangle-freeness. Any pair of high neighbors of a row must now be medium to one another (distance at most 4 and neither high nor ordinary). Three high neighbors would require three medium pairs.

Two more consequences are convenient. If \(e\) is bad with just one medium partner \(g\), and \(f\) is a good high neighbor of \(e\), then:
- If \(g\) is not high to \(f\), \(e\notin D\). In fact \(g\) matches \(e\) at one or both differing positions and matches \(f\) at neither, by subtracting \(s(g,f)=1\) from \(s(g,e)=2\) or 3. Each of \(e\)'s different values either has one extra occurrence (and then degree at least three), or has equal degree to its crossed counterpart, with no exceptional contribution to either. The latter equality cannot be two by the cross rule. Its common positions with \(f\) also cannot have degree two.
- If \(g\) is high to \(f\), \(f\notin D\), by the symmetric comparison: \(g\) matches more of \(f\) than of \(e\), and at neither differing position matches \(e\).

Call the latter arrangement, for a medium pair \(a,b\) of size 3 with good common high neighbor \(f\), a centered pair. Assume \(a,b\) have no other medium partners. The three rows share the three common positions of \(a,b\), and on the other three positions \(i,j,k\), \(f\) agrees with \(a\) at \(i\), with \(b\) at \(j\), and has a third value at \(k\). This follows since its two distances to \(a,b\) sum to four, one more than their distance. Put \(R\) for the sum of degrees at the three common positions, \(d=d(f_k)\), \(s=d(a_k)\), \(t=d(b_k)\). The cross comparison using \(b\) as the only exception for \(a,f\), and \(a\) for \(b,f\), yields
\[
 d(a_j)=d(b_i)=d,\qquad d(f_j)=s+1,\qquad d(f_i)=t+1.
\tag{3}
\]
Every edge other than \(f\) through \(f_k\) contains both \(a_j,b_i\) (and neither \(a,b\) can be such an edge). If each bad row has exactly one high neighbor, its total vertex-degree sum is \(28+3+2=33\), by counting its intersection sizes with the other 22 edges. Thus
\[
 R+d+s+t=32.
\tag{4}
\]
If \(a,b\in D\), their degree-two vertices must be at \(k\) by (3), since \(f\notin D\) and their other positions are common with \(f\). Then \(s=t=2\), so \(d\ge4\) because \(R\le24\).

## 3. Exact exclusion for \(L=0,1,2\)

For \(L=0\) the high graph is a matching, all its endpoints outside \(D\), so \(h\le\lfloor A/2\rfloor\). For \(L=1\), the two bad vertices have high degree at most one (a row of high degree two has the two medium partners as its neighbors, and cannot be one of them). Thus \(h\le\lfloor A/2\rfloor+2\). For \(L=2\), if the two medium pairs share an endpoint, all three bad rows have high degree at most one: a high-degree-two row would need as neighbors one of these two medium pairs, neither including itself nor including its own medium partner. Otherwise the four bad rows are arranged in two disjoint medium pairs. A bad row has high degree two only if both its high neighbors belong to the other medium pair, so its high edges are internal to these four. The internal high graph is a subgraph of \(K_{2,2}\); an outside high attachment can use only an isolated bad row and at most once. The number of internal edges plus isolated rows in any subgraph of \(K_{2,2}\) is at most four, with equality only for the empty and the full graph. Hence \(h\le\lfloor A/2\rfloor+4\).

Apply these bounds and (1) to the 576 profiles. The exact checker finds:
- \(L=0\): no surviving profile.
- \(L=1\): only \((A,h,l_3)=(1,2,1)\).
- \(L=2\): only \(A=1,h=3\text{ or }4\); \(A=3,h=5\); or \(A=5,h=5,l_3=2\). In every surviving profile no part has four degree-two vertices.

For \(L=1\) the single row outside \(D\) must be incident to both high edges. Bad rows have high degree at most one, and there is no high pair with two good rows (it would use both outside \(D\)). The two bad rows \(a,b\) therefore attach to the same good row \(f\). Both are in \(D\), so (4) yields \(d\ge4\). The \(d-1\) other rows through \(f_k\) share the three specified vertices of (3). All of their pairs are high (there is no medium pair left and none intersects in five), making a high triangle, contradiction.

For \(L=2,A=1\), every high edge touches the single row outside \(D\), impossible since \(h>2\). For \(A=3,h=5\) there must be a high pair with both endpoints good (at most four other high pairs). Such a pair uses two rows outside \(D\) and neither endpoint can have another high neighbor, since that would force a medium pair incident to a good row. The one remaining row outside \(D\) has high degree at most two, so \(h\le3\), contradiction.

It remains \(A=5,h=5,l_3=2\). There is exactly one high good–good pair: there must be at least one, while two would use four rows outside \(D\) and leave only one row to support the other three high pairs. Thus the four remaining high pairs all touch bad rows. The two medium pairs must be disjoint, and the high graph on their four endpoints must be either empty with four outside attachments, or the full \(K_{2,2}\). The good–good pair has already used two of the five rows outside \(D\), leaving only three.

**Four outside attachments.** For either medium pair its two bad rows are attached to distinct good rows or to a single good center. Distinct attachments cost two rows outside \(D\) (both bad endpoints), and a center costs one (the good center), by the two cross comparisons above. Both pairs cannot attach separately. If exactly one pair attaches separately, the centered pair has both bad endpoints in \(D\) because all three remaining non-\(D\) slots have been used. Its group through \(f_k\) from (3) then has at least three rows, all sharing three vertices. Since the high graph has no triangle, a group of at least three such rows must have exactly three and contain the other medium pair and one common high neighbor of that pair. This contradicts separate attachments. If both pairs are centered, at least one has both bad endpoints in \(D\) (its two distinct centers use two of the three slots). Its group through \(f_k\) therefore has exactly three rows consisting of the other pair and its center, and \(d=4\). That group shares three degree-four vertices by (3). These are exactly the three common positions of the second medium pair, so \(R=12\) for that centered pair. At least one of its bad endpoints is in \(D\), whence \(s=2\) or \(t=2\); the other terms \(d,s,t\) are all at most 8. Thus \(d+s+t\le18\), contradicting (4), which requires 20.

**Internal high square.** Denote its opposite medium pairs by \(a,b\) and \(c,d'\). The four rows share the three common positions of \(a,b\), and on the other three positions \(a=(a_1,a_2,a_3), b=(b_1,b_2,b_3)\). We can put \(c=(a_1,b_2,c_3)\) with \(c_3\) a third value. Since \(c,d'\) also differ in all three positions, and \(d'\) is high to \(a,b\), up to exchange of roles there are two forms:
\[
 d'=(b_1,a_2,d_3)\quad\text{or}\quad d'=(d_1,a_2,b_3),
\]
where \(d_1,d_3\) are third values and \(d_3\ne c_3\) in the first form. In the first form any degree-two coordinate among the four rows is the third, since each other coordinate is shared in a high pair. Cross comparison gives
\[
 d(b_2)=d(a_3)+1=d(d_3)+1,\quad
 d(a_2)=d(c_3)+1=d(b_3)+1,\quad
 d(b_1)=d(a_3)+1=d(c_3)+1.
\]
For example, comparing \(a,c\), the only exceptional rows \(b,d'\) use \(b_2\) and \(a_2\), respectively, and not the third-coordinate vertices of \(a,c\). These equalities force the four third-coordinate degrees equal. If they are two, that part has four degree-two vertices; if not, all four rows are outside \(D\). Both are impossible.

In the second form the sole possible degree-two positions for \(a,c\) are third and for \(b,d'\) first, again because of shared high positions. In the comparison \(a,d'\), neither exceptional row \(b,c\) uses either \(a_3,d_1\); they are crossed and therefore have equal degree, not two. In the comparison \(b,c\), neither exceptional row \(a,d'\) uses \(b_1,c_3\); these too have equal degree, not two. So all four rows are outside \(D\), contradiction. This closes all \(L\le2\).

## 4. Coupling the tables by the degree-two incidence budget

Among the 576 profiles, only 156 have \(F\ge3\). They all have exactly six active vertices per part and \(A=1\) or 3; this is an output, not an assumption on the input.

For every vertex \(x\) of degree at least three,
\[
 d(x)-A\ \le\ \sum_{y:\,d(y)=2}c(x,y)\ \le\ d(x).
\tag{5}
\]
The sum counts those incident edges of \(x\) containing a degree-two vertex exactly once, so its complement is at most \(A\). Unlike the earlier pair tests, these constraints couple all five other parts at \(x\).

Use the same unit increments per codegree as above. Let \(0\le u_j\le1\) be the increments, \(C\) their cost vector, \(V u=v\) the equality margins, and \(T u\le t\) the two bounds at each vertex from (5), all after subtracting lower codegrees. A rational lower certificate is any \(\lambda\), \(\eta\le0\); its value including the cost \(B_0\) of the lower codegrees is
\[
 B_0+\lambda^Tv+\eta^Tt+
 \sum_j\min\!\left(0,C_j-(V^T\lambda)_j-(T^T\eta)_j\right)
 \ \le\ B .
\tag{6}
\]
This follows by equality, the sign of \(\eta\), and the box bound on each \(u_j\). Integral codegree tables satisfy the relaxation, but the proof does not assume its optima integral. The verifier reads 156 rational certificates of denominator at most 2 and recomputes all terms independently. No reliance on a numerical solver or a feasibility tolerance remains.

The only two profiles whose certificate permits \(L\ge3\) are as follows. Write
\[
 P=(3,3,3,3,3,8),\quad Q=(2,3,3,3,4,8),\quad
 R=(2,2,2,3,7,7),\quad R'=(2,2,2,3,6,8).
\]
For \(P,P,Q,R,R,R\) one has \(E=21,L\le4\); for \(P,P,Q,R,R,R'\) one has \(E=22,L\le3\). Both have \(|D|=20\).

## 5. The last two profiles

An edge in \(D\) incident neither to medium nor to high pairs has vertex-degree sum exactly \(6+22=28\). In the first profile every ordered degree signature of sum 28 with exactly one degree-two vertex must use the unique degree-four vertex in the part \(Q\). Indeed relative to baseline \((2,3,3,3,3,3)\), the required increase is 11; without the degree-four vertex only increases 4 and 5 are possible in the available parts, and \(4b+5a=11\) has no nonnegative solution. Thus at most four edges in \(D\) can be ordinary to all others. In the second profile the only additional possibility is that the degree-two vertex is in \(Q\); the short Cartesian product checks this explicitly in the verifier. Alternatively, without degree four and with the degree-two position outside \(Q\), the unique degree-six option can contribute 3, requiring two contributions of 4, but then the degree-two position must be in \(Q\) (at a pole in any of the last three parts, either one of those 4's or the 3 is absent). A contribution of 5 by the last part also cannot complete 11. So there are at most six fully ordinary edges in \(D\) in the second profile.

Therefore at least 16, respectively 14, edges of \(D\) must be touched by a high or medium pair. But each high pair touches at most one edge of \(D\), and each medium pair at most two. By (1) \(h\le\lfloor E/3\rfloor=7\) in both profiles. The touched counts are consequently at most \(7+2\cdot4=15\) and \(7+2\cdot3=13\). Both contradict the lower bounds. This completes the theorem.

**Replay.** Run `python3 -B verify_ryser_six_twenty_three_edges.py` for the prior residual facts and then `python3 -B verify_ryser_six_twenty_four_edges.py` for the present enumerations, exact min-cost certificates, rational coupling certificates, and final signature checks. The checker uses the standard library only. The high/medium geometric case arguments in Sections 2–3 are proved explicitly above.
