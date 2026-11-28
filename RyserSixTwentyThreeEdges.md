# A twenty-three-edge necessary condition for rank-six Ryser counterexamples

**Theorem.** A finite intersecting six-partite six-uniform hypergraph with cover number six has at least 23 distinct edges, without any upper bound on the number of vertices in a part. Moreover, if it has 23 edges, its maximum degree is at most eight.

This excludes the previously remaining 19-, 20-, 21-, and 22-edge cases of the repository's [nineteen-edge bound](../../ryser-rank-six/NINETEEN_EDGE_BOUND.md). It does not settle the 23-edge case, prove the rank-six conjecture, or apply to general six-uniform hypergraphs without partiteness. No priority claim, resolution for arbitrary matchings, or Lean formalization is made.

Discard duplicate edges, which do not affect the cover number. Let \(H\) be a candidate with \(\tau(H)=6\) and \(N\le23\), let \(E(v)\) denote the edges containing \(v\), and write \(d(v)=|E(v)|\). Only active vertices are counted. Each part is itself a cover, so it has at least six active vertices. Each active degree is at least two: if \(v\) lies only on edge \(e\), then \(e\setminus\{v\}\) covers all edges. Thus \(N\ge12\).

## 1. Two small residual facts

Every intersecting family of at most six edges has a three-cover by pairing the edges. This remains true for seven six-partite edges: a vertex of degree at least three leaves at most four edges, and otherwise the six parts account for at most \(6\lfloor7/2\rfloor=18<21\) pairs of edges.

A six-partite intersecting family \(J\) with eight edges and cover number four has at least five parts with exactly four active vertices. This is the portion of the eight-edge structure in [Abu-Khazneh and Pokrovskiy, Lemmas 2.1 and 2.8](https://arxiv.org/abs/1409.4938) used here. For an independent finite replay, the entire small argument is as follows:

* The maximum degree is at most three, since a vertex of degree four and two paired vertices cover all edges. Any two degree-three stars meet: otherwise their vertices and a common point of the two remaining edges cover all eight. Thus there is at most one degree-three vertex per part. Every edge belongs to a degree-three star, since six degree-two or degree-one vertices cannot meet seven other edges.
* Number the eight edges as rows. If there are \(t\) degree-three stars, the other blocks in a part have size one or two. A part with a triple can cover at most five pairs of rows (three in the triple and two outside it); a part without a triple can cover at most four. Accounting for all 28 row pairs requires \(t\ge4\), with at most \(t-4\) repeated pair incidences. In particular the triples alone have at most that many repetitions.
* The attached integer checker enumerates triples of row labels, relabeling one to \(\{0,1,2\}\) and sorting the rest. For \(t=4\), it finds no pairwise-meeting, spanning triple list with zero repeats. For \(t=5\), there are exactly 900 triple lists satisfying the necessary conditions, all with one repeat. Each would need every one of the 14 remaining pairs in the matchings outside the five triples and in the part without a triple (five two-pair matchings and one four-pair matching). Recursing on the smallest available row, allowing either omission or a permissible partner, finds no such completion. For \(t=6\), the same triple test with repeat bound zero finds none.
* Therefore there are six triples and they account for at most 17 distinct pairs. At least 11 of the remaining size-two blocks are necessary, and there are at most two in each part. At least five parts consequently have block sizes \(3,2,2,1\).

It follows that **any two vertices of \(H\) leave at least nine edges**. At most seven would give a five-cover by the first fact. If exactly eight remain, they form a family \(J\) with \(\tau(J)=4\): the two vertices have already been used, and four suffice by pairing. The five parts just identified together lack at least ten vertices of \(H\). Excluding the two selected vertices leaves at least eight missing vertices, all of degree at least two in \(H\). Their at least sixteen incidences are entirely in removed edges. Each removed edge \(e\) hits every edge in \(J\); so \(e\cap V(J)\) has size at least four. The edge \(e\) also contains at least one of the two selected vertices, outside \(V(J)\). Thus it can contain at most one of the additional missing vertices. There are \(N-8\le15\) removed edges, a contradiction.

We will also use that any six-partite intersecting family with cover number at least five has at least 13 edges, the lower half of the known result \(f(6)=13\) ([Aharoni, Barát and Wanless, Theorem 2.7](https://arxiv.org/abs/1409.4833), and [Abu-Khazneh and Pokrovskiy, Theorem 1.1](https://arxiv.org/abs/1409.4938)). Here is a short derivation using the seven-edge fact. At most eight edges can be paired. In a family of 9 or 10 edges with no four-cover the maximum degree is at most two (deleting the incident edges leaves at least eight necessary edges to avoid a three-cover); then the six parts supply at most \(6\lfloor N/2\rfloor\) pairs, fewer than \(\binom{N}{2}\). For 11 edges the maximum degree is at most three and the same part cannot have three degree-three vertices (use them and pair the last two edges). Each part accounts for at most eight pairs, fewer in total than 55. For 12 edges the maximum degree is at most four. In a part without a degree-four vertex there may be at most three degree-three vertices, giving at most ten pairs. A part with a degree-four vertex has no second degree-four vertex (they would leave four edges) and at most one degree-three vertex (two with the degree-four vertex would leave two edges). Thus every part supplies at most eleven pairs. All six must attain eleven, and every pair of edges must meet exactly once because \(6\cdot11=\binom{12}{2}\). The six degree-four vertices are in different parts and any two must belong to one edge, or their disjoint stars would leave four edges. Some edge contains at least three such vertices, because their fifteen pairs cannot lie on twelve distinct edges if each edge contains at most two. Those three degree-four stars meet pairwise only on that edge, covering ten edges together. One additional vertex meets the remaining pair, a contradiction.

## 2. A stronger one-vertex degree cap for \(N\le23\)

Delete all edges through \(x\), leaving an intersecting family \(J\) with \(m=N-d(x)\) edges and cover number at least five. Every removed edge contains \(x\), and its intersection with \(V(J)\) is a cover of \(J\), so it consists of exactly five vertices and omits no other vertex of that edge. Hence the active vertices of \(J\) are precisely the active vertices of \(H\) other than \(x\). Five parts have at least six active vertices and the part of \(x\) has at least five.

A five-cover of \(J\) contains at most one degree-one vertex of \(J\): two such vertices can be replaced by one, using a common vertex of their unique edges if those edges are different. Every degree-one vertex of \(J\) belongs to some removed edge, since its degree in \(H\) was at least two. Thus \(J\) has at most \(d(x)\) degree-one vertices. Also its maximum degree is at most \(m-9\) by the two-vertex residual bound. In a part of \(J\) the sums of its two, three, or four highest degrees are at most \(m-5,m-3,m-1\), respectively: otherwise pairing the remainder (or using its emptiness) gives a four-cover.

The previous section gives \(m\ge13\). For \(m=13\), since \(d(x)\le10\), the partition check in the script bounds
\[
S_J=\sum_{v\in V(J)}\binom{d_J(v)}2\le70<78.
\]
For \(m=14\), \(d(x)\le9\). The check sums three integer statistics from each part: the number of degree-one vertices, the contribution to \(S_J\), and the number of degree-five vertices. At \(S_J\ge91=\binom{14}2\) the only possible triples are
\[
(8,91,6),\quad(9,91,5),\quad(9,91,6),\quad(9,92,6).
\]
These are only numerical possibilities. If \(S_J\le92\), at most one unordered pair of vertices of \(J\) has codegree at least two: counting common vertices over pairs of edges, there can be at most one pair of edges meeting twice, and none meeting three or more times. On the other hand any three degree-five vertices of \(J\) have a pair of codegree at least two. Indeed two degree-five stars cannot be disjoint because that would leave just four edges, giving a four-cover. If all three pairwise codegrees equal one, their union covers \(15-3\) or \(15-3+1\) edges, and the remaining at most two edges require at most one further vertex. Since there are at least five degree-five vertices, some triple can avoid the only possible repeated pair. This contradiction excludes \(m=14\). Thus \(m\ge15\) for every \(x\).

## 3. A stronger pressure on repeated intersections

An edge of \(H\) cannot contain two degree-two vertices: discard them from the edge and the remaining four vertices leave at most two edges, which can be covered by one vertex. Nor can an edge contain four vertices of degree at most three: choose the other two vertices and observe that the number of edges avoiding them is at most \(\sum_{i=1}^4(d_i-1)\le8\), contradicting the two-vertex residual bound. Globally, writing \(D_2\) for the incidence count at degree two and \(D_{\ge4}\) for the incidence count at degrees at least four, we therefore have
\[
D_2\le N,\qquad D_{\ge4}\ge3N.
\]

If two distinct edges meet in five vertices, those five vertices cover \(H\): an edge avoiding them would have to contain both distinct remaining vertices, which lie in the same part. Thus the intersection sizes \(s(e,f)\) lie in \(\{1,2,3,4\}\). Set \(S=\sum_v\binom{d(v)}2\) and let \(c(v,w)=|E(v)\cap E(w)|\) for distinct vertices. Double counting, with the sum over pairs from different parts, gives
\[
S=\sum_{e<f}s(e,f),\qquad
B=\sum_{v<w}\binom{c(v,w)}2=\sum_{e<f}\binom{s(e,f)}2.
\]
Since \(s(s-1)\le4(s-1)\), a necessary condition is
\[
2B\le4\big(S-\tbinom N2\big).
\]

For a degree-\(x\) vertex and a different part of degrees \(y_1,\ldots,y_k\), its codegree row \(c_j\) satisfies \(\sum_j c_j=x\) and
\[
\max(0,x+y_j-N+9)\le c_j\le
\begin{cases}
0 & (x=y_j=2),\\
\min(x,y_j)-1 & \text{otherwise}.
\end{cases}
\]
The lower bound is inclusion–exclusion with at least nine edges avoiding the two vertices. The upper bound, apart from the already noted degree-two case, is because a codegree equal to one of the degrees gives a star contained in the other. Indeed if \(v\)'s whole star lies in \(w\)'s, take an edge \(e\) through \(v\); then \(e\setminus\{v\}\) is a five-cover, including \(w\).

Minimize \(\sum_j\binom{c_j}2\) over these integer bounds and row sum. This can be done by adding the residual units in least marginal-cost order, starting at the lower-bound vector: raising a cell from \(a\) to \(a+1\) costs \(a\), so choosing the lowest available marginal cost always achieves the lowest total (increments in each cell are nondecreasing and consumed in prefix order). The checker independently confirms each row minimum by bounded integer composition. For a pair of parts the larger of the sums of the individual row minima taken in the two orientations is a lower bound on that pair's total. Its sum \(B_*\) over the 15 pairs of parts satisfies \(B_*\le B\); the two orientations are not added. If some row is infeasible, the part pair is impossible. No assumption that the row minima are simultaneously attained is needed.

## 4. Exact finite closure through 22 edges

A sorted part pattern is a partition of \(N\) into at least six integers in \([2,N-15]\) whose top two sum to at most \(N-9\), since same-part stars are disjoint. The checker enumerates these patterns by choosing each next integer between the last integer and the floor of the remaining sum divided by the remaining length. It takes all unordered six-part multisets and imposes \(D_2\le N,\ D_{\ge4}\ge3N,\ S\ge\binom N2\). None has an infeasible pair after these filters in this computation. Counts and maxima of \(F=4(S-\binom N2)-2B_*\) are:

| \(N\) | Part patterns | Filtered multisets | Maximum \(F\) |
|---:|---:|---:|---:|
| 12–17 | 0 at each \(N\) | 0 | n/a |
| 18 | 4 | 0 | n/a |
| 19 | 9 | 0 | n/a |
| 20 | 22 | 0 | n/a |
| 21 | 35 | 0 | n/a |
| 22 | 57 | 171 | \(-10\) |

The whole finite certificate is standard-library Python. There are no floating-point tolerances, SAT-status claims, or structural assumptions on the size of any part besides those proved above. Run both `python3 -B verify_ryser_six_twenty_three_edges.py` and `python3 -B -O verify_ryser_six_twenty_three_edges.py`; explicit checks remain active in the optimized run. This proves the edge bound, and the degree cap at 23 is \(23-15=8\).

## Relation to earlier results

The older repository proof used scalar lower bounds on independent codegrees and excluded at most 18 edges. The new constraints combine the small residual-family obstruction, the global scarcity of degree-two incidences, and codegree rows with specified sum. The linked \(f(6)=13\) result concerns cover number **at least five**, not six; the present statement concerns the latter. [Francetić, Herke, McKay and Wanless](https://arxiv.org/abs/1508.00951) rule out linear intersecting counterexamples through rank nine; the present bound permits arbitrary intersection multiplicities. The conclusion is separate from the Erdős–Lovász lower bounds for the larger class of general intersecting uniform families, and from large-rank multipartite constructions. The degree constraints do not by themselves certify existence or nonexistence at 23 edges.
