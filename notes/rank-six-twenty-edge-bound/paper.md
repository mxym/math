# A twenty-edge necessary condition for a rank-six Ryser counterexample

Research continuation, 7 October 2026. This strengthens the repository's
nineteen-edge necessary bound. It is a finite obstruction and does not
solve Ryser's conjecture or claim mathematical priority.

## 1. Statement and prior input

**Theorem.** Every finite simple intersecting six-partite six-uniform
hypergraph with at most nineteen edges has a vertex cover of size at
most five. Thus any rank-six intersecting counterexample to Ryser's
bound needs at least twenty distinct edges.

Each edge contains exactly one vertex from each of six specified parts.
There is no upper bound on part sizes. Vertices outside the union of
edges are ignored. We use the established lower half of \(f(6)=13\),
with a complete elementary proof included in Appendix A:

**Input F.** Every intersecting six-partite six-uniform hypergraph with
at most twelve edges has a cover of size at most four.

Here \(f(6)\) is the minimum edge count under \(\tau\ge5\), not the
minimum under \(\tau=6\). Input F was proved by
Abu-Khazneh--Pokrovskiy [AP, Theorem 1.1, Section 2.1], and independently
by Aharoni--Barát--Wanless [ABW]. AP's twelve-edge proof is a hand
classification, with the earlier \(f(6)\ge12\) bound of
Mansour--Song--Yuster as an input. Its Lemma 2.9 is written for
\(\tau=5\); its same greedy bounds and low-degree pair count also
exclude \(\tau=6\) at twelve edges. Appendix A instead reproduces
the short ABW twelve-edge argument and supplies the at-most-eleven
reduction explicitly. No linearity assumption, solver certificate
or external unproved lemma is needed by the full note.

## 2. Degrees and the small-excess reduction

Suppose \(H\) is a counterexample, with \(N\le19\) distinct edges.
Any edge is a six-cover, so \(\tau(H)=6\). Every part has at least
six active vertices. Every active vertex has degree at least two:
if \(v\) belonged only to \(E\), then \(E\setminus\{v\}\) would
meet every edge and be a five-cover.

If a vertex has degree \(d\ge N-12\), deleting its incident edges
leaves at most twelve edges. Input F covers the remainder with four
vertices, giving a five-cover of \(H\). Consequently
\[
 \Delta(H)\le N-13. \tag{1}
\]
Fixing an edge and counting other edges through its six vertices gives
\[
 N-1\le6(\Delta-1)\le6(N-14),
\]
so \(N\ge17\).

Let
\[
 S=\sum_v\binom{d(v)}2
   =\sum_{\{E,F\}}|E\cap F|,\qquad
 I=S-\binom N2\ge0. \tag{2}
\]
In each part its positive degrees sum to \(N\), have at least six
entries and lie between two and \(N-13\). For \(N=17\), this
part energy is at most 18; for \(N=18\), at most 24. One direct
bound is the chord inequality
\[
 \binom d2\le1+\frac{M+1}{2}(d-2),\quad 2\le d\le M,
\]
which follows from \((d-2)(M-d)\ge0\). For a part with \(u\ge6\)
entries this gives energy at most \((M+1)N/2-Mu\). With
\((N,M)=(17,4)\) the bound is \(18.5\), hence at most 18 by
integrality; with \((N,M)=(18,5)\) it is 24. Therefore
\[
 S\le108<\binom{17}2\quad\hbox{or}\quad
 S\le144<\binom{18}2,
\]
contradicting (2). Only \(N=19\) remains, with \(\Delta\le6\).

For this case a part with \(u\) entries has \(19-2u\) units of
excess above two, each entry allowing at most four units. Convexity
maximizes the sum of squared excesses by filling entries successively
to capacity. Explicitly, transfer one unit from a positive smaller
entry to a larger unsaturated entry: the squared sum increases by
\(2(a-b+1)>0\). This proves the following complete small table:

| active vertices in the part | maximum pair energy, degree at most 6 |
|:--|--:|
| 6 | 29 |
| 7 | 23 |
| 8 | 17 |
| 9 | 11 |

The first maximum is attained by \((6,5,2,2,2,2)\).
If the part has no degree-six vertex, its maximum is 26, attained
by \((5,5,3,2,2,2)\). Hence
\[
 S\le174,\qquad I\le3. \tag{3}
\]
If any part has no degree-six vertex, (2) forces exactly one such
part: two would give \(S\le168<171\). With one, \(S\le171\), so
\(I=0\). The other five parts have degree-six vertices. Their five
incidence blocks have size six and pairwise intersections at most
one, by linearity. Their union has size at least
\(5\cdot6-\binom52=20>19\), a contradiction. Thus choose a
degree-six vertex \(v_i\) in each part, \(i=1,\ldots,6\).

## 3. Four-vertex budgets force an impossible overlap pattern

Let \(B_i\) be the six original edges incident with \(v_i\), and
let \(b_{ij}=|B_i\cap B_j|\). For any four-element
\(A\subset\{1,\ldots,6\}\), their union has size at most 16:
if it covered at least seventeen original edges, the at most two
remaining edges could be covered by one intersection vertex. That
would give a five-cover. The elementary union lower bound therefore
gives
\[
 16\ge\left|\bigcup_{i\in A} B_i\right|
       \ge24-\sum_{\{i,j\}\subset A}b_{ij},\qquad
 \sum_{\{i,j\}\subset A}b_{ij}\ge8. \tag{4}
\]
Sum (4) over the fifteen four-subsets. Every pair occurs in six of
them, so
\[
 \sum_{i<j}b_{ij}\ge20,\qquad
 \sum_{i<j}\binom{b_{ij}}2\ge20-15=5. \tag{5}
\]
The second inequality uses \(\binom b2\ge b-1\) for every
nonnegative integer \(b\), including zero.

Double counting pairs of vertices shared by pairs of original edges
gives
\[
 Q:=\sum_{\substack{\{v,w\}\\v,w\text{ in different parts}}}
       \binom{|B_v\cap B_w|}2
    =\sum_{\{E,F\}}\binom{|E\cap F|}2\ge5. \tag{6}
\]
The lower bound follows from (5) by retaining only the selected
vertices. Under \(I\le3\), the only way to have \(Q\ge5\) is
that exactly one original edge pair shares four vertices and all
other edge pairs share exactly one. Indeed an edge-pair excess
\(j=|E\cap F|-1\) contributes \(j(j+1)/2\) to \(Q\). Total
excess at most three gives at most 4 unless it is the single term
\(j=3\), which gives 6. This is the complete integer list, not a
floating point estimate.

Let \(U\) be the four parts containing the four shared vertices of
that exceptional pair. For any \(i,j\), a value \(b_{ij}\ge2\)
would give two original edges sharing \(v_i,v_j\); that edge pair
must be the exceptional pair. Thus \(b_{ij}\le2\), and a value two
is possible only when \(i,j\in U\). Choose four parts consisting
of the two outside \(U\) and two inside \(U\). Among their six
pairs at most one can have codegree two; all others have codegree
at most one. Their sum is at most seven, contradicting (4).
This finishes the proof. \(\square\)

## 4. The next finite search case

An assumed twenty-edge counterexample satisfies \(\Delta\le7\) by
Input F, every active degree is at least two, and every part has at
least six active vertices. The same convexity calculation gives the
following maxima for one part:

| active vertices | 6 | 7 | 8 | 9 | 10 |
|:--|--:|--:|--:|--:|--:|
| pair energy | 35 | 29 | 22 | 14 | 10 |

Since \(S\ge\binom{20}2=190\), no part can have nine or more
active vertices: even five other maximal parts give
\(5\cdot35+14=189<190\). Thus **eight vertices per part suffice
for the complete twenty-edge case**. At most one part has eight
vertices. If one does, at most one other part has seven; otherwise
at most three parts have seven. These assertions follow by comparing
the deficits from \(6\cdot35=210\) with the budget of twenty.

Deleting any edge from a twenty-edge counterexample leaves nineteen
edges, so the new theorem supplies a five-cover of the remainder.
It must avoid the deleted edge and have exactly five vertices:
otherwise adding one vertex of that edge gives a five-cover of all
twenty edges. This justifies edge-critical search constraints at
twenty edges. It is not a nonexistence theorem for that case.

## 5. Verification and scope

The proof is finite counting, including the prior Input F's full proof.
`check_exact.py` enumerates the complete degree-partition domains
independently, every excess partition up to three, all possible
exceptional four-part supports, and the four-subset incidence count.
It includes an incorrect-energy negative control. The enumeration
is a diagnostic companion to the complete inequalities above, not
an unchecked solver status. Partial Lean exports verify the chord,
integer codegree inequality and scalar budget transfers; they do
not formalize hypergraph covers or the full appendix.

The earlier nineteen-edge package remains unchanged. This note does
not exclude twenty-edge examples, establish the unrestricted rank-six
case, or change the unrelated general Erdős--Lovász edge minimum.
In particular it does not assert a general nonpartite \(g(6)\ge20\).

## Appendix A. The prior twelve-edge four-cover bound

This appendix is attributed to [ABW, Theorem 2.7] for its twelve-edge
classification. These are known ingredients, not claimed as new
results. We give all the reductions needed here so the present
twenty-edge proof has no external mathematical black box.

**A.1. Seven-edge three-cover lemma.** Every intersecting six-partite
family with at most seven edges has a cover of size at most three.
For at most six edges use pairing. With seven edges, a vertex of
degree at least three, followed by pairing the remaining at most
four edges, gives a three-cover. Otherwise all degrees are at most
two. If no three-cover existed, every part would have at least four
active vertices. In a part with total degree seven and at least
four vertices of degrees one or two, at most three vertices have
degree two. Thus the total pair energy would be at most
\(6\cdot3=18<\binom72=21\), a contradiction. \(\square\)

**A.2. At most eleven edges.** Suppose a family has \(N\le11\)
edges and no four-cover. By A.1, \(N\ge8\). Selecting any vertex
and applying A.1 to the remaining edges shows
\(\Delta\le N-8\). A fixed original edge then gives
\(N-1\le6(\Delta-1)\le6(N-9)\), hence \(N\ge11\). So
\(N=11\), \(\Delta\le3\), and every part has at least five active
vertices. For degrees one through three,
\(\binom d2\le3(d-1)/2\). Each part therefore has energy at most
\(3(11-5)/2=9\), and total energy at most
\(54<\binom{11}2=55\). This excludes the assumed family.

**A.3. Twelve edges (ABW's argument).** Suppose \(N=12\) and no
four-cover exists. A.1 shows \(\Delta\le4\), because a degree at
least five would leave at most seven edges. Let \(x_i\) count
degree-\(i\) vertices and \(n\) be the active-vertex count.
Every part has at least five active vertices, so \(n\ge30\).

There cannot be two degree-four vertices in one part: they cover
eight distinct edges with two vertices and leave four edges to pair.
Hence \(x_4\le6\). A part with no degree-four vertex has at most
three degree-three vertices: four would cover all twelve edges.
A part with a degree-four vertex has at most one degree-three
vertex: two together with the degree-four vertex cover ten edges
with three vertices, leaving a pair. Thus
\(x_3\le18-2x_4\). The exact degree identity is
\[
 S=72-n+x_3+3x_4.
\]
Consequently
\[
 66\le S\le42+x_3+3x_4
       \le60+x_4\le66.
\]
All inequalities are equalities. In particular \(I=0\), and there
is exactly one degree-four vertex in each part.

Any two of these six vertices have incident blocks that intersect:
if disjoint, they cover eight edges, and pairing the remaining four
gives a four-cover. By linearity they intersect in exactly one
original edge. The fifteen pairs of high vertices have just twelve
original edges to witness them, so some original edge contains at
least three of the six vertices. Choose three on that edge. Their
size-four incidence blocks meet pairwise exactly in that common
edge, and their union has size \(12-3+1=10\). Selecting the three
vertices and pairing the two remaining edges gives a four-cover,
the final contradiction. This proves Input F. \(\square\)

## References

[AP] A. Abu-Khazneh and A. Pokrovskiy, *Intersecting extremal
constructions in Ryser's Conjecture for r-partite hypergraphs*,
<https://arxiv.org/abs/1409.4938v1>, Theorem 1.1 and Section 2.1.
This source is cited as a preprint; no unverified journal reference
is attached to it.

[ABW] R. Aharoni, J. Barát and I. M. Wanless, *Multipartite hypergraphs
achieving equality in Ryser's conjecture*, Graphs and Combinatorics
**32** (2016), 1--15; <https://arxiv.org/abs/1409.4833v2>,
DOI <https://doi.org/10.1007/s00373-015-1575-9>.

[Previous] The repository's *Nineteen-edge necessary bound*,
the rank-six research document `NINETEEN_EDGE_BOUND.md`, frozen at `db0b1c7`.
Its proof does not use Input F. The stronger conclusion here uses
that external input and a new four-vertex budget obstruction.
