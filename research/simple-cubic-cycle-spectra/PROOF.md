# The complete cycle-count spectra of simple 2-connected cubic graphs, with and without planarity

**Computer-assisted theorem.** For finite undirected simple 2-connected cubic graphs, the positive integers that do **not** occur as the total number of simple cycles are precisely the following 41 integers:
$$
1\text{–}6,\quad 8\text{–}13,\quad 16\text{–}21,\quad 23\text{–}25,\quad
27,\quad31\text{–}37,\quad40,\quad43\text{–}45,\quad48,\quad58,59,62,64,68,75,115.
$$
With planarity required, the exceptions are the same 41 together with these 15:
$$
15,29,42,51,54,56,67,70,78,86,90,107,112,123,131.
$$
In particular all integers above 115 occur without requiring planarity and all integers above 131 occur in planar graphs. We count an undirected cycle once, regardless of starting point or orientation. At intermediate *multi*graphs a pair of parallel edges forms one cycle; the final witnesses have no loops or parallel edges. No claim on the 3-connected classes is made.

McCulloch, McKay, Salahshoori and Zaslavsky, [*The Cycle Counts of Graphs*](https://doi.org/10.1007/s00373-026-03047-3), *Graphs and Combinatorics* **42**, 53 (2026), §6(b,d), proposed finite exception lists. Relative to the printed (b) list the general census adds 16–21. Relative to the printed (d) list (including all of (b) as printed and (d)'s own 15–21), the planar census adds 42. No printed occurrence data underlie the proof. Their Theorem 1 itself already excludes 16 for every inseparable graph; their Theorem 2 concerns cubic **multigraphs**. We use their reference to (b) to read (d) as the simple planar cubic subclass.

The proof has three disjoint ranges: exhaust all possible witnesses with at most 131 cycles, exhibit literal positive witnesses for every integer 132 through 2678, and apply the previously proved explicit [analytic construction for every integer at least 2679](../simple-cubic-prescribed-cycle-count/PROOF.md). Only the last step relies on that preceding result. None of the finite computations presupposes a vertex cutoff for the set of all simple graphs.

## Exhausting the small range

1. **Closure from the theta multigraph.** Start with two vertices joined by three separate edges. Select two distinct points in edge interiors, in either two distinct edge occurrences or the same occurrence. Subdivide at both points and join the new vertices by a fresh edge. In the same-edge case one segment of the subdivided old edge becomes parallel to the fresh edge, which is permitted in the census. In the distinct-occurrence case the two chosen edges may already be parallel. The operation produces a loop-free cubic multigraph two vertices larger. It preserves inseparability: the subdivision of a non-bridge in an inseparable graph is inseparable, and adding an edge does not introduce a cut vertex. This also holds for the initial three-edge theta multigraph.

   Every simple 2-connected cubic graph comes from the theta by a sequence of these operations up to isomorphism. For clarity, the requisite open-ear argument is short. Start with a cycle. If not all vertices of the final graph are present, any component outside the current 2-connected subgraph attaches to it at two or more distinct vertices (otherwise the unique attachment would be a cut vertex of the final graph). Adjoin a path between two such vertices with interior in that component; once spanning, add unused edges singly. Each addition preserves 2-connectivity, and the process reaches the whole finite graph. The first ear plus the cycle is a subdivision of the theta. At each later step the two endpoints of the ear have degree two *before* the addition, since all final degrees are three. In the cubic core of the previous prefix they therefore project to two distinct positions in the interiors of edge occurrences. The internal degree-two vertices of the new ear suppress to the new edge; the endpoints become degree three and remain distinct. Same-edge positions are covered regardless of their order, by renaming the two new vertices. No assumption that ear endpoints were adjacent in the previous graph is made; arbitrarily long initial paths are absorbed into subdivisions. Finally the cubic host has no degree-two vertices to suppress.

2. **Exact monotone count and safe discard.** Subdividing does not change the old cycle count; there is an edge-preserving bijection after smoothing vertices of degree two. The new cycles are in bijection with the simple paths between the new vertices in the subdivided graph before inserting the ear. The paths distinguish actual parallel edge occurrences. This is the Ear–Path Lemma (Lemma 4 of McCulloch et al.). At least one such path exists, so an intermediate graph with more than 131 cycles cannot lead to any target at most 131 and a graph with exactly 131 need not be extended. A depth-first count may stop immediately after the number of new paths exceeds the remaining budget. There is **no** simplicity-based pruning, assumed maximum order, or lower-bound estimate depending on the order or cycle rank.

3. **Exact enumeration modulo isomorphism.** `census.cpp` carries each graph as an unordered-endpoint edge list with all multiplicities retained. For edges of different endpoint-pair types it tries their two types; edge occurrences identical up to permutation give isomorphic children. For one type it tries a repeated choice of the *same* edge, and also two distinct copies if multiplicity is at least two. Thus every operation in step 1 is examined up to relabeling. Where candidate children are grouped by a distance-layer invariant, a hash collision does not discard anything. The final test tries injective maps compatible with all already mapped multiplicity-matrix entries, including zeros. Only a complete matching permutation discards a representative as isomorphic. The three-edge seed has three digons.

4. **Termination and counts.** The run advances by two vertices, exhausts the next generation of all eligible children, and stops on the empty generation. It would abort, not succeed, if the fixed array capacity were exceeded. The following table is the actual generation size, followed by simple representatives and their verified planar counts, for cycle budget 131. The final generation at order 28 has no simple representatives and produces no child within budget.

|Order|All eligible cores|Simple|Simple planar|
|---:|---:|---:|---:|
|2|1|0|0|
|4|2|1|1|
|6|5|2|1|
|8|16|5|3|
|10|66|18|8|
|12|365|81|29|
|14|1818|96|56|
|16|3482|61|45|
|18|4338|43|34|
|20|4806|27|22|
|22|4756|10|9|
|24|3872|6|6|
|26|3028|1|1|
|28|552|0|0|

5. **Planarity certificates and second cycle count.** There are 351 simple representatives. `planar.py` finds 215 orientable rotations of Euler characteristic two and 136 explicit subgraphs homeomorphic to the nonplanar graph `K3,3`. A separate checker consumes these as *witnesses*, not as claims about the completeness of the planarity-finding heuristic. In a rotation certificate it checks one cyclic permutation of the three actual neighbors at each vertex and computes the number of face boundary walks by the edge-reversal/next-neighbor rule. The connected orientable surface obtained by capping those faces has Euler characteristic two and hence is a sphere. In the other certificate it checks that each marked edge belongs to the input, suppresses vertices of degree two in the marked subgraph, then tests equality to a simple complete bipartite graph with parts of size three. Each outcome is thus verifiable without invoking planarity software. Applying the tests to the sole representative having 42 cycles yields a `K3,3` subdivision, not a planar embedding.

   The separate `witness_check.cpp` also tests cubicity, simplicity, connectivity after every one-vertex deletion, and the cycle count of each literal graph. A spanning tree gives a binary fundamental cycle basis; Gray-code enumeration visits every vector in its span. In a cubic graph, every nonempty vector describes a disjoint union of cycles (all degrees are zero or two); it is a single cycle exactly when traversing one component exhausts its edge set. Thus the second check for cycle counts does not use the increment in step 2. The two verified finite spectra are printed in full in `WITNESSES.txt`.

## Filling the positive middle range without any outside occurrence table

For every integer 132 through 2678 inclusive, `cover.py` and `emit.py` construct one explicit graph from two of the small planar representatives with one edge removed from each. Zero or more wraps add two vertices and a bypass; two new edges join the two poles to close the graph. The construction merely helps find witnesses: **verification does not need its counting formulas**. The materializer writes every graph's complete edge list and rotation. The independent checker tests uniqueness and full interval coverage of all 2547 target labels, simplicity, cubicity, 2-connectivity, sphere embedding and direct cycle-space count separately for every graph. The largest witness here has only 26 vertices. No unavailable graph or computation from the original authors is used. Coupled with the analytic theorem at 2679, this proves both spectra.
