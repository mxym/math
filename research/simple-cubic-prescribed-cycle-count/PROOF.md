# A cofinite construction for cycle counts of simple 2-connected planar cubic graphs

**Theorem.** Every integer k≥2679 is the number of (undirected, simple) cycles of a simple, 2-connected, planar, cubic graph. The construction is explicit and uses O(√k) vertices. Neither the threshold nor the size order is asserted optimal. No 3-connectivity is claimed.

McCulloch–McKay–Salahshoori–Zaslavsky, [*The Cycle Counts of Graphs*](https://doi.org/10.1007/s00373-026-03047-3), §6(b,d), give finite computational observations and ask whether additional cycle counts are missing. The construction below gives an unconditional analytic tail for both classes; its proof uses neither printed finite list. We claim no full occurrence statement outside either proposed list and infer no additional cases below 2679 from that source. Indeed the printed (b) positive assertion is inconsistent at 16 with the authors’ Theorem 1. We interpret (d) as the simple planar subclass in view of its reference to (b) and the distinct multigraph Theorem 2. Separate finite checks are in progress, not certified here. No 3-connectivity is asserted.

## Graph operations

A pole H here is a finite connected simple plane graph with two distinct terminals s,t on the same face. Both terminals have degree two; all other vertices have degree three. Require that every vertex belongs to some simple s-to-t path. Let p(H) be the number of simple s-to-t paths and c(H) the number of cycles. Put e(H)=p(H)(p(H)−1)/2−c(H). We use the actual plane embeddings merely to show planarity of constructions.

Use fresh disjoint copies of all poles. Their parallel composition H⊕J adds a new terminal x adjacent to both left terminals, and a new terminal y adjacent to both right terminals. If each original pole is drawn in a disk with its terminals at the two ends, use two disjoint strips between x and y. This gives the required common outside face. The new graph is simple and has the required degrees; any vertex on an old terminal path lies on a new one. A new terminal path chooses exactly one old branch, so p=p(H)+p(J). Cycles are either old or consist of a full terminal path through each of the two branches. Thus c=c(H)+c(J)+p(H)p(J), and

    (p,e)(H⊕J) = (p(H)+p(J), e(H)+e(J)).                        (1)

A wrap U(H) adds new terminals x,y and the three edges xs, ty, xy. It places a direct wire in parallel with a **genuine pole**; this operation never adds parallel graph edges since x and y are new. It preserves all pole properties. It sends (p,c) to (p+1,c+p), equivalently (p,e) to (p+1,e).

The closing operation takes H and a disjoint diamond X=K₄ minus an edge (with the ends of that edge as its two terminals). Join their left terminals and their right terminals by one edge each. The resulting graph is simple, cubic and planar: join two disk drawings across their boundaries. It is 2-connected as well. Indeed after removal of an internal vertex of H, each surviving vertex of H can reach at least one terminal along a segment of a pre-existing simple terminal path avoiding the deleted vertex, and both terminals are connected through X. After removal of a terminal of H, every surviving vertex of H reaches its other terminal by the same path argument; X is connected to that terminal. The argument is symmetric for deletion in X. Cycles in the closed graph stay in one of the poles or traverse a terminal path in each. Since p(X)=4 and c(X)=3, the number of cycles is

    k = c(H)+3+4p(H) = J(p(H))+3−e(H),   J(p)=p(p+7)/2.        (2)

The outside may have separating vertex pairs; this is the step that supplies 2-connectivity, not 3-connectivity. The terminal-path condition does not assume an entire path is spanning.

## Three finite coins

Deleting an edge st from a simple 2-connected plane cubic graph whose vertices each lie on a cycle through st yields an admissible pole: removal merges the adjacent faces so both ends are cofacial; a cycle through st becomes a terminal path. In particular this holds if st is on a Hamilton cycle. Use X as above and the triangular prism with either a triangle edge or a vertical matching edge deleted. Each of those edges occurs on a Hamilton cycle (the prism is symmetric on each edge type; a Hamilton cycle uses both types). The two triangles of the prism are cycles. Any other cycle uses exactly two of the three vertical edges and one of the two possible paths in each triangle between the chosen endpoints. Thus the prism has 2+3·4=14 cycles. Each vertical edge is in 2·4=8 of them. For a fixed top triangle edge, it is in the triangle and, for each of the three pairs of vertical edges, exactly one of the two top paths and either of the two bottom paths can be chosen, hence 1+3·2=7. A terminal path in an edge-deleted graph is exactly a former cycle through that edge. The diamond counts follow by listing two routes of length 2 and two of length 3; the remaining cycles are the two triangles and a quadrilateral. Consequently the coins (p,e) are

    A (diamond)        (4,3)
    B (triangle edge)  (7,14)
    C (vertical edge)  (8,22).

For each r in [20,41], the table gives counts of A,B,C with combined deficit r. Each triple uses total terminal-path count at most 44, by (1).

    r       20 21 22 23 24 25 26 27 28 29 30
    A        2  7  0  3  8  1  4  9  0  5 10
    B        1  0  0  1  0  0  1  0  2  1  0
    C        0  0  1  0  0  1  0  0  0  0  0

    r       31 32 33 34 35 36 37 38 39 40 41
    A        1  6 11  2  7  0  3  8  1  4  9
    B        2  1  0  2  1  1  2  1  1  2  1
    C        0  0  0  0  0  1  0  0  1  0  0

For every e≥20 write e=r+22q with r∈[20,41] and q≥0. Use that row and q additional C-coins, parallel-composing any two until only one pole remains. This gives exactly e at a path count no greater than

    44+8q ≤ 44+4(e−20)/11.                                      (3)

There is always a genuine coin; no empty parallel network or multiple wire is needed.

## Closing exactly at the target

Given k≥2679, choose the smallest nonnegative p with J(p)+3−k≥20 and call that difference e. Since J(70)=2695, p≥71. Consecutive J values differ by p+3. Minimality and integrality therefore give 20≤e≤19+p+3=p+22. By (3), the path cost is at most 44+4(p+2)/11≤p, the last inequality being 492≤7p. Add as many wraps as necessary to make the path count exactly p without changing e. Equation (2) now gives precisely k cycles. Each coin, each join and each wrap uses a bounded number of vertices; the number of coins and wraps is O(p). Since J(p−1)+3<k+20, p=O(√k). This completes the constructive proof.
