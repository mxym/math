# An order-nine induced-subgraph certificate for Conway's 99-graph

**Theorem.** In a strongly regular graph with parameters (99,14,1,2), the number n₃ of unordered pairs of vertex-disjoint triangles joined by exactly two edges is at least **1,602**. No assumption on symmetries or on another subgraph is made. This does not decide existence. Using [Reimbayev's induced-hexagon identity](https://ejaam.org/articles/2024/10.62780-ejaam-2024-001.pdf), it gives at least **210,888** induced hexagons.

The certificate is a positive identity involving thirteen induced graph counts. All its entries and the exact integer/rational replay are in `check.py` (plain Python 3.10+, no dependencies or downloaded data). It does **not** require the nine-vertex density-gap theorem, a graph atlas, a solver, numerical tolerances, or the separate partner-regular proof.

## What the certificate counts

For a finite labeled simple graph H, write I(H) for the number of injective vertex maps to G carrying every edge to an edge (additional edges permitted). Write J(H) for the corresponding *induced* count, so nonedges must remain nonedges as well. Counts are for maps, not unlabeled images. Our target H₀ is the union of two triangles with a two-edge matching between them. Cross edges in a pair of disjoint graph triangles cannot share an endpoint, since then an edge of one triangle has an extra common neighbor. H₀ has exactly two triangles and four automorphisms: it follows that J(H₀)=4n₃.

A graph below is encoded by (n,m): for 0≤i<j<n, bit j(j−1)/2+i of m specifies edge ij. The rational IDENTITY certified is

    J(H₀) = 83160/13 + Σ_h c_h J(h),

where H₀=(6,0x5674), and the table is complete:

| n | m (hex) | c_h |
|--:|:--------|:----|
| 7 | 7cf0c | 1/2 |
| 8 | 1f996a0 | 421/2340 |
| 9 | f67e0000 | 1/104 |
| 9 | f67e1a00 | 7/90 |
| 9 | 1757e04a0 | 1/13 |
| 9 | 1757e44a0 | 29/1170 |
| 9 | 1b5bb2b00 | 1/13 |
| 9 | 2b6af1a00 | 119/2340 |
| 9 | 4baa65a00 | 17/1170 |
| 9 | 4bcb16300 | 61/1170 |
| 9 | 8ea5c2500 | 17/1170 |
| 9 | a63475200 | 1/39 |
| 9 | c34b53380 | 7/585 |

All coefficients are positive, giving n₃≥20790/13. To check that 3 divides n₃, fix a triangle T and let a_j count disjoint triangles joined to T by j edges. An outside vertex meets at most one vertex of T. The three groups of twelve vertices attached to T are linked by perfect matchings across each pair of groups: a point of one group is nonadjacent to the other parent, with its own parent one of their two common neighbors. The second witness lies in the other group. Each of the 36 cross-group edges lies in a unique triangle disjoint from T. Counting them gives a₂+3a₃=36. Summing over T gives 3 dividing 2n₃, hence n₃≥1602.

## Exact recurrence and independent replay

The following elementary rules verify the stated identity.

1. If a pair in H has more than two common neighbors, or an adjacent pair more than one, I(H)=0. This is a *non-induced* obstruction since the edge/common-neighbor witnesses survive an injective edge-preserving map. The obstruction is monotone under adding edges.
2. By inclusion–exclusion, J(H)=Σ_{L ⊇ H} (−1)^{|E(L)|−|E(H)|} I(L) over all labeled spanning supergraphs. Add missing edges in fixed increasing order, discarding a supergraph and all its supersets whenever rule 1 fails. The fourteen certificate templates, target first, respectively have 2, 1, 1, 283, 9, 8, 4, 4, 3, 19, 16, 42, 49, 8 surviving labeled supersets. No graph outside those fourteen extension trees is needed for the inclusion–exclusion.
3. In I(L), choose a vertex x of degree d≤2 and put H=L−x, R=N_L(x), n=|V(L)|. If d=0, I(L)=(100−n)I(H). If d=1, initially 14 choices exist for x. Subtract one completion for each possible collision with an image of v∈V(H) not in R, which contributes I(H+vR). Here H+vR means add every edge from v to R, keeping already present edges. If d=2 with R={a,b}, initially there are two common neighbors unless the images of a,b are adjacent, in which case there is one. This gives 2I(H)−I(H+ab), from which one again subtracts Σ_{v∉R} I(H+vR). Collisions with a or b themselves cannot occur (no loops). These recurrences use labeled injective maps and hence have no missing symmetry factors.
4. Set I(single vertex)=99. Treat any surviving graph of minimum degree at least three as a free formal symbol, using the same symbol on isomorphic graphs. One need not assume that these formal counts are independent. The verifier refines vertex classes by their neighbor counts and checks all orderings within the resulting invariant classes, obtaining canonical keys independent of the search used to discover the certificate.

Substitute rules 1–4 in the left side minus the thirteen weighted terms. Exact rational coefficients of *every* formal graph symbol cancel, leaving the constant 83160/13. This supplies a short checkable proof, not a solver feasibility report. The earlier seven-vertex census approach and its scope can be compared with [Wave 44's integration audit](https://github.com/YesterdaysLemon/conway-99-research/blob/main/verification/2026-07-27-wave44-integration-audit.md); this certificate operates through nine vertices.

[Uncovered squares and rook grids at the endpoint](../uncovered-squares/README.md): an exact two-star certificate strengthens the identity to `4n₃−83160/13 ≥ (136/195)U₀`. If `n₃=1602`, at most 15 squares lack a prism direction and the number of induced rook grids is 53 or 54. The endpoint remains open.
