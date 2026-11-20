# Binary cut equations at every root, and sixteen generating partners

This corollary strengthens the local numerical bound in Percolation.md. It uses the no-partner-regular-root theorem but not an automorphism.

Use the 21 four-point cells C_e at o, e an edge of the seven-axis K₇. Call a cell clean if its square completes the two axes to a 3-by-3 rook grid. For x in cell C_h define a binary word on the 21 edges by

    δ_x(e) = |N(x) ∩ C_e| + [e and h are disjoint]   (mod 2).

This word vanishes on every clean cell e, by domination of the grid: for disjoint h the count is one, for distinct intersecting h it is zero, and for h=e it is two. Also δ_x has even weight, because x has twelve exterior neighbors and ten disjoint axis pairs.

Every δ_x has even degree at every underlying axis a. Indeed, over F₂, if t_a indicates the two signed points of axis a and B_e the four cell points, then (A+I)t_a=sum_{e incident with a}B_e. The SRG identity gives A²=A, so multiplying by A annihilates that sum. The binary baseline on each axis has sum 0 as well (zero or four disjoint axis pairs). Thus a nonzero δ_x is an even-cardinality Eulerian subgraph, of size at least four.

If δ_x=0 for x at the signed pair (a,b), then there is at least one neighbor of x in each of the ten cells disjoint from ab. Its triangles with its two distinct signed parents also require two *distinct* outside neighbors, one sharing the signed a and one the signed b. These twelve demands exhaust its twelve exterior neighbors. The two latter neighbors must lie in the same underlying cell, because the parity is zero in every nondisjoint cell. That cell must contain both a and b, so is C_ab, and the two edges realize both standard sign flips. If all δ_x are zero the root is therefore partner-regular, impossible. Consequently the missing cells at every root contain the edge support of an even Eulerian subgraph, and in particular there are **at least four missing cells**. By the closure classification in Percolation.md all four vertices of each missing cell generate the graph together with o. Hence every vertex has **at least sixteen** generating nonneighbors. No conclusion on graph existence is drawn.

**Point-code identity, valid without partner regularity.** Let B have columns B_e, K be KG(7,2) adjacency, and F=AB+BK over F₂ on all 99 points. The rows outside the first two layers are the above δ_x; the root and its first-layer rows are zero. Each row of F has even weight and even axis degrees. Writing K=J+I+DᵀD in F₂ for the axis-edge incidence D gives FK=F. Also K²=K by its integer square relation or K=J+I+DᵀD. Hence AF=AB+ABK=F+FK=0. Each column of grid-parity deviations is an actual binary kernel word of the graph.
