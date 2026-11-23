# Seven five-site shores: two exact wings, one excluded at rank 36

Let \(T\) be one fixed triangle and count the actual nontrivial three-edge bonds with a five-site shore in its cubic wing \(W\). By the [rank-free identification and disjointness](nongrid-squares-fano-unconditional.md), their five-site shores are disjoint. Each has one vertex in its small physical wing and two vertices in each other wing. Its three boundary darts are a mate of the small site and one transverse edge from each of its two lower sites, all pointing into its small wing. The three outside endpoints are distinct (unit square marks). In particular a fixed triangle has at most seven five-site shores.

**Result.** Exactly seven such shores leave only two completely specified 36-site wing diagrams, as abstract labelled diagrams to be tested, not realizations. One has wing tree number 4 modulo seven and is impossible at mod-seven Seidel rank 36. The other, even if realizable, forces two distinct original unit charge-three cost-39 fields with independent positives. Consequently at rank 36 with that literal shell subtype absent, every triangle has at most six five-site shores.

## Classification in two diagrams

Seven shores occupy 35 sites, leaving one singleton \(z\). If \(r_i\) is the number of shores small in physical wing \(i\), then \(14-r_i\le12\), so \(r_i\ge2\). Their sum is seven. Thus the small types have multiplicities \(3,2,2\), and the remaining singleton is in the type \(A\) with multiplicity three.

An edge joining two shores of the same small type can only join their two small sites as mates: both boundary endpoints must be in that physical type, and its small sites have both cross-wing neighbors internal. For different small types \(i,j\) a connecting edge joins their two lower sites in physical \(j,i\) respectively; no other endpoint would have a boundary edge to the required physical type. No two shores have two connecting edges.

All three neighbors of \(z\) in \(W\) are on \(A\)-small shores (all boundary targets of a shore are in its small wing). They are on three distinct shores, because a given shore has distinct outside endpoints. Label those shores \(A_0,A_1,A_2\) according as their edge to \(z\) is the mate dart, the dart from physical \(B\), or the dart from physical \(C\). Then \(A_1,A_2\) are small-site mates. Likewise the two \(B\)-shores are small-site mates of each other, and so are the two \(C\)-shores. The two remaining required \(A,B\) joins link \(A_0,A_2\) to the two \(B\)-shores, which labels them \(B_0,B_1\). The \(A,C\) joins similarly link \(A_0,A_1\) to \(C_0,C_1\). All labels were assigned by these local conditions, not by assuming a graph automorphism. Finally \(B\) and \(C\) each have a required dart to the other small type, giving either the identity matching \((B_0C_0,B_1C_1)\) or the interchange \((B_0C_1,B_1C_0)\).

This determines every edge in the cubic wing: internal to a shore, the upper three sites \(U,H_i,H_j\) form a triangle, the lower sites \(L_i,L_j\) are adjacent, and \(H_iL_i,H_jL_j\) are the other edges. Across shores or to the singleton all edges were just specified. Both diagrams are connected.

## Exact determinant and the surviving subtype

The [two-chart checker](seven-five-shores.js) uses only ordinary arithmetic modulo seven on the explicit 35-by-35 Laplacian cofactors, verifies the physical matchings and connectedness, and outputs
\[
 [[\mathrm{true},0],[\mathrm{false},4]],
\]
where the Boolean records whether \(A_0B_0C_0\) is a join triangle, and the number is the matrix-tree residue. This checksum requires no actual far labels and no optimization. Apply the [rank-36 spanning-tree obstruction](triangle-wing-tree-rank36.md): a seven-unit wing tree count is necessarily a nonsquare at rank 36. The interchange residue 4 is square, so it is excluded there; no exclusion of the identity diagram is claimed.

In the identity diagram \(A_0B_0C_0\) has a joined triangle of five-site shores. Its 15-site union has three small-site outgoing mates exactly \(\{z,U_{B_1},U_{C_1}\}\), which are independent. The inside small sites are also independent, as their joins use only the lower sites. Thus both complementary orientations of the [balanced three-cut transfer](three-cut-original-fields.md) yield actual original independent-positive charge-three cost-39 fields. Their positive supports are disjoint, so they are different. This gives the stated rank-36 structural conclusion. Even without any rank input, the identity diagram always requires these two extra fields; nothing in this argument rules out the interchange at higher rank.
