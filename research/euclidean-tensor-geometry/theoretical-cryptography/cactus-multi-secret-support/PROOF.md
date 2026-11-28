# Cactus block classification and elimination of nonuniform three-state sources

## 1. Model and pair-edge reduction

Let \(G=(V,E)\) be a finite simple graph and let \(\varnothing\ne D\subseteq\{0,1\}^V\). The dealer has a fixed finite source \(R\) with positive weights, independent of the input \(x\in D\). At input \(x\) and state \(r\) the share on \(e\) is \(W_e(x,r)\). The view at \(v\) is the full tuple of incident shares. Correctness requires that the view supports for different local bits be disjoint, and privacy that its law be equal at all inputs with the same local bit. These are pointwise conditions, with no prior on \(D\).

A vertex is active if both local bits occur, and a pair edge \(uv\) is one on which \(x_u\oplus x_v\) is constant on \(D\). On such an edge we can always replace its share by one endpoint bit: the law at either end depends only on its local bit, and both endpoints can decode. The endpoints are called covered. Replacement preserves the other shares, preserves privacy as a deterministic modification conditional on the local bit, and preserves correctness at all endpoints by the new pair-edge decoder. Write \(H\) for the spanning subgraph after all pair edges are deleted, and call active uncovered vertices **required**. Thus on \(H\) only required vertices must decode; all vertices still need privacy.

On a nonpair edge the marginal share law is independent of the complete input \(x\). To see this, first use endpoint privacy to conclude that the marginal depends only on either endpoint bit. Form the bipartite graph on the occurring bit values at each endpoint, with an edge for each occurring pair. A disconnected graph would have to be exactly two disjoint edges using both bits at both ends; this is precisely an XOR relation. Otherwise the law is common along all edges by connectivity. This also handles inactive endpoints. Consequently a required vertex of degree zero or one in \(H\) cannot decode. If there are no required vertices, deterministic pair-edge shares suffice, and if one is required, deterministic shares cannot decode it because all its marginals would be globally constant.

## 2. No nonuniform three-state minimum, on any graph

By [M, Proposition 12], any nonuniform three-state weight vector other than \(Q=(1/2,1/4,1/4)\), up to ordering, already reduces to at most two states. For clarity this known reduction uses coincidences of subset masses on three positive atoms. Unless one weight is \(1/2\), the only unequal subsets of equal mass exchange equal-weight atoms, so a uniquely weighted atom has the same view at all inputs of each local bit and can be fixed. If the weights are \(1/2,a,b\) with \(a\ne b\), a view with a partition other than the heavy singleton versus the light pair has uniquely determined fibers given its law: the light singleton masses are unique and any remaining fiber is then determined. In the exceptional partition the two output values can interchange. Restricting to the heavy atom and one light atom, now equally weighted, preserves privacy in either case. Restriction preserves correctness. Two-state sources can also be taken uniform, as noted in [M, Lemma 9]; if two weights differ, each atom's view is determined by the law.

We remove the remaining case \(Q\). Work on \(H\), reinstating deterministic pair shares at the end. Let \(h\) be the heavy atom. An edge has a fixed marginal of one of four types:
- constant;
- balanced with masses \(1/2,1/2\), written \(B\);
- masses \(3/4,1/4\), or three masses \(1/2,1/4,1/4\), together written \(J\).

Its original value on \(h\) is globally fixed on every non-\(B\) edge: it is the value of mass at least \(1/2\) that contains \(h\), which is unique for these types. On a \(B\) edge relabel its two values as bits and write \(\alpha_e(x)=W_e(x,h)\); both light atoms have the opposite bit. Use a fresh uniform bit \(U\), putting \(U\oplus\alpha_e(x)\) on \(B\) edges, \(U\) on every \(J\) edge, and constants on the remaining edges.

Consider the full view on \(H\).
- If \(v\) sees no \(B\) edge, the new view is independent of \(x\). The old view on \(h\) was globally constant, so \(v\) could not have been required.
- If \(v\) sees \(B\) but no \(J\), the two light atoms had identical old view and the new law and support of the \(B\) labels exactly reproduce the old ones. Constant entries can be retained.
- If \(v\) sees both \(B\) and \(J\), the old view separates all three atoms. Indeed \(B\) separates \(h\) from the lights, and a \(J\) edge separates the two lights. The mass-\(1/2\) view value is therefore unique, belongs to \(h\), and depends only on \(x_v\) by privacy. Each incident \(\alpha_e\) is then a function of \(x_v\), so the new joint law is private. If \(v\) is required, the two heavy view values must differ between its local bits, and the differing entry must be on a \(B\) edge. From any \(J\) edge it reads \(U\), and can distinguish the bits using that \(B\) entry.

So \(Q\) also reduces to two uniform states. In particular, whenever the true minimum is three, **every minimum scheme has a uniform source**. This reduction does not assume a cactus or any other graph structure.

## 3. Exact cycle tests on a cactus

Assume \(G\) is a connected cactus (every edge is in at most one simple cycle). The same edge property holds for the possibly disconnected \(H\); its nonsingleton blocks are bridges and simple cycles. In each component, deleting one edge per cycle leaves a connected tree: the other edges of each cycle still connect its endpoints, and no cycle remains. Thus, if there are \(c\) cycles, the original edge count is the vertex count minus one plus \(c\). Replacing each cycle by a new center joined to its vertices preserves edge count and adds one vertex, hence yields a tree; subdividing every bridge adds both one vertex and one edge. This is the tree of blocks and their incidence vertices, with non-cut original vertices as leaves. A required vertex on a cycle of \(H\) is called **rigid** on it if its degree in \(H\) is two. Call the remaining vertices of that cycle **flexible**. This includes nonrequired vertices and cut vertices with at least one retained edge outside that cycle.

For \(m=2,3\), perform the following test separately on each cycle \(C=(v_1,\ldots,v_k)\) of \(H\). Fix any \(x^0\in D\).
- A cycle with an edge joining two flexible vertices passes.
- Otherwise, it passes if there exist permutations \(\delta_i\in S_m\), one per vertex, such that each rigid vertex has a fixed-point-free \(\delta_i\), and
\[
  \delta_k^{x_{v_k}\oplus x^0_{v_k}}\circ\cdots\circ
  \delta_1^{x_{v_1}\oplus x^0_{v_1}}=\mathrm{id}
        \qquad(x\in D).
 \tag{1}
\]
Only the projection of \(D\) to the cycle is used in (1). For \(m=2\) the transposed positions are precisely a subset containing all rigid vertices whose parity is constant on \(D\). For \(m=3\) one can equivalently use affine maps \(t\mapsto a_i t+b_i\) on \(\mathbb F_3\), with \(a_i\in\{1,-1\}\), requiring \(a_i=1,\ b_i\ne0\) at rigid vertices. The normalized word test can be examined in at most \((m!)^k\) tuples. There is no joint search across different blocks.

**Theorem.** If all required vertices have degree at least two in \(H\), then a uniform \(m\)-state scheme, for \(m=2,3\), exists if and only if every cycle passes its \(m\)-test.

**Necessity.** Consider a rigid vertex. Both edges are nonpair and each sees a globally fixed marginal. For \(m=2\), neither edge can be constant, since the other would reveal no bit by itself; hence each takes two values. For \(m=3\), again discard a constant edge. A two-valued edge has a unique mass-\(2/3\) label and a unique mass-\(1/3\) label. Two such edges always have their mass-\(2/3\) labels occur together at some state, so their joint supports for the two bits overlap. If one edge has two values and the other three, at most two of the three globally fixed labels of the latter can be paired to the mass-\(1/3\) value over any two representative inputs of opposite local bits. The remaining label occurs with the mass-\(2/3\) value at both. Therefore both edges at a rigid vertex must take \(m\) distinct values with uniform probabilities.

If no edge of \(C\) joins two flexible vertices, every edge is incident to a rigid vertex. Each is thus a full \(m\)-label share, which can be identified with \([m]\). At \(v_i\), the joint law gives a fixed permutation \(\pi_i^b\) from the incoming edge label to the outgoing one for each occurring bit \(b\). Its value for a missing bit is arbitrary. At a rigid vertex, disjoint view supports say \(\pi_i^0(t)\ne\pi_i^1(t)\) for every \(t\), or equivalently the relative permutation is fixed-point-free. At each input, following the permutations around \(C\) gives the identity on all labels, since the starting edge takes every label. Relabel each outgoing edge by \(g_i\), where \(g_i\circ\pi_i^{x^0_{v_i}}=g_{i-1}\) starting from any incoming-edge relabeling. Closure at \(x^0\) makes these relabelings cyclically consistent. The new baseline maps are identities, the other maps are the required \(\delta_i\), and identities and fixed-point-freeness are preserved by the corresponding conjugations. This is (1).

**Sufficiency, within a block.** Use labels \(\mathbb Z/m\) and one global uniform \(R\) in that set. For a cycle with a flexible-flexible edge, make its share constant and retain the other edges as a path. In the path, prescribe the permutation \(t\mapsto t+x_v\) at rigid interior vertices (from one edge to the next) and the identity elsewhere. All rigid vertices remain interior. For a cycle certified by (1), retain all edges and prescribe the permutation \(\delta_i^{x_{v_i}\oplus x^0_{v_i}}\) from incoming to outgoing. For a bridge retain its single edge. In each block every vertex has at least one retained edge, and for a fixed input one may prescribe any retained edge's label and propagate to all others. When propagating backwards one uses inverse permutations. A path has no closure condition; cyclic consistency is (1). If the starting label is a permutation of \(R\) at each input, so are all other labels. At a rigid vertex the two local labels decode, by a shift on a path or by the fixed-point-free requirement on a full cycle.

**Sufficiency, between blocks.** Independently root each component's block–cut tree at any nonempty block, using the same \(R\) even across components. In the root block choose any retained edge and set its label to \(R\). Process children recursively. At a cut vertex \(v\), let \(Y_v\) be the label of a designated retained edge in its parent block. In each child block fix a designated retained incident edge to have label \(Y_v\); if \(v\) is required, use \(Y_v+x_v\pmod m\) instead in one designated child. This is possible since a cut vertex has at least two blocks, has at least one child block in this rooting, and each block permits an arbitrary starting label. Then propagate within each child block. At \(v\), all incident labels in each block are the designated label there or its image under a prescribed local permutation (or its inverse), depending only on \(x_v\). Thus the **entire** view at \(v\) is a fixed function of \(Y_v\) and \(x_v\) and constants/deterministic pair shares; \(Y_v\) is uniform for each input. A required cut vertex decodes by subtracting the two designated labels. At a vertex in just one block the same privacy statement holds using a designated edge in that block alone; if it is required with degree at least two it is rigid and already decodes. Isolated vertices are not required. This proves the theorem.

## 4. Four states suffice whenever feasible, except for the bare triangle

Suppose \(G\ne C_3\) and all required vertices have degree at least two in \(H\). Build two spanning forests \(F_1,F_2\subseteq H\) retaining all bridges. From every cycle of length at least four delete one edge in each forest, taking distinct disjoint edges for the two deletions. From a triangle delete two distinct edges that meet at a flexible vertex, one per forest. A residual triangle always has a flexible vertex: otherwise every vertex would be required of degree two, so the triangle would be a component of \(H\). Any edge of the connected \(G\) outside the triangle that joins it to the rest would be a deleted pair edge, contradicting required status at its triangle endpoint. If no such edge exists, \(G=C_3\), by connectivity and simplicity.

Every required vertex has degree at least two in at least one forest. For degree at least three, write that degree as \(b+2c\) from \(b\) bridges and \(c\) cycle blocks incident there. Its degree in each forest is at least \(b+c\ge2\). For degree two, two bridges survive in both, and for the two edges of one cycle, disjoint deletion edges (or deletions meeting only at a flexible vertex) keep both edges in some forest. Assign each required vertex to one such forest.

In each \(F_i\), use the one-bit forest construction of [M, Theorem 3], with its own independent uniform bit \(U_i\). Explicitly, fix signs \(q_{ve}\in\mathbb F_2\) at incidences, taking opposite signs at two edges at each vertex assigned to this forest. For each \(x\) choose potentials \(h_v(x)\) with \(h_u(x)\oplus h_v(x)=q_{ue}x_u\oplus q_{ve}x_v\) on \(e=uv\) by starting at zero at each tree root and following paths. At \(v\) the edge field is \(U_i\oplus h_v(x)\oplus q_{ve}x_v\), which agrees at both ends and decodes via opposite signs. If an edge occurs in both forests put both fields on it, with positions specified in advance. At any vertex the two shifted root masks \(U_i\oplus h_v(x)\) are jointly independent uniform bits for every fixed input, so the complete combined view depends only on the local bit. Add back deterministic pair shares. The result uses four positive states.

Together, the exact minimum for connected cactus \(G\ne C_3\) is:
1. \(\infty\) if a required vertex has degree below two in \(H\);
2. \(1\) if no vertex is required;
3. \(2\) if every cycle passes its 2-test;
4. \(3\) if every cycle passes its 3-test;
5. \(4\) otherwise.

In this ordered list the two-state test precedes the three-state test: a uniform-two solution need not imply a uniform-three solution. The standalone \(C_3\) has its prior exact three-secret-sharing classification [A]. The tests in §3 continue to hold there for uniform two and uniform three; the four-state bound is not claimed for the bare triangle.

## 5. A six-vertex cross-block obstruction

Identify the first bit \(a\) of a triangle and a four-cycle at their shared vertex. On their ordered vertices use domains
\[
 D_3=\{000,011,101,110\},\qquad
 D_4=\{0000,0111,1001,1010,1100\}.
\]
Take all pairs of these words with matching \(a\), identifying that bit. The two projections are unchanged, so all six vertices are active and no edge is a pair edge. The resulting domain has ten points. Only the attachment vertex is flexible on either cycle.

On the triangle all-word parity is zero, giving a 2-test certificate. If it had a 3-test certificate, the two rigid maps would be translations; since \(a\) takes both values, the sign of the group product in (1) forces its map to be a translation as well. Taking baseline zero, the three words of weight two force the three pair sums of the shift coefficients to vanish modulo three. Hence all three shifts are zero, contradicting rigidity.

For the four-cycle, the four nonzero words span \(\mathbb F_2^4\): the three with first bit 1 have distinct single ones in the last three coordinates, and their sum is \(1111\), while \(0111\) is not in their span. No nonzero parity is fixed, ruling out the 2-test. The shifts \((-1,1,1,1)\) sum to zero with the indicated word coefficients over \(\mathbb F_3\), giving a 3-test certificate. This cyclic domain is the known five-point mod-three example [M, Theorem 5]; we use it as one block, rather than claim it as a new individual cycle construction.

Each block by itself admits at most three states even with its shared vertex required to decode. On the union neither of the two common-state tests passes globally, and the nonuniform reduction excludes every other three-state source; four states are optimal by §4.
