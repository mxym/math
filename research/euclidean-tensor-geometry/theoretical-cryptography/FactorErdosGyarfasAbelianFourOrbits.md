# Power-of-two cycles for free abelian actions with four vertex orbits

**Theorem.** Let \(X\) be a nonempty finite simple graph of minimum degree at least three. Suppose an abelian group acts freely by graph automorphisms and has at most four vertex orbits. Then \(X\) has a simple cycle of length \(4\), \(8\), or \(16\). The bound \(16\) is optimal, even among connected cubic graphs with exactly four orbits under a specified cyclic group action. In particular, the theorem applies to Cayley graphs of groups with an abelian subgroup of index at most four, and to all regular abelian covers of \(K_4\).

The proof extends the [three-orbit result](FactorErdosGyarfasAbelianThreeOrbits.md). For four orbits it reduces to 15 finite quotient templates and a small exact certificate (109 relation cells), **independent of the size, exponent, or number of invariant factors of the acting group**. It establishes existence of a cycle, not containment through a designated vertex or edge. It does not resolve the general [Erdős–Gyárfás problem](https://arxiv.org/abs/2609.28594). The setup of cyclic and abelian covers of small complete graphs has prior literature, e.g. [Pan, Huang, Xu and Ding](https://doi.org/10.1016/j.disc.2014.04.023); the claim here is a uniform dyadic-cycle conclusion under the wider free action hypothesis.

## 1. Reductions to the templates

Write the acting group \(A\) additively, and identify each orbit with a copy of \(A\) by choosing an origin. Between different layers \(i,j\) every edge orbit is a matching \(i_g\sim j_{g+s}\) for a single shift \(s\). Edges within a layer are given by a symmetric set of nonzero steps. If there are at most three layers, the earlier theorem applies. If the graph on the four layers formed by the cross matchings is disconnected, take one connected component of it; each retained vertex keeps all its incident edges, and the restricted action has at most three layers.

The following cases settle some quotient shapes immediately.

* Internal steps \(x,y\) in one layer with \(y\ne\pm x\) give the simple commuting square on \(0,x,x+y,y\).
* At least three matchings between two layers give the [two-layer three-matching result](FactorErdosGyarfasAbelianTwoOrbits.md).
* Two adjacent layers with internal steps \(x,y\) and a cross matching give a square if \(y=\pm x\). Otherwise normalize that matching to zero and take the cycle \(i_0,i_x,j_x,j_{x+y},i_{x+y},i_y,j_y,j_0\). The four coordinates are distinct except in the already excluded cases.
* Two pairs of doubled cross matchings sharing a layer \(i\) give two kinds of length-two paths \(i_g\leadsto i_{g+d}\) and \(i_g\leadsto i_{g+e}\) through the two different neighboring layers, for nonzero label differences \(d,e\). If \(d=\pm e\), use the two paths to the same endpoint to get a square. Otherwise use the rectangle \(0,d,d+e,e\) in layer \(i\), lifting each side through the corresponding neighboring layer. The two intermediate points in each of these layers differ by \(e\) or \(d\), so the lifted 8-cycle is simple.

In the remaining shapes each pair has multiplicity \(0,1,2\), the doubled pairs are disjoint, and each layer has internal degree \(0,1,2\), respectively no step, one nonzero involution, or a pair \(x,-x\) with \(2x\ne0\). No cross matching joins two layers that both have internal edges.

Delete redundant edge orbits while preserving minimum degree three: a cross matching can be removed if both endpoint layers have degree greater than three, and an internal edge orbit if that layer already has at least three cross matchings. If this disconnects the layer graph, use the at-most-three-layer theorem on a component. No deletion can create any of the already excluded patterns. When no rule remains, write \(\ell_i\in\{0,1,2\}\) for the internal degrees and \(m_{ij}\in\{0,1,2\}\) for the matching multiplicities. The conditions are just those checked in the following finite enumeration:

1. The layer graph is connected and doubled pairs are disjoint.
2. \(\ell_i+\sum_{j\ne i}m_{ij}\ge3\) for each \(i\).
3. No positive \(m_{ij}\) joins two positive \(\ell_i,\ell_j\).
4. A pair with \(m_{ij}>0\) has at least one layer of total degree three.
5. A layer with \(\ell_i>0\) has cross degree at most two.

The independent Python checker inspects all \(3^4 3^6\) arrays, giving 179 labeled shapes and 15 representatives up to the 24 relabelings of the layers. A deleted edge orbit does not need to be restored to obtain a cycle.

## 2. Universal integer-voltage representation

For each representative, normalize the first edge along each link in a spanning tree to shift zero. The checker takes these tree links greedily in the order \(01,02,03,12,13,23\). Each remaining cross matching has a formal generator, as does each nonempty internal layer. If there are \(b\) generators, assign them the standard basis vectors of \(\mathbb Z^b\). For a noninvolutory step use two arrows with opposite voltages, and for an involution use one arrow with a single formal vector \(e\) and the relation \(2e=0\). All orientations, including reverse arrows for each matching, are specified by the checker.

Write \(R_0\le\mathbb Z^b\) for the relation subgroup generated by the involution relations. Any actual label assignment on the template is evaluation by a homomorphism \(\phi:\mathbb Z^b\to A\) with \(R_0\subseteq\ker\phi\), subject to a list of **nonvanishing vectors**: the difference of the two labels for every doubled link, the step vector for an involution, and twice the step vector for a noninvolutory internal pair. These are the only assumptions on the homomorphism in the certificate. For instance there is no independence or generic-position requirement.

A candidate cyclic quotient walk is encoded by its directed arrow indices, with no immediate reversal, including across the cyclic boundary. Let \(w\) be the sum of its voltage vectors. For each successive vertex before the final return, record its layer and its partial voltage. Form a list \(D\) of differences of partial voltages of distinct occurrences in the same layer. The lift, starting at any chosen coordinate in its starting layer, is a simple cycle exactly when
\[
                         w\in\ker\phi,\qquad D\cap\ker\phi=\varnothing .
\]
Indeed the lifted vertices are the pairs of the recorded layers and the corresponding evaluated partial voltages plus the starting coordinate.

## 3. Finite certificate and soundness

The [frozen certificate](erdos_gyarfas_four_orbit_certificate.json) and [its Python verifier](verify_factor_erdos_gyarfas_four_orbits.py) use the following inference. At a state \(R\) we consider all admissible evaluations with \(R\subseteq\ker\phi\). If \(R\) contains a required nonvanishing vector, no evaluation remains. Otherwise the certificate gives a walk of length \(4,8,\) or \(16\) with \(w\in R\) and \(D\cap R=\varnothing\). For any admissible evaluation, either this lifts simply, or \(\phi(d)=0\) for some \(d\in D\). For the latter possibility check the child state \(R+\mathbb Z d\). It either violates a nonvanishing constraint directly or is another checked state. This tests every possible reason the walk fails to lift simply, not merely collisions seen in some finite deck group.

The checker computes canonical row Hermite bases by integer unimodular row operations. Membership in their row lattice is tested by successive pivot divisions and then a zero test on the remainder; in particular neither rational span nor modular testing substitutes for **integer** membership. Each child strictly enlarges \(R\), and every certificate has a finite reached-state list, so induction up the resulting directed acyclic graph proves coverage. Starting at \(R_0\), 109 reached nonterminal cells over the 15 templates suffice, with depth at most four. Every asserted cell is used and all its collision children are verified, not just the chosen quotient walk. Python 3 with its standard library suffices; run the verifier beside the frozen JSON file.

## 4. Sharpness with exactly four cyclic layers

Use the \(K_4\) template \(0000111111\). Put shift zero on the three edges from layer 0; label the remaining forward edges \(12,13,23\) by
\[
                  1,\quad33,\quad33^2
\]
in \(\mathbb Z/M\mathbb Z\), where any integer \(M>16(1+33+33^2)\) works. The regular cover is simple and cubic, and it is connected: the fundamental triangle \(0120\) yields shift 1, so the fiber over layer 0 is connected by walks, and the zero tree shifts reach the other fibers.

Any formal coefficient vector relevant to a walk of length at most 16 or to one of its partial-voltage differences has all coordinates in \([-16,16]\). A nonzero such vector evaluates to a nonzero integer at \((1,33,33^2)\): a highest nonzero base-33 term dominates all lower terms. Its absolute value is smaller than \(M\), so it stays nonzero in the cyclic group. Thus short walk closure and collisions agree with those in the formal group.

The verifier checks every rooted directed cyclically nonbacktracking walk of lengths 4 and 8 in \(K_4\) (respectively 24 and 168): none has zero formal total. Alternatively, if the cotree totals vanish, the tree-edge totals vanish too by zero net flow at each vertex. Thus a closed walk of length at most eight with zero total would use at most four distinct unoriented edges, each in both directions. Its connected support has minimum degree at least two by cyclic nonbacktracking. In simple \(K_4\) a support of at most four edges with that property is only a cycle, on which cyclic nonbacktracking cannot balance the two directions. For length 16 the formal arrow indices
\[
          0,6,3,0,6,3,4,9,1,2,7,1,2,7,8,5
\]
give zero sum and no collision, checked directly. Hence the shortest power-of-two length is exactly 16 for this whole unbounded family, with four vertex orbits under the displayed cyclic translation action.
