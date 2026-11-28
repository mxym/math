# Classification of all short-dyadic-free graphs with six free abelian orbits

**Theorem.** Let \(G\) be a nonempty finite simple graph of minimum degree at least three admitting a free abelian action on at most six vertex orbits. If \(G\) has no simple cycles of lengths \(4,8,16\), it has exactly six vertex orbits, and its quotient on these orbits is the **simple \(K_{3,3}\)**, with no internal edges within an orbit and one translation matching per base edge. In particular \(G\) is cubic and bipartite, and its connected components are connected regular abelian covers of \(K_{3,3}\).

Consequently each vertex of such a short-dyadic-free graph lies on a simple \(32\)-cycle. The minimum possible order is **798** and exactly **three nonisomorphic graphs** attain it. The same result permits nonbipartite input graphs and does not require the group to preserve a specified bipartition. It still assumes the free abelian action and at most six orbits, and does not prove the unrestricted Erdős–Gyárfás conjecture.

This strengthens the [part-preserving bipartite six-orbit classification](FactorErdosGyarfasSixLayerExtremalQuotient.md), and uses the previously proved [fixed-base exact minima](FactorErdosGyarfasFixedBaseMinima.md) and [rooted \(K_{3,3}\) result](FactorErdosGyarfasK33Rooted.md). Those minima and witness graphs are not new here. The new proof covers all reduced six-orbit quotient templates and all four ways to extend a cubic \(K_{3,3}\) quotient. It follows the relation-lattice method of the [earlier five-orbit proof](FactorErdosGyarfasAbelianFiveOrbits.md), whose five-orbit result and certificate were [previously released](https://github.com/mxym/math/releases/tag/erdos-gyarfas-abelian-five-orbit-threshold-v1.0.0). [Ducoffe–Dumitru](https://arxiv.org/abs/2609.28594) address restrictions and finite-order verification for the unrestricted graph problem, rather than this free-action classification.

## 1. All reduced six-layer templates

Identify each free orbit with a copy of its acting abelian group \(A\). A cross edge orbit is a translation matching, and an internal edge orbit is given either by one nonzero involution step or by two opposite steps. If the number of orbits is at most five the established theorem already supplies a \(4/8/16\)-cycle. If the graph on the orbit layers is disconnected, retaining the union of layers in any connected quotient component gives a free action with fewer layers and the same degree condition. We may therefore work with six layers and a connected quotient.

The following local reductions are independent of bipartiteness.

* Two internal steps at one layer not equal up to sign give the square on \(0,x,x+y,y\) in that layer. Thus each layer has internal degree \(\ell_i\in\{0,1,2\}\), the three possibilities being none, one involution, or a pair of distinct opposite steps.
* Three matchings between two layers give a short dyadic cycle by the [three-matching abelian lemma](FactorErdosGyarfasAbelianTwoOrbits.md#1-three-translation-matchings). Thus cross multiplicities \(m_{ij}\) are in \(\{0,1,2\}\).
* Adjacent layers with respective nonzero internal steps \(x,y\) give a square if \(y=\pm x\), and otherwise a simple eight-cycle. Indeed normalize a matching to zero and use the commuting rectangle with each internal step in its own layer and matching edges between them; the four coordinates \(0,x,y,x+y\) are distinct in the latter case.
* Doubled pairs of layers are disjoint. If two share a layer, they give two ways to move in it by length-two paths through different intermediate layers, with nonzero steps \(x,y\). If \(y=\pm x\), two paths can end at the same point and form a square. Otherwise expand the rectangle \(0,x,x+y,y\) into an eight-cycle. Within each intermediate layer the two visits differ by the other nonzero step, so the cycle is simple.

Delete a cross matching whenever both endpoint layers have degree greater than three, and delete an internal edge orbit if its layer already has cross degree at least three. These operations preserve simplicity, the free action, and minimum degree at least three. If the quotient disconnects during deletion the fewer-layer theorem applies to one component. Stop when no operation applies. The surviving template \((\ell,m)\) therefore satisfies:
\[
\begin{gathered}
 \text{the cross layer graph is connected and doubled pairs are disjoint},\\
 d_i=\ell_i+\sum_{j\ne i}m_{ij}\ge3,\qquad
 m_{ij}>0\ \Longrightarrow\ \ell_i\ell_j=0,\quad\min(d_i,d_j)=3,\qquad
 \ell_i>0\ \Longrightarrow\ d_i-\ell_i\le2 .
\end{gathered}
\tag{1}
\]
These conditions are finite and complete for this reduction. The checker enumerates every underlying connected simple graph on six labeled layers, every matching of its edges to be doubled, and every allowed \(\ell\) assignment by (1). It labels the types by the six internal degrees followed by the fifteen multiplicities in increasing pair order, and takes the lexicographically least string under all layer permutations. There are **130,348** labeled arrays and **291** types. This enumeration iterates simple graphs and matchings in a different order from the construction of the certificates. For a cross degree of one the internal degree must be two; for cross degree two it is one or two; for cross degree at least three it is zero. Thus the internal choices never omit a solution of (1). The connected degree condition precludes cross degree zero.

## 2. Universal label relations

For any connected template choose the greedy spanning tree in increasing pair order. Set its first matchings to zero by choosing one sheet origin per layer. Give a formal coordinate to each remaining cross matching and each internal orbit. Within an internal degree-two orbit use darts labeled \(x,-x\); within an internal degree-one orbit use a self-reversing dart and the relation \(2x=0\). All actual labels are evaluations of these coordinates by a homomorphism \(\phi:\mathbb Z^r\to A\) satisfying the involution relations and the following nonvanishing tests:
* parallel cross labels have nonzero difference;
* an involution step is nonzero;
* for each internal opposite pair \(x,-x\), \(2x\ne0\).

No hypothesis about the order, exponent, or rank of \(A\) is made. Only these explicitly verified constraints are used. The encoding covers disconnected lifts of a connected layer template as well.

For a cyclically nonbacktracking directed template word, record the layer and partial voltage of every position before the final return. The lift is a simple cycle exactly if its total voltage vanishes and each difference between distinct prefix voltages in the same layer is nonzero under \(\phi\). The certificates work with a lattice \(R\subseteq\ker\phi\). Each supplied word has length \(4,8\) or \(16\), its total belongs to \(R\), and no such collision difference is in \(R\). If all differences stay nonzero under evaluation we are done. Otherwise a possible collision \(b\) instead permits passing to \(R+\mathbb Zb\). Such a child is discarded only when the new relation lattice contains a required nonzero vector, and otherwise is explicitly checked. Every update strictly increases the lattice, and the finitely many checked states give a complete induction. In particular the proof is **not** a survey of some finite group orders or an assumption of independent generic labels.

The [data](erdos_gyarfas_general_six_orbit_certificate.json) and [exact verifier](verify_erdos_gyarfas_general_six_orbits.py) cover **290** of the 291 types, with **4,639 distinct nonterminal states** in total and maximum depth five. The sole omitted reduced type is
\[
                     \texttt{000000001110111111000},
\]
namely simple \(K_{3,3}\) without internal edges. The verifier independently recreates the shape list and every dart label, and checks lattice membership via integer row Hermite form using Euclidean unimodular row operations. It checks the exact coverage of every collision child and verifies every listed table entry is reached. No floating point is required to verify the printed theorem.

## 3. The four possible extensions of the surviving quotient

The reduced graph retains the full vertex set. If it survives without a short dyadic cycle, its six-layer quotient is simple \(K_{3,3}\). If any deleted edge orbit existed in the original graph, restore just that orbit. Up to a base relabeling, it is one of the following:
1. another cross matching across a base edge;
2. a cross matching between layers in the same part of the \(K_{3,3}\) quotient;
3. an internal involution at one layer;
4. an internal non-involutory pair of opposite steps at one layer.

The cases are exhaustive because an edge orbit consists of either a translation matching between specified layers or one internal step orbit. The automorphism group of \(K_{3,3}\) is transitive on layers, on cross pairs, and on same-part unordered pairs. The original graph is simple, so the restored orbit satisfies precisely the nonvanishing requirements in §2. These four exact extension tables have respectively **10, 43, 7, 19** nonterminal relation states. All their evaluations have a \(4/8/16\)-cycle. Hence no deleted orbit could have existed, establishing the simple quotient and graph cubicity. The pullback of the base bipartition now gives an \(A\)-invariant bipartition of the original graph.

After switching the five spanning tree labels to zero, let \(H\le A\) be generated by the remaining four chord labels. In the lifted graph each connected component consists of one coset of \(H\) in each of the six fibers. Tree paths reach all layers with unchanged coordinate, each chord gives its shift via the fundamental closed walk, and no edge can leave the coset. Thus \(H\) gives a connected regular abelian \(K_{3,3}\) cover on each component. The rooted theorem supplies a \(4/8/16/32\)-cycle through each vertex; the first three lengths are excluded by hypothesis, so the cycle has length \(32\). The fixed-base census gives at least 798 vertices per component and, at equality, three nonisomorphic possibilities for the single component. Conversely these three connected lifts already supply free abelian actions on six orbits and have the required lengths. This completes the classification.

## Replay

Run `python3 verify_erdos_gyarfas_general_six_orbits.py` in this directory. Only the standard library is needed. The seven compressed blocks in the data file are ordinary UTF-8 JSON objects compressed with gzip and serialized as base64; each maps a quotient type to a dictionary taking its row-lattice key to a cyclic dart word. The small extension tables are stored without compression. The data and verifier are a finite proof for this specific scope, not a proof of the general conjecture.
