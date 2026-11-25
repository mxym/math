# Sharp large-k entropy in the injective graph model

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Use the graph model and local edge-connectivity criterion of [Erdos817GraphCutClassification.md](Erdos817GraphCutClassification.md). Let \(G\) have \(e>0\) edges and no \(k-1\) edge-disjoint paths between distinct vertices. Let \(W(G)\) be the set of integer vertex-boundary vectors of all subsets of any orientation of \(E(G)\); reversing any edge just translates the whole set. Put \(a=(k-1)/2\). Then
\[
 |W(G)|\ge (1+a)^{e/a}.
\]
Consequently for numerical marks whose projection is injective on \(W(G)\), including the explicit cut-coordinate construction, the least possible logarithmic subset-sum cardinality per edge is \((2+o(1))\log(k)/k\) as \(k\) tends to infinity. This does not bound a noninjective projection.

**Forest identity.** The graphic zonotope is the image of the real cube under the oriented incidence matrix. Every integer point in its image has a cube preimage with entries in \(\{0,1\}\): impose the integer prescribed boundary and the bounds 0 and 1, then use total unimodularity of the incidence matrix (equivalently, integer feasible flow). The incidence vectors form a unimodular configuration; a forest's columns are a basis of their lattice span, by repeatedly removing leaves. [Stanley's lattice-zonotope formula, as stated for graphical zonotopes by Postnikov](https://math.mit.edu/~apost/papers/permutohedron_full.pdf), therefore counts these integer points by all independent sets of columns, exactly the forests of \(G\).

**Counting forests using local edge connectivity.** Every subgraph \(J\) inherits the path constraint; the cut-tree density estimate gives \(|E(J)|\le a\,\mathrm{rank}(J)\), where \(\mathrm{rank}(J)\) is its graphic-matroid rank. If an ordered forest has \(i\) edges, its components span an induced-edge union whose rank is \(i\). That union contains at most \(ai\) edges; every other edge can extend the forest. Consequently writing \(M=\lfloor e/a\rfloor\), the number of \(t\)-edge forests for \(0\le t\le M\) is at least
\[
 \frac{\prod_{i=0}^{t-1}(e-ai)}{t!}\ge a^t\binom{M}{t}.
\]
Summing gives \((1+a)^M\). Apply the same bound to \(N\) disjoint copies of \(G\), for which the number of forests is raised to the \(N\)th power, then take \(N\)th roots and let \(N\to\infty\).

**Matching first order.** Let \(s=k-1\) and take \(K_s\), with exactly \(s-1=k-2\) edge-disjoint paths between any distinct vertices (the direct edge and the paths through individual other vertices); use its injective marking. Every forest on these \(s\) vertices can be extended injectively to a tree on \(s+1\) vertices by adjoining one new vertex and connecting it to the least-labelled vertex of each component. Cayley's formula gives at most \((s+1)^{s-1}\) forests, hence log cardinality per edge at most \(2\log k/(k-1)\), matching the first order of \(a^{-1}\log(1+a)\). Disjoint unions attain the same per-edge upper rate with arbitrarily many generators. No conclusion is made about optimal scalar marks that merge different boundary vectors.
