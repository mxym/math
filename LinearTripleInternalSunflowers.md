# Sharp internal sunflower extraction for linear triple systems

**Yongxian Zhang.** AI-assisted research and internal mathematical verification; no external peer review claimed.

Fix \(m\ge2\). Call a subfamily *nonempty-kernel-valid* if every nonempty intersection of two of its edges is the kernel of an \(m\)-petal sunflower in the subfamily. For a linear 3-uniform hypergraph \(H\), the worst-case proportion of edges one can keep is
\[
\Theta(m^{-3/2}).
\]
If the empty kernel is required as well, the sharp worst-case proportion for linear systems is \(\Theta(m^{-2})\). This is a special case and variant of the internal-witness problem raised by [Janzer–Jin–Sudakov–Wu, §6](https://link.springer.com/article/10.1007/s00493-026-00222-1#Sec6); it does not settle the unrestricted 3-uniform question. In a linear hypergraph, all nonempty intersections are singletons, and each vertex in a nonempty-kernel-valid subfamily has degree 0, 1, or at least \(m\), an equivalent condition.

## Lower bound for nonempty kernels

Partition the vertices into three parts \(A,B,C\), retaining at least a \(2/9\) fraction of the edges meeting each part once, by independent random coloring. Work in this tripartite linear hypergraph. Repeatedly delete vertices of degree less than \(m\), assigning each lost edge to its first deleted vertex. The surviving core already has the desired property. Otherwise it suffices to handle the edges assigned to one part, say \(A\); in this piece every \(A\)-vertex has degree less than \(m\).

Each edge in the piece corresponds to a distinct edge of the simple bipartite \(B,C\) projection, labeled by its \(A\)-vertex. Peel vertices of projection degree less than \(D=\lceil 16m^{3/2}\rceil\). This splits the piece into at most two edge classes assigned to their first deleted endpoint and the remaining projection core. It suffices to find a suitable fraction in each class.

In the class assigned to \(B\), each \(B\)-vertex has degree less than \(D\). Select a maximum-size family that is a union of vertex-disjoint stars centered in \(C\), each of size one or at least \(m\). Within each star, linearity ensures distinct leaves in both \(A\) and \(B\). The selected family is valid. Delete the original edges touching the selected \(A,B\) leaves, at cost at most \((m+D)\) times the family size. Every residual edge has its \(C\) endpoint at a selected singleton center: otherwise it could be added at an unused center or an existing large star. At each singleton center there are fewer than \(m-1\) residual edges, because otherwise we could enlarge it to an \(m\)-edge star. Thus the selected size is at least the class size divided by \(D+2m\). The class assigned to \(C\) is symmetric.

Now suppose the projection core has \(e\) edges and \(v\) nonisolated vertices, so \(v\le 2e/D\). Independently keep each \(B,C\) vertex with probability \(m^{-1/2}\). Keep an edge with both endpoints sampled only if its \(A\)-label occurs on exactly one sampled edge. Since edges with a common \(A\)-label have pairwise disjoint \(B,C\) endpoints and there are fewer than \(m\) such edges for each label, every edge survives with probability at least
\[
\frac{1}{m}\left(1-\frac1m\right)^{m-1}\ge\frac{1}{4m}.
\]
Next peel sampled \(B,C\) vertices of current degree less than \(m\), losing at most \(m\) times the number of sampled projection vertices. The expected loss is at most \(\sqrt{m}\,v\le e/(8m)\), so some outcome retains at least \(e/(8m)\). Its \(A\)-degrees are at most one, and its positive \(B,C\)-degrees are at least \(m\). Taking the best of the constant number of classes proves the lower bound.

## Matching obstruction

For large \(m\), take two classes \(B,C\) of size \(n=m^8\) and a random bipartite graph with independent edge probability \(d/n\), where \(d=\lfloor m^{3/2}/100\rfloor\). With probability tending to one it has between \(nd/2\) and \(2nd\) edges and maximum degree at most \(2d\). In addition, with probability tending to one, for every pair \(X\subseteq B,Y\subseteq C\) with \(|X|,|Y|\le 8nd/m^2\),
\[
e(X,Y)\le \frac{m}{4}(|X|+|Y|).
\]
Indeed, writing \(x=|X|,y=|Y|\), the expected count is \((d/n)xy\le (4d^2/m^2)(x+y)\le .001m(x+y)\). A binomial tail bound at \(m(x+y)/4\) is at most \(2^{-m(x+y)/4}\); there are at most \(n^{x+y}\) pairs of sets of the given sizes. Sum over \(x,y\), with empty sets trivial and \(\log n=o(m)\).

Fix such a graph. By bipartite edge-coloring, partition its edges into at most \(2d\) matchings, then split each matching into blocks of at most \(m-1\) edges. Give every block its own \(A\)-label. There are at most \(2nd/(m-1)+2d\le 8nd/m\) labels. Lift each edge to a triple by adding its label. This gives a linear 3-uniform hypergraph with at least \(nd/2\) edges. In a valid selection of \(s\) edges, every \(A\)-label occurs at most once, so \(s\le8nd/m\). The sets \(X,Y\) of selected \(B,C\) vertices of degree at least \(m\) each have size at most \(s/m\). Edges between them number at most \(m(|X|+|Y|)/4\le s/2\). All other selected edges meet at least one degree-one vertex in \(B\cup C\), so number at most \(2n\). Thus \(s\le4n\), proving the matching upper bound on the fraction.

## Adding the empty kernel

If an \(m\)-matching exists in the original linear hypergraph, reserve one and remove all edges meeting its vertices. If at least half the edges remain, apply the nonempty-kernel bound to the remainder and add the reserved edges. The reserved matching supplies an internal sunflower with empty kernel without creating new nonempty intersections.

If at least half the edges are removed, some vertex of the reserved matching has degree at least \(e(H)/(6m)\). If there is no \(m\)-matching, the endpoints of a maximal matching of fewer than \(m\) edges cover the graph, with the same degree conclusion. If the high-degree vertex has degree at least \(m\), its entire star is valid, as all pairs intersect at its center and there are no disjoint pairs. Otherwise \(e(H)\le6m^2\), so a singleton suffices. These alternatives give the universal \(\Omega(m^{-2})\) full-kernel fraction.

For sharpness, take \(m-1\) disjoint vertex blocks each supporting a linear star of \(m-1\) triples. No two edges can be retained: a same-star pair has no \(m\)-petal witness at its center, and a pair from different stars has no \(m\)-matching anywhere. The original family has \((m-1)^2\) edges.
