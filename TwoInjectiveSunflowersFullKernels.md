# Sharp full-kernel internal sunflowers with capped pair multiplicity

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Let \(m\ge2\), \(1\le D\le m\), and let \(H\) be a nonempty tripartite 3-uniform family on \(A,B,C\). Assume its \(AB,AC\) pair projections are injective and each \(BC\) pair occurs at most \(D\) times. Say \(F\subseteq H\) is fully valid if for every two distinct edges \(e,f\in F\), their intersection \(e\cap f\), now including the empty set, is the kernel of an \(m\)-petal sunflower entirely in \(F\).

**Theorem.** The worst-case fraction that can be fully retained is \(\Theta(1/(m^2D))\), uniformly over the stated range. This is a restricted case of the question in [Janzer–Jin–Sudakov–Wu, Section 6](https://link.springer.com/article/10.1007/s00493-026-00222-1#Sec6). In contrast, if the empty intersection is exempted, the sharp fraction in this class is \(\Theta(1/(m^{3/2}\sqrt D))\) by the [companion proof](TwoInjectiveInternalSunflowers.md).

## Lower bound

Write \(E=|H|\) and let \(\Delta\) be its largest vertex degree.

If some vertex \(v\) has degree \(\Delta\ge E/(6m)\), work only with its incident edges. When \(v\in A\), its link (the pairs left after removing \(v\)) is a matching because both pair projections at \(A\) are injective. Thus take all edges if the degree is at least \(m\), and a single edge otherwise. This always keeps at least \(\Delta/(mD)\). When \(v\in B\), the \(A\) labels of its incident edges are distinct, while each \(C\) label occurs at most \(D\) times. If at least \(m\) distinct \(C\) labels occur, choose one edge per \(C\); the resulting family is a sunflower of at least \(m\) petals with kernel \(\{v\}\), and keeps at least \(\Delta/D\). If fewer occur, \(\Delta<mD\), so a single edge suffices for the stated bound. The case \(v\in C\) is symmetric. These subfamilies have no empty pair intersections, hence are fully valid, and retain at least \(E/(6m^2D)\).

If \(\Delta<E/(6m)\), greedily reserve \(m\) pairwise disjoint edges. Each choice deletes at most \(3\Delta\) original edges meeting its vertices, so the reservation succeeds and leaves more than \(E/2\) edges disjoint from all reserved vertices. Apply the companion nonempty-kernel theorem to the remaining family. The union of its output with the reserved \(m\)-matching is fully valid: the reserved matching supplies the witness for every empty intersection, and all nonempty intersections already have witnesses in the extracted remainder. Its size is \(\Omega(E/(m^{3/2}\sqrt D))\), and therefore also \(\Omega(E/(m^2D))\).

## Matching upper bound

Let \(d=\min(D,m-1)\). Make \(m-1\) disjoint blocks. In each block, fix a private vertex \(b\) and \(m-1\) private \(C\) labels; for each such label use \(d\) new \(A\) labels, each used once. Thus there are \((m-1)^2d\) triples overall, the two projections are injective, and the maximum \(BC\) codegree is \(d\le D\).

The entire family has no \(m\)-matching because there are only \(m-1\) distinct \(B\) vertices. So fully valid \(F\) cannot meet two blocks, or else two disjoint retained edges would require an empty-kernel witness. Within a block, \(F\) cannot repeat a \(BC\) pair because it occurs fewer than \(m\) times. Two edges using distinct \(C\) labels intersect in \(b\) alone, but there are fewer than \(m\) labels, precluding an \(m\)-petal sunflower with that kernel. Hence \(|F|\le1\). As \(d\ge D/2\), the retention is \(O(1/(m^2D))\), as claimed.
