# A weighted link-energy bound for tetrahedron-free triples with one reversed type

## Statement

Let a tetrahedron-free 3-uniform hypergraph have a partition \(A,B,C\), with all transversal triples \(ABC\) present. The only types allowed for nontransversal edges are
\[
AAB,\quad BBC,\quad CCA,\quad AAC,\quad AAA,\quad BBB.
\]
In particular \(C\) is independent; the optional reverse type is \(AAC\). There are no restrictions on the within-type incidence matrices beyond tetrahedron-freeness. Let \(a,b,c\) be the corresponding part masses, with \(a\le b\le c\). For the probability \(D\) that three independent vertex samples form an edge, one has
\[
D\le 6abc+3(a^2b+b^2c+c^2a)\le \frac59(a+b+c)^3 .
\]
Part masses can be cardinality proportions for the original finite problem, or any nonnegative weights assigned to vertices. This is a bound for the ordinary tetrahedron problem on the indicated family, not a bound on the unrestricted Turán density.

In the cardinality case \(a+b+c=1\), \(D=6|E|/n^3\), so \(|E|/\binom n3\le5/9+O(1/n)\). The balanced cyclic construction with complete \(ABC,AAB,BBC,CCA\) and no other edges attains \(5/9\) in the limit. For fixed proportions the first cubic bound is also asymptotically attained by the cyclic construction at those proportions. The inequalities for zero-mass parts follow by the same coefficient inequalities (if a part is empty in the weighted proof, the quantities involving a sample from it can be treated separately); in the zero-mass case \(a=0\) only \(BBC,BBB\) can contribute, and \(BBB\) is paid for by the \(BBC\) deficit exactly as below if \(b>0\), with the case \(b=0\) empty.

## Notation and disjoint pair targets

All probabilities below are independent samples with replacement from the indicated normalized parts. An edge always has three distinct original vertices. Thus pair diagonals can be regarded as missing wherever needed, and triple diagonals never form internal edges. Denote by \(Q(x,y)\) the indicator that \(x,y\) in \(A\) have an \(AAC\) extension, i.e. there exists a positive-mass \(z\in C\) for which \(xyz\) is an edge. Write \(s=\mathbb E Q(x,y)\), \(d(x)=\mathbb E_y Q(x,y)\) and \(t=\mathbb E_{x,y,w} Q(x,y)Q(y,w)Q(w,x)\).

If \(x,y\) have both a \(C\) extension and a \(B\) extension, those two vertices with \(x,y\) would form a tetrahedron by completeness of the transversal triples. Thus all \(Q\)-pairs have no \(AAB\) extensions. Let \(f\) denote the probability of selecting a non-\(Q\) pair in \(A\) and a \(B\) vertex giving a missing \(AAB\) triple; total \(AAB\) deficit is \(s+f\). Let \(g\) denote total \(BBC\) deficit. For \(x\in A\) let \(h(x)\) denote the density of missing pairs in the \(CCA\) link of \(x\), and \(\bar h=\mathbb E_x h(x)\). Let \(o\) denote density of edges of type \(AAC\) under the corresponding sampling. Let \(i_A,i_B\) denote internal triple densities.

For an internal \(A\) edge with no \(Q\)-pair, each \(B\) vertex misses at least one of its three \(AAB\) pairs (or there would be a tetrahedron). A union bound, discarding the other internal edge requirements, shows that such internal edges have density at most \(3f\). The probability that a random \(A\)-triple has any \(Q\)-pair is exactly \(3s-3\mathbb E d^2+t\) by inclusion-exclusion, even with replacement. Hence
\[
i_A/3 \le f+s-\mathbb E d^2+t/3.
\]
Similarly \(i_B/3\le g\), by considering a \(C\)-vertex on each \(B\) triple.

## Link-energy inequality

Fix \(x,y\in A\) with \(Q(x,y)=1\). Write \(S=\{z\in C:xyz\in E\}\). For every ordered pair in \(S^2\) at least one of the \(CCA\) edges with singleton \(x\) or \(y\) is absent. If the two \(C\)-vertices were distinct and both edges were present, they would make a tetrahedron with \(x,y\); if repeated, both edges are absent. Thus
\[
\mu_C(S)^2\le h(x)+h(y).
\]
For \(h(x)+h(y)>0\) put \(r_{xy}=\sqrt{h(x)/(h(x)+h(y))}\), and otherwise put \(r_{xy}=1/\sqrt2\). In all cases \(r_{xy}^2+r_{yx}^2=1\) and
\(\sqrt{h(x)+h(y)}=r_{xy}\sqrt{h(x)}+r_{yx}\sqrt{h(y)}\).
Set \(k(x)=\mathbb E_y Q(x,y) r_{xy}\). This proves
\[
o\le 2\mathbb E_x k(x)\sqrt{h(x)}.
\]
The following refinement uses orientation-free Gram overlap:
\[
\mathbb E k^2\le\mathbb E d^2-t/2.
\]
Indeed the difference equals
\(\mathbb E_{x,y,w}Q(x,y)Q(x,w)(1-r_{xy}r_{xw})\).
All summands are nonnegative. Restricting to triples which give a full \(Q\)-triangle, the integrand can be averaged over the choice of anchor. For each (ordered) triangle,
\[
r_{xy}r_{xw}+r_{yx}r_{yw}+r_{wx}r_{wy}
\le \tfrac12\sum_{\{u,v\}\subset\{x,y,w\}}(r_{uv}^2+r_{vu}^2)=3/2.
\]
This proves the claimed improvement. Finally, weighted Young applied to \(a^{3/2}k(x)\) and \(a^{1/2}c\sqrt{h(x)}\) gives
\[
a^2c\,o\le a^3\mathbb E k^2+ac^2\bar h
\le a^3(\mathbb E d^2-t/2)+ac^2\bar h.
\]

## Combining the terms

With \(F=6abc+3(a^2b+b^2c+c^2a)\), the exact excess over the standard cyclic template is
\[
(D-F)/3=-a^2b(s+f)-b^2c\,g-ac^2\bar h
+a^2c\,o+(a^3i_A+b^3i_B)/3 .
\]
Use the internal-edge and link-energy inequalities to obtain
\[
(D-F)/3\le
-a^2(b-a)(s+f)-b^2(c-b)g-a^3t/6\le0 .
\]
This displays an explicit penalty for switched triangles, beyond the mere \(5/9\) bound. For the second bound write \(a=x,\ b=x+y,\ c=x+y+z\) with \(x,y,z\ge0\), and expand:
\[
\frac59 (a+b+c)^3-F
=2x(y^2+yz+z^2)+\frac{13y^3+33y^2z+30yz^2+5z^3}{9}.
\]
Thus the sharp asymptotic constant in the stated family requires balanced masses.

## Nearly complete cross-edges

If \(ABC\) is not complete but the same nontransversal types are allowed, let \(\delta\) be the within-\(ABC\) density of absent triples. For a fixed \(A\)-pair \(x,y\), let \(U,V\) be its \(B,C\) extension sets, with masses \(p,q\) inside \(B,C\). On \(U\times V\) at least one of the two transversals with singleton \(x\) and \(y\) must be absent, by tetrahedron-freeness. Hence \(pq\le\delta_x+\delta_y\), where \(\mathbb E\delta_x=\delta\) and \(\delta_x\) measures missing \(BC\) pairs in \(x\)'s cross-link. Delete from the \(A\)-pair its outgoing edges to whichever of \(B,C\) has smaller **weighted** extension mass (compare \(bp\) and \(cq\)). Then \(A\)-pairs have disjoint targets; making \(ABC\) complete introduces no tetrahedra. To see this, any new tetrahedron would have to have type \(AABC,ABBC\) or \(ABCC\); the first is blocked by disjoint targets, the other two by the originally forbidden double types \(BBA\) and \(CCB\). Deleting edges cannot cause a tetrahedron.

The probability cost from deletions is bounded by
\(3a^2\mathbb E\min(bp,cq)\le3a^2\sqrt{2bc\delta}\). Filling the missing transversals adds \(6abc\delta\). Therefore
\[
D\le F+3a^2\sqrt{2bc\delta}-6abc\delta.
\]
This gives the same asymptotic constant for almost-cross-complete sequences.

## Strict noncontainment from Fon-der-Flaass

A restriction of a Fon-der-Flaass complement to a vertex subset is again a Fon-der-Flaass complement (use the induced oriented graph). The family addressed here is not contained even in the downward closure of the Fon-der-Flaass complements, as follows without using any claimed \(5/9\) theorem.

On \(m\) labelled vertices let \(R\) include each triple independently with probability \(m^{-1/2}\). For each labelled orientation with no induced directed 4-cycle, its Fon-der-Flaass complement is tetrahedron-free, so it omits at least \(\tfrac14\binom m3\) triples, by counting missing-triple incidences on four-sets. The number of edges of \(R\) outside that complement has mean at least \(\tfrac14 m^{-1/2}\binom m3=\Omega(m^{5/2})\). A binomial lower-tail Chernoff bound says that with probability \(1-\exp(-\Omega(m^{5/2}))\) it is at least half its mean. There are at most \(3^{\binom m2}\) orientations, so with probability tending to one \(R\) has \(\Omega(m^{5/2})\) edges outside *each* candidate completion, with a uniform constant.

Meanwhile the expected number of tetrahedra in \(R\) is \(\binom m4 m^{-2}=O(m^2)\). With probability tending to one their number is at most \(m^{9/4}\), by Markov. For a realization satisfying both events, deleting at most one edge per original tetrahedron produces a tetrahedron-free \(H_0\) still not contained in any Fon-der-Flaass complement. For any \(N\ge m\), start with the standard cyclic construction on \(A,B,C\) of size \(N\), and choose \(U\subseteq A\) of size \(m\). Delete every \(AAB\) edge whose \(A\)-pair is in \(U\), and put \(H_0\) on \(U\). This satisfies the hypotheses and remains tetrahedron-free. A new tetrahedron would have to contain an internal edge in \(U\); it cannot be entirely in \(A\) because \(H_0\) is tetrahedron-free, cannot extend to \(B\) by the deletions, and cannot extend to \(C\) because \(AAC\) is absent. No Fon-der-Flaass complement contains this witness because no such complement contains its \(U\) restriction. The probability-density loss relative to the standard cyclic construction is at most \(6N\binom m2/(3N)^3=O((m/N)^2)\), so the asymptotic density of the blow-ups below can be arbitrarily close to \(5/9\) by choosing a large fixed \(N/m\) (the probability-density deficit of the size-\(3N\) cyclic construction itself is \(1/(3N)\)).

This also yields a positive edit-distance separation in the \(n\to\infty\) setting: take the equal blow-ups of this fixed witness, replacing each vertex by \(L\) independent clones. For any candidate Fon-der-Flaass complement on the \(3NL\) vertices, a transversal of the \(3N\) clone classes (one vertex from each) restricts to a completion on the witness's order, so it misses at least one specified edge. Averaging over independent uniformly random clone representatives shows that at least \(L^3\) blow-up edges are absent in the proposed complement. Thus separation is at least \(L^3/\binom{3NL}{3}\) in normalized edge counts. Taking \(L\to\infty\) with \(N\) fixed shows positive normalized edit distance. Taking large \(N/m\) lets the proven density approach \(5/9\) as closely as desired, with a correspondingly smaller but still positive fixed separation for each choice of \(N\). This does not show a universal separation bounded away from zero as density tends to \(5/9\).

An explicit small choice of \(H_0\), on vertices \(0,\ldots,5\), is
\[
123,\ 024,\ 034,\ 134,\ 234,\ 015,\ 025,\ 125,\ 135,\ 045.
\]
The companion `verify_tetrahedron_fdf_noncontainment.js` first checks that none of its 15 four-sets forms a tetrahedron. It then assigns each of the 15 vertex pairs one of the three orientation states (absent or either direction), using the induced-triple criterion (no isolated vertices and no vertex of outdegree two) for each required edge and excluding induced directed four-cycles. It discards a branch only when all pairs of a violating required triple or quadruple have been assigned; every valid completion would reach a leaf. It checks 9,733 nodes with none reaching a valid leaf. The probabilistic noncontainment proof above does not depend on this computational witness.

## Literature and scope

The ordinary conjecture (still open in the primary sources searched) is surveyed in https://people.maths.ox.ac.uk/keevash/papers/turan-survey.pdf, section 3.1. Current ordinary upper bound in Jeong, Park, Im, Lee, Yang, v2: https://arxiv.org/abs/2609.27495. The distinct uniform Turán theorem does not imply the ordinary conjecture: https://arxiv.org/abs/2609.08336.

The initial suggested target was the Fon-der-Flaass 4/9 conjecture. The independent recent preprint by Flynn Bettens posted Nov 24, 2026 already claims this exact result, using rational flag-algebra certificates and a Lean formalization; not peer reviewed and not independently replayed here: https://zenodo.org/records/24508905. Earlier literature includes Razborov https://arxiv.org/abs/1008.4707 and Veronica Phan https://arxiv.org/abs/2507.17666. The present algebraic bound uses the given 3-graph directly and does not require any orientation on its pairs. It is not a competing proof of the Fon-der-Flaass theorem. A sharp finite-order bound, complete removal of the template conditions, and the unrestricted ordinary Turán conjecture are not claimed here.
