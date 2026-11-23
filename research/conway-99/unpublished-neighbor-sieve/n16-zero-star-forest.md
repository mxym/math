# The zero-height neighbourhood of a norm-sixteen marking

Let \(A\) be the adjacency matrix of a graph with the Conway parameters. Let \(t\ne0\) be an integral \(-4\)-eigenvector of squared norm 16. The claims below do not assume any value of the Seidel rank or absence of other short markings.

**Theorem.** The signs of \(t\) give two independent eight-sets \(P,N\), with a 4-regular bipartite graph between them. On the 83 exterior vertices put \(h(z)=|N(z)\cap P|=|N(z)\cap N|\) and write \(H_i=\{z:h(z)=i\}\), \(Z=H_0\). The populations are
\[
  (|Z|,|H_1|,|H_2|)=(11,64,8).
\]
The induced graph on \(Z\) is a forest with either five or six edges. If it has six edges, it has at most four wedges (unordered pairs of edges incident at one vertex). The induced graph on \(H_2\) has zero or one edge, respectively. Each component of \(Z\) is a path on at most four vertices or a claw \(K_{1,3}\). At a claw, six \(H_2\) sites see one each of the six pairs of claw vertices and two \(H_2\) sites see just its centre. If \(H_2\) has its one edge, its triangle cannot be capped at height one. The [subsequent cap proof](shared-norm-18/u226-norm16-disjoint.md) also excludes a support cap, so the cap lies in \(Z\).

There are also two 2-regular multigraphs, one on \(P\) and one on \(N\): for each \(z\in H_2\), put an edge between its two neighbours on each shore. The two multigraphs have the same component-size deck, one of \(8,\ 6+2,\ 4+4,\ 4+2+2,\ 2+2+2+2\), where a double edge is a component of size two. In any opposite shore each site sees exactly half the sites of every component. Whenever a pair of exterior sites gives a double edge on one shore, the pair is nonadjacent and has disjoint \(Z\)-neighbourhoods; it cannot give a double edge on the other shore.

## Signs and height populations

If an entry has magnitude at least two, orient it positive and subtract the ordinary site mark \(d_i=(3I-A)e_i\). The resulting integral field has charge \(-1\) and squared norm \(16+23-14t_i\le11\). Its coordinate sum is \(+11\), so equality is required and all entries would be nonnegative. But equality gives \(t_i=2\), and the translated entry there is \(-1\), a contradiction. Hence all nonzero entries are units, and \(\sum t_i=0\) makes both signs eight-sets.

For \(p\in P\) the number of neighbours in \(N\) is \(4+d_P(p)\), and conversely. The two same-sign edge counts therefore agree, say \(e\). Counting the common neighbours of pairs in \(P\) using only \(N\) gives
\[
56-e\ \ge\ \sum_{n\in N}\binom{4+d_N(n)}2\ \ge\ 48+8e.
\]
Thus \(e=0\). The equality of the exterior heights follows from the eigen-equation. If an exterior vertex met at least three positive sites, each of those three has four \(N\)-neighbours and any two share at most one of them (they already share the exterior vertex). Their union would have at least nine points in the eight-set \(N\), impossible. All exterior heights are at most two. The total positive exterior incidence is \(8(14-4)=80\); the remaining positive pair slots are \(56-8\binom42=8\). This yields the stated populations.

## The forest and its edge count

Write \(d_X(z)\) for the number of neighbours of \(z\) in \(X\). From \(A^2=12I-A+2J\), for every exterior \(z\),
\[
\sum_{\substack{y\sim z\\y\text{ exterior}}}h(y)=16-5h(z)
\]
because each of its \(h(z)\) negative neighbours contributes four and positive neighbours contribute zero. Together with the exterior degree \(14-2h(z)\), this gives
\[
d_{H_2}(z)=2+d_Z(z)\ (z\in Z),\quad
d_Z(y)=4+d_{H_2}(y)\ (y\in H_2),\quad
d_Z(x)=1+d_{H_2}(x)\ (x\in H_1).
\]
If \(e=e(Z)\), the number of \(Z\)-to-\(H_2\) edges is \(22+2e=32+2e(H_2)\). So \(e\ge5\), and \(e(H_2)=e-5\).

For any \(R\subseteq Z\), put \(r=|R|\), \(e_R=e(R)\), and \(w_R=\sum_{z\in R}\binom{d_R(z)}2\). Across the pairs in \(R\) at most \(2\binom r2-e_R-w_R\) common-neighbour incidences come from outside \(R\). Indeed adjacent pairs have only one common neighbour, and the \(w_R\) incidences from inside \(R\) are already used. If \(R\) is the vertex set of a simple cycle, \(e_R,w_R\ge r\), and every member has at least four neighbours in \(H_2\). The \(H_2\) family alone uses at least
\[
\sum_{y\in H_2}\binom{d_R(y)}2
\ \ge\ s^2/16-s/2\ \ge\ r^2-2r,\qquad
s=\sum_{y\in H_2}d_R(y)\ge4r.
\]
Here the first inequality is Cauchy--Schwarz over eight sites, and the expression is increasing for \(s\ge4\). This exceeds the capacity \(r(r-3)\). Thus \(Z\) is a forest.

The \(Z\)-to-\(H_1\) edge count is \(154-2e-(22+2e)=132-4e\). The two integer bounds \(\binom k2\ge k-1\) and \(\binom k2\ge4k-10\) give
\[
 \sum_{x\in H_1}\binom{d_Z(x)}2\ge68-4e,\qquad
 \sum_{y\in H_2}\binom{d_Z(y)}2\ge 8+8e.
\]
Using the full capacity \(110-e-w_Z\) therefore yields \(5e+w_Z\le34\). Combined with \(e\ge5\), this proves the edge and wedge assertions.

## The five allowed component shapes

In the earlier subset pair count, if a site of \(Z\) has degree at least four, take it and four of its neighbours for \(R\). The forest condition gives a four-star with outside pair capacity \(20-4-6=10\). The \(H_2\) incidence count is at least \(6+4\cdot3=18\) across eight sites, which uses at least twelve pairs by distributing the degrees as evenly as possible. Hence the maximum degree is three.

At a degree-three site take the centre and its three neighbours as \(R\). The outside pair capacity is \(12-3-3=6\), while the \(H_2\) incidence is at least \(5+3\cdot3=14\). For fourteen incidences the minimum pair usage is six, attained only with six degrees two and two degrees one. If any leaf has a further \(Z\)-neighbour, at least fifteen incidences give at least seven pairs, impossible. Thus this claw is an isolated component. Each of the six pairs of claw vertices has outside capacity exactly one, so each is the two-point trace of one \(H_2\) site. The two singleton traces must be at the centre to attain degree five there.

Finally, if \(Z\) contains a five-site path, take its middle three sites as \(R\). The pair capacity is \(6-2-1=3\). As each middle site has \(Z\)-degree at least two they have at least twelve incidences into \(H_2\), which use at least four pairs. So all non-claw components are paths on at most four sites.

## The cap of the unique height-two edge

Suppose \(e(Z)=6\), and call the \(H_2\) edge \(ij\) and its unique common neighbour \(x\). By the [norm-sixteen affine lift](shared-norm-18/exclusion.md#every-oriented-norm-16-vector-gives-a-different-unit-labeling-of-type-127), the original field and its opposite give the two fields \(b=1_{H_2}-1_{P\cup Z}\) and \(1_{H_2}-1_{N\cup Z}\), of charge one and squared norm 27. If \(x\notin Z\) select a lift with \(b_x=0\); this is possible both on the support and at height one. Let \(D_T=\sum_{v\in T}d_v\) for \(T=\{i,j,x\}\). The triangle mark \(D_T\) has squared norm 39, is \(+1\) on \(T\), and is \(-1\) on the 36 outside neighbours of \(T\), since none meets two triangle vertices. The dot product \(D_T\cdot b=7\sum_{v\in T}b_v+6=20\), so \(D_T-b\) has charge two and squared norm 26. Such a field is unit: a positive entry at least two gives, on subtracting the corresponding \(d_v\), a charge-one field of norm at most \(13\); a negative entry at most \(-2\) gives, on adding the corresponding \(d_v\), a charge-three field of norm at most \(29<33\). Its sum is \(-22\), so a unit field has exactly two positives, one at \(x\).

If \(x\) has height one, then \(T\) meets the neighbourhoods of exactly \(2+2+1=5\) sites on the selected negative support shore, with no repeats. The other three sites of that shore become further positive sites of \(D_T-b\), impossible. If \(x\) is a support site, the triangle meets the opposite shore on \(2+2+4=8\) distinct sites and has exactly ten distinct \(Z\)-neighbours from \(i,j\), with none from \(x\). The other positive site of \(D_T-b\) is the unique missed point of \(Z\); it is nonadjacent to \(x\). Given the resulting field and the choice of positive \(x\) and triangle at \(x\), the lift and then the oriented norm-sixteen field are recovered by the cited injectivity. There are at most \(2\cdot7=14\) such choices per charge-two field. In particular, if \(G_{2,26}\) counts the actual positive-charge fields of this type, the number of unoriented norm-sixteen lines with \(e(Z)=6\) and a support cap is at most \(14G_{2,26}\).

If \(x\in Z\), the two size-five \(Z\)-neighbourhoods of \(i,j\) meet only at \(x\), so they cover nine zero sites. Any \(Z\)-neighbour of \(x\) must be one of the two missed sites because an exterior vertex cannot meet two triangle vertices. In particular this cap cannot be the centre of a claw.

## The common-neighbour deficiency on the two shores

At a fixed positive site there are \(2\cdot7=14\) common-neighbour incidences with the other positives. The four negative neighbours each provide three, leaving exactly two incidences supplied by \(H_2\). Thus the multigraph on positives constructed from \(H_2\) is 2-regular, and likewise on negatives. If \(M\) is the \(8\times8\) support crossing matrix and \(B_P,B_N\) are these two multigraph adjacency matrices, common-neighbour quotas give the exact identities
\[
MM^\top=2I+2J-B_P,\qquad M^\top M=2I+2J-B_N.
\]
For any component \(L\) of \(B_P\), \(B_P1_L=2\cdot1_L\) implies \(\|M^\top1_L\|^2=2|L|^2\). The vector has coordinate sum \(4|L|\), so equality in Cauchy--Schwarz gives \(M^\top1_L=(|L|/2)\mathbf1\). In particular the component has even size. The same holds on the other side. The two matrices \(B_P,B_N\) are cospectral: on \(\mathbf1^\perp\) use the two Gram identities and identical singular spectra of \(M,M^\top\), and the constant eigenvalue is 2 on both sides. The multiplicity of eigenvalue 2 gives the component count. The only ambiguity among the five listed decks is between \(6+2\) and \(4+4\): a 6-cycle has eigenvalue 1, whereas a 4-cycle does not and a double-edge component has only the eigenvalues \(\pm2\). This distinguishes them.

For a double edge the corresponding exterior sites have already used two common-neighbour slots in the indicated shore. They therefore cannot be adjacent, cannot meet at a common \(Z\)-neighbour, and cannot share any further support neighbour on the other shore. In particular, if the deck is \(2+2+2+2\), the two partitions of \(H_2\) into exterior pairs from the two shores have no pair in common.

### A refinement of rooted-triple packing

At a given positive \(p\), consider its four negative neighbours. If \(p\) lies in a double-edge component, one other positive shares none of that four-set and the remaining six share two each. If it lies in a component of size at least four, two other positives share one each and five share two each. These statements follow directly from \(MM^\top\). Thus among the six pairs of the four negative neighbours, all six have their second common neighbour in \(P\) in the first case, and exactly five do in the second. In the terminology of [the existing rank-42 rooted-triple argument](norm16-packing.md), the four rooted triples have exactly four and exactly two good triples, respectively. If \(D\) is the sum, over all oriented norm-sixteen fields, of the number of double-edge components in their positive-shore deck, the earlier weighted bound strengthens to
\[
28N_{14}+24N_{16}+2D\le27\,720\qquad(r=42).
\]
There is no resulting all-rank exclusion of norm sixteen or of the ambient graph.

**Height-two overlap and four-cubes.** The [height-two edge theorem](shared-norm-18/norm16-edge-and-cube.md) forces an isolated zero-height cap and two missed zero-height sites, and removes 22 of 24 necessary portraits of an induced four-cube. The remaining two are not asserted to extend.
