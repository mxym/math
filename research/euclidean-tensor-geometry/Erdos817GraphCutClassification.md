# Which graphs admit progression-free edge differences?

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Let \(G=(V,E)\) be a finite simple graph and \(k\ge3\). We ask whether one can assign distinct integer marks \(t_v\) to the vertices so that the positive edge distances \(A=\{|t_v-t_u|:uv\in E\}\) are pairwise distinct and the set \(H(A)\) of all their subset sums contains no nonconstant \(k\)-term arithmetic progression. There is an exact criterion:

> Such a marking exists if and only if no two vertices are joined by \(k-1\) edge-disjoint paths.

If the criterion holds and \(h=|V|-\#\{\text{components of }G\}>0\), the largest generator can be made smaller than \(2p^{h-1}\) for any prime \(p\ge k\). In these markings the scalar observation is injective on the distinct graphical boundary vectors. This classifies a graph model, not all feasible integer generator sets or the rate of [Erdős problem 817](https://www.erdosproblems.com/817).

The graphical factorization and the path obstruction are prior work; see [Section 3 of the public workbench](https://github.com/KokunoYumeto/erdos-problem-817-workbench/blob/main/research/graphical_obstructions/notes/graphical-obstructions.md). The reverse direction below uses a [Gomory–Hu cut tree](https://doi.org/10.1137/0109047) and the [restricted-digit argument of Korsky, Lemma 6.1](https://arxiv.org/html/2606.24139v1#S6).

**Prior work and scope.** The [September 15 workbench, Theorems 3.1 and 4.1 and equation (5.2)](https://github.com/KokunoYumeto/erdos-problem-817-workbench/blob/bb9c492ad2dbc520b3d619e013fa70d22ed8ac54/research/supported_defects/notes/graphic-visibility-filtration.md), already establishes the exact vector progression threshold from Gomory–Hu coordinates and the same cut-tree density bound. The qualitative existence criterion is a consequence: a generic rational linear evaluation avoids the finitely many equality hyperplanes for marks and absolute edge distances and avoids creating a scalar progression from a nonprogression of boundary vectors. Scale the resulting marks to integers. The following is a direct quantitative marking with an explicit generator bound and a mixed-prime capacity calculation, not a novelty claim for the qualitative criterion or density bound.

## Necessity

If \(k-1\) edge-disjoint paths join \(u\) to \(v\), orient each walk from \(u\) to \(v\). On each path, the signed sum of its positive edge distances is \(d=t_v-t_u\ne0\). Start with the sum of all negatively signed generators on the paths. For each path in turn, replace its negative terms by its positive terms. Each substitution increases the sum by \(d\), and the choices are disjoint as the paths share no edges and generators are distinct. This gives \(k\) distinct subset sums in arithmetic progression.

## Sufficiency via cut coordinates

Use the disjoint union \(T\) of Gomory–Hu trees for the connected components, with unit capacities on the original graph. For each edge of \(T\), its two sides in its component form a cut having size equal to the corresponding tree-edge min-cut value. All these cuts have at most \(k-2\) original graph edges crossing them by the hypothesis and max-flow/min-cut.

Number the \(h\) tree edges from \(0\) to \(h-1\); choose one side of each cut. Define the mark of a vertex to be the sum of \(p^i\) for cuts \(i\) whose chosen sides contain it. Different vertices in one component have distinct indicator vectors, hence distinct marks. One may translate all marks of each component by a constant, if needed, to make every vertex mark distinct globally, without changing edge differences.

Each positively oriented graph edge has a vector of cut differences in \(\{-1,0,1\}^h\) and at least one nonzero coordinate. Within its component, its support is the full tree path between its endpoints, so different edges have different supports. Edges in different components have disjoint, nonempty supports. Evaluating at \(1,p,\ldots,p^{h-1}\) is injective on \(\{-1,0,1\}^h\): the difference of two distinct vectors has coefficients in \([-2,2]\), and its highest nonzero term outweighs all smaller terms because \(p\ge3\). The positive numerical differences are therefore nonzero, distinct, and less than \(2p^{h-1}\).

In any cut coordinate \(i\), at most \(k-2\) edge vectors contribute any nonzero amount. Thus the \(i\)-coordinates of all sums of edge vectors are contained in an integer interval of width at most \(k-2\). Subtract the sum of the negative coordinate contributions independently in each coordinate. This translates every numerical subset sum by one and the same integer and leaves all digits in \(\{0,\ldots,k-2\}\), with no carrying. The evaluation is injective on this digit box. If the resulting integer set had a \(k\)-term progression with nonzero step \(d\), at the first nonzero base-\(p\) position of the step its digits would realize \(k\) distinct residues modulo \(p\). The allowed digit set has only \(k-1\) residues. This proves sufficiency.

## Size consequences and the limit of the model

Each original edge contributes the length of its path in \(T\) to the sum of the fundamental cut sizes. At most \(h\) original edges have length one, and all others have length at least two. Therefore
\[
2|E|-h \ \le\ \sum_{i=0}^{h-1}|\delta_G(\text{cut }i)| \ \le\ (k-2)h .
\]
In particular \(|E|\le(k-1)h/2\), the usual weak edge-density bound for this edge-connectivity constraint. For the displayed inequalities to be equalities, every cut must have size \(k-2\), every tree edge must be an original edge, and every additional edge must connect vertices at tree distance two. Conversely a spanning forest obeying those cut and distance conditions implies the density equality and the connectivity constraint, since a fundamental cut along the path separates any two vertices of its component.

The same density bound holds for all induced subgraphs (they inherit the path constraint). Hence \(G\) has a vertex ordering with at most \(k-2\) later neighbors per vertex. Let \(d_i\) be the number of later neighbors and express the original graphical boundary vectors in the natural vertex coordinates with one sign at each endpoint. When processing the vertices in this order, group each edge at its earlier endpoint. At vertex \(i\) the \(d_i\) signed contributions give \(d_i+1\) distinct possible sums, and later groups do not affect that coordinate. Choosing one witness for each sum in each group yields at least \(\prod_i(d_i+1)\) distinct full boundary vectors. The cut coordinates determine a zero-sum vertex boundary vector in each component: their subtree sums recursively recover the individual vertex coordinates. Consequently the constructed scalar marking, and more generally any marking injective on these boundary vectors, satisfies
\[
|H(A)|\ \ge\ \prod_i(d_i+1)\ \ge\ (k-1)^{|E|/(k-2)}.
\]
The last inequality follows from concavity of \(\log(1+x)\) on \(0\le x\le k-2\). This says nothing about how many vectors an arbitrary numerical marking may merge.

## Mixed prime bases

For a cut of width \(w_i\le k-2\), one may choose a different prime radix \(p_i\ge w_i+2\) at each position, and replace \(p^i\) by \(Q_i=\prod_{j<i}p_j\). All radices are at least three if only connected nontrivial components are used. As before every highest nonzero term of a difference in \([-2,2]^h\) outweighs the lower terms. After translation each allowed digit lies in \(\{0,\ldots,w_i\}\). If \(d\) is a nonzero progression step, the least position \(i\) with \(Q_{i+1}\nmid d\) exists because every translated number is in \([0,Q_h)\); at that position the first \(\min(k,p_i)\) residues in the progression are distinct, but \(w_i+1<\min(k,p_i)\). Thus the construction remains safe.

This does not improve the best per-edge logarithmic capacity cost within this model. For \(L_k=\min_{p\ge3\text{ prime}}\log p/(\min(p,k)-1)\), one has \(\log p_i\ge L_k(w_i+1)\), so the cut-distance inequality gives
\[
\log Q_h=\sum_i\log p_i\ge L_k\sum_i(w_i+1)\ge 2L_k|E|.
\]
This ratio is attained by disjoint cliques of order \(\min(p,k)-1\) at a minimizing \(p\), with a star cut tree in each clique and the constant radix \(p\). The assertion concerns this cut-coordinate capacity cost, not the unrestricted exponent or a particular smaller numerical maximum.
