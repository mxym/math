# The two-type face forces equal projective classes and Hoffman cocliques

Assume the graph has only neutral norms 18 and 24 among the twelve selected unit types of [the shell test](../short-shell-moments.md#when-the-nonzero-labels-must-all-be-signed-units). This face is already excluded at ranks 36 and 38; the conclusion applies in every maximal determinant-49 extension at the remaining ranks 40 and 42. It rules out no whole rank.

Fix a maximal isotropic subgroup H at seven and its rank-44 extension. In the residual anisotropic plane every nonzero norm occurs on eight vectors, that is, four opposite pairs. **The numbers of eligible oriented norm-18 vectors in these four opposite pairs are equal.** The assertion also holds for norm 24 and for the sum over opposite seven-classes at positive charges in the four shells (1,29), (2,32), (3,35), (4,44). This is an equality of counts, not a graph symmetry.

In particular the eligible oriented neutral counts in norms 18 and 24 are multiples of eight: in each opposite pair, negation bijects the two individual classes. Hence the folded count W018 is an integer. For positive charge we assert projective equality only, implying a multiple of four for the total, not necessarily eight.

The [fixed-extension identity](higher-moments.md#a-quantitative-target-for-the-remaining-pair), with the zero shell W000=1, is
```
6 W018 = 93 + 2 W014 + 2 W123 + 5 W222 .
```
All of W014, W123 and W222 have zero class in the residual anisotropic plane and denote actual integer populations. Therefore **W222 is odd, in particular positive**, in every H. Such a labeling is exactly the negative indicator of a Hoffman 22-coclique C: each vertex outside C has four neighbors in C, by its charge-two equation. Using W123 at least 99 gives W018 at least ceil((93+198+5)/6)=50, hence at least **400** eligible oriented norm-18 markings. Averaging over H as in the shell test gives a total graph bound N18 at least 50(7^((44-r)/2)+1) in this face; respectively 2500 and 400 at ranks 40 and 42.

The coclique is perpendicular to all eligible norm-18 fields t in the graph-coordinate dot product: the two seven-classes pair trivially because C has residual class zero, and the three-component of t vanishes. Equivalently 7 divides t·1_C, using the charge-zero pairing formula 7(y_t,y_c)=t·c for c=-1_C and integrality of the eligible seven/three pairing. This can also be seen from the anisotropic plane: even if the charge-two representative has a 3-part, t has none. Its absolute value is at most nine. An absolute value seven would produce a charge-two field c+t or c−t of squared norm 22+18−14=26, forbidden here. Therefore C meets the nine positive and nine negative sites of t in the same number k. In fact k≤3. Outside the support C has 22−2k sites, and the sum of their heights (neighbors on either sign) equals 4(9−k)−4k=36−8k, counting all walks from the positive sites to C and using bipartite degree four on the support. Thus k≤4, but k=4 requires at least ten height-zero sites, exceeding nine by [the universal height counts](height-three.md). No distinct cocliques across different H are asserted.

## Unaveraged residues

Use exactly the four rank-48 unimodular gluings and the harmonic quadratics of [the shell proof](../short-shell-moments.md#four-unimodular-lattices-from-the-same-extension). Do not average over the sixteen anti-isometries yet. Fix one as reference and label the graph classes by their images in the discriminant plane of K, the rank-four summand with Gram B=diag(B0,B0), B0=((2,1),(1,4)). For a four-space projection h let g be its column of pairings against the K basis multiplied by d=1 in the unshifted gluing and d=3 in a shift. Its seven-class is represented by
```
c=((g0+5g1)/d, (g2+5g3)/d) modulo 7.
```
Indeed the two columns of B0 map to zero, the map is onto, and the bilinear form induced by 7 B0-inverse is 4 times the ordinary dot product on these coordinates. The seven-primary part is unchanged by shifts of index a power of three. In particular dividing by d is legitimate over F7. The reference anti-isometry can be changed by any orthogonal matrix O of the ordinary plane; whether one calls O the change or its inverse is immaterial since all are used.

For each ordinary norm/charge (a,n), let X(a,n,[c]) be its count in one class averaged over the opposite pair [c]={c,−c}; when c=0 take the full count. For a>0 use just positive charge. Average the equations for the changes O and −O: this gives precisely the X variables even in the shifted gluings, without assuming any equality at opposite classes for a positive charge. Thus the expected multiplicity at a K projection g is X(a,n,[Oc]), doubled for a>0 to include the opposite full vector. The separate charge-zero term is not doubled.

For every O, shift e and i≤j, form a row by summing
```
2g_i g_j − B_ij g_0^2
```
with these multiplicities over the norm-four shell and with 48 times the multiplicities on the norm-two shell. The row is zero by the weight-26 cusp identity. A perpendicular root projects to zero, so only the surviving K roots contribute at norm two; their fixed contribution can be put in the column X(0,0,0)=1. The entire rank-four projection enumeration is finite and reproduced in the checker. The charge ranges, positive/negative folding, shift cosets and residual norms are those of the cited shell proof.

When deleting columns it is important to use true graph counts. The shells (0,16),(0,20),(1,21),(2,26),(2,28),(2,30),(3,37) are unit-only. For (0,26) and (1,25) the nonunit contributions vanish because (1,21) and (0,16) vanish. At (1,27) the [exact site translation](../short-shell-moments.md#when-the-nonzero-labels-must-all-be-signed-units) leaves nine times the count of (0,18), *in the same seven-class*: add the marked field 3e_i−Ae_i at one of the nine negatives, with no other source since (2,26)=0. This translation has zero seven-component.

The [standard-library checker](two_type_residue_balance.py) sums thirteen of the genuine rows with small integer multipliers, obtaining exactly
```
1728 ( X(0,18,[(2,3)]) − X(0,18,[(2,4)]) ) = 0.
```
Orthogonal rotation ((2,5),(2,2)) acts cyclically on the four opposite pairs of this quadratic value; rotating the reference anti-isometry gives the other equalities. The other five projective equalities are checked by exact rational elimination of all 640 generated rows (16 changes, four gluings, ten quadratics; rank 30). Run `python3 two_type_residue_balance.py` without third-party packages. No external solver result enters the proof.

## At least 42 disjoint intersecting-support pairs in every extension

This strengthens the [overlap matching argument](two-type-overlap-matching.md) using equal class sizes and the required Hoffman coclique. Select 50 representatives from one signed residue class on each of the four directions. This is possible by the integer bound above and negation. Join representatives whose ordinary dot product has absolute value 6 or 7, as in the earlier argument. After removing the endpoints of a maximal matching the remaining graph has no edges.

Write \(n_i\) for the size of each of the four remaining classes; \(0\le n_i\le50\). The same-class affine difference spaces have dimension at least
\[
d(n_i)=\left\lceil\frac{24(n_i-1)}{n_i+24}\right\rceil
\quad\text{if }n_i>0,\qquad d(0)=0
\]
by the earlier centered Gram estimate. In the edgeless remainder, dots between two different signed classes are constant on each class pair, so their affine difference spaces are mutually orthogonal. In addition, all retained vectors lie in the part of the \(-4\) eigenspace perpendicular to the centered indicator \(1_C-\frac29\mathbf1\) of the compatible coclique. This part has dimension 43.

The four projective directions can be written \((1,0),(0,1),(2,2),(2,-2)\) with the pairing \(4I\) over \(\mathbb F_7\). If at least three classes remain, two of them pair to zero and a third pairs nontrivially with both. The ordinary interclass dots on the edgeless set are \(0,1,-1\) according to their residues, by the same distance exclusions as in the earlier matching proof. Projecting one vector from each class to the complement of all within-class difference spaces preserves the interclass dots. Hence two perpendicular projections are nonzero (both pair nontrivially with the third), and this complement requires at least two more dimensions. We obtain
\[
\sum_i d(n_i)+2\,[\#\{i:n_i>0\}\ge3]\le43.
\]
The companion checker tests every sorted integer quadruple in \(0,\ldots,50\) and finds the maximum of \(\sum_i n_i\) under this inequality is 117, attained for example at \((1,16,50,50)\). Therefore at least \(200-117=83\) endpoints were removed and the matching has at least 42 edges. Each edge gives two norm-18 supports sharing six or seven sites, as proved in the earlier argument; the 84 supports can all be chosen distinct. This is a constraint on any graph on the two-type face, not a graph realization or a rank exclusion.

A vertex cover of the same 200-vertex overlap graph must delete at least 83 vertices by the same dimension inequality. Choosing one endpoint of every edge always gives a vertex cover; therefore there are also at least **83 distinct overlapping pairs in each extension**, without requiring them to form a matching.

At rank 40 this implies at least **2,075 distinct overlapping support pairs in the full graph**. The original seven-discriminant space is minus type of dimension four and has 50 isotropic lines \(H\), one per maximal extension. For an overlap pair retained in an extension, its original classes have norms \(4,4\) and product \(0\) or \(\pm1\) modulo seven. Their Gram determinant is a nonzero square, so their independent span is an anisotropic plane (minus one is a nonsquare in \(\mathbb F_7\)). Its perpendicular plane in the original minus space is split and hence contains exactly two isotropic lines. The pair is eligible precisely for those two choices of \(H\), since eligibility means both original classes are perpendicular to \(H\). Double-counting all extension incidences gives the lower bound \(50\cdot83/2=2075\). The full-graph pairs counted this way need not be pairwise disjoint.
