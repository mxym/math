# A quantitative charge-two bound when unit charge-one cost 27 is present

With no sparsity or Seidel-rank assumption,
```
2 G226 ≤ 8316 + 3 U127.
```
The counts on both sides are literal positive-charge graph fields. It remains true in a fixed maximal extension when both field populations are restricted to eligible ones. This follows from a disjoint charge-one edge budget, not from equidistribution across seven-classes.

Keep the [positive-pair classification and two translations](u226-positive-pair.md). Let n_c count U226 labels of subtype c. The [unconditional uniqueness](norm16-height-two-edge.md) gives n_0≤4158, the number of unordered positive pairs. For c=1 the cited reversible switch identifies each b with a unit (1,27) field u equipped with an unordered induced P3 of positive vertices. For c=2 every b has at least one zero-zero mate under each of its two positive hubs: it has c+m−1≥1 at each. A chosen mate y,y′ under hub p makes T={p,y,y′} a triangle; u=D_T−b is unit of type (1,27), has a positive edge y,y′ and its unique triangle cap p is zero. All these marked pairs of output field and edge are distinct across input fields and choices: the edge determines its cap and hence T, and b=D_T−u then recovers the input; the cap also recovers which positive hub was chosen. In particular the two choices from different hubs cannot coincide. Consequently n_1 is bounded by the total marked positive paths and 2n_2 by the total available marked positive edges of u.

For completeness, here is the joint budget on one actual (1,27) unit u. Write P,N for its positive and negative sets, of sizes 8 and 19. Each positive sees 6+d_P negatives, and each negative sees 2+d_N positives. If the positives span e edges the negatives span 5+e by counting cross edges. Write Q_I=Σ_{x∈I}binom(d_I(x),2). The common-neighbor slots for positive pairs number 56−e; the positive sites use Q_P and the negative sites use
```
Σ_{x∈N} binom(2+d_N(x),2) = 19+2(10+2e)+Q_N.
```
Thus 5e+Q_P+Q_N≤17, in particular e≤3.

A triangle of positive sites would give a charge-two field D_T−u of cost 39+27−54=12, impossible. For every positive induced P3 T, D_T−u is charge two of cost 53+27−54=26, hence signed-unit by the elementary site translation in the linked note. Any *other* positive adjacent to a vertex of T would have value at most −2 there, impossible. In particular every positive P3 is a whole isolated component of the positive graph. Each of the positive edge outputs used by c=2 is also an isolated-edge component: for its triangle T of two positives and a zero cap, D_T−u is the signed-unit input b. An additional positive meeting either endpoint would be outside T and have value at most −2 in b. Thus every positive graph is a disjoint union of isolated sites, isolated edges, and isolated three-vertex paths. With q paths and l isolated edges we have 2q+l=e≤3.

Counting the disjoint marked outputs yields 2n_1+2n_2≤Σ_u(2q(u)+l(u))≤3U127. Adding 2n_0 proves the claim. This does not say the positive-charge fields occur in any graph.

As a scalar consequence on any rank-36 graph for which N16 and N20 vanish (unit U127 is now **allowed**), the [global norm-18 row and prism cap](u226-global-pressure.md) give
```
2 U026 + 2 U125 + 29 U127 ≥ 130,480 .
```
Indeed substitute 9G226≤9·4158+(27/2)U127 before subtracting 6·16166+17·29372. The explicit U127 coefficient on the left of the native identity supplies the additional one. There is no support cardinality assumption.
