# The simultaneous short-field tensor on a Hoffman complement

Fix a 22-coclique C. Use the determinant-two rank-33 saturation T **with no dual norm 1/2**, as in the [simultaneous avoidance theorem](hoffman-positive-norm70.md). Let B be the 77 outside points. Let m_b be the projected marks in T, with Gram
$$Q=16I+4A_B-D^tD,$$
so each has squared norm 12. Evaluation f_b=(x,m_b) is injective and scales squared norm by 28. Use the following actual, oriented field families (subsets of all fields at their graph norms):
* F56 from the roots of T; write R=|F56|.
* F70 from the dual norm-5/2 vectors; |F70|=60+2R.
* F112 from the norm-four vectors of T.

Write S_j=Σ_{f∈Fj}ffᵗ, in B coordinates. Then
$$S_{112}+414 S_{56}+56 S_{70}=(11520+60R)Q,\qquad
|F_{112}|=92940+218R.$$
In particular these three families together span the full 33-dimensional real space of +3 fields vanishing on C. This is not just a statement about coefficient counts independently attainable at different saturations.

**Proof of the tensor.** In the E7 gluing U of rank 40, the norm-two and norm-four populations are n₂=126+R and n₄=39600+456n₂. The quadratic harmonic relation is W₄+288W₂=((4n₄+576n₂)/40)I for shell tensors W. The scalar is 3960+60n₂=11520+60R. Project to the residual 33-space: the norm-two contributions are just the T roots; at norm four they are the norm-four vectors of T, each T root repeated by the 126 E7 roots, and the dual norm-5/2 vectors each repeated by the 56 E7 dual norm-3/2 vectors. The possible dual norm-1/2 contribution is absent by construction. Evaluating on every pair m_b,m_c yields the formula. Taking traces, with tr Q=924, gives the asserted count; it also follows from n₄−756−126R−56(60+2R). Positive definiteness of the scalar tensor on the residual space yields the span.

## Largest coordinates identify their sites and use up bona fide roots

For each f∈F70, all coordinates are at most 5 in magnitude by Cauchy, since (5/2)·12=30. If one is +5 at b, then the ten B-neighbors of b have sum 15, and the other 66 B-sites sum −20. Their minimum integer square costs are 25 (five 1 and five 2) and 20 (twenty −1 and all others zero). Together with the pivot's 25 this already reaches 70, so equality gives exactly these patterns. In particular no other site has magnitude five.

Write m=m_b and x for the dual vector giving f. Then 2x is in T, and r=2x−m has norm 10+12−4·5=2. Its actual evaluation z=2f−Q_{*,b} has norm 56 and z_b=−2. The binary signature z mod 2 identifies b, even if we forget the sign of the root: it equals D^tD_b, for the true 4-set D_b. Distinct columns D_b,D_c cannot give the same signature. Their symmetric difference would be a nonzero binary kernel word of weight 4,6 or 8 (they share at most two sites). Weights below eight are impossible; at eight the word contains the entire block D_b, whereas an eight-cut contains no actual block by the [binary design moment](hoffman-binary-grid-deck.md). Thus the rooted signature recovers b; then z_b=−2 chooses the root orientation and f=(z+Q_{*,b})/2 recovers the input oriented to be +5. This injects the antipodal pairs with an extreme coordinate into the R/2 root pairs. Hence **at least 60+R distinct oriented fields in F70 have all coordinates of magnitude at most four**. If R=0 there are exactly 60 such fields, and their 30 lines are equiangular: the nonzero dual class has self-pairing 1/2 modulo one; distinct nonopposite norm-5/2 representatives have pairings ±1/2 or ±3/2, and ±3/2 would give a root by summing or subtracting. The actual absolute field dot product is then 14, i.e. normalized angle cosine 1/5.

There are at most **two** sites of magnitude four in any field just counted. Indeed let f_b=f_c=4, after changing the overall sign if needed. Cauchy on m_b+m_c gives 64≤(5/2)(24+2Q_bc), so Q_bc>0, forcing adjacency. If their unique cap is in C, the nine other B-neighbors at each end are disjoint and have sum eight on each side. The remaining 57 B-sites sum −24, making the square cost at least 32+16+24=72. If their cap is in B with coordinate u, the two disjoint eight-neighbor remainders have sum 8−u each and the remaining sites sum u−24. The square cost is at least
$$32+u^2+2(8-u)+(24-u)=72+u^2-3u\ge70.$$
Equality requires u=1 or 2, all entries on the two arms 0 or +1, and all remaining entries 0 or −1. Hence besides b and c no site has magnitude four. Any three absolute fours would contain two of the same sign, proving the bound. If two fours have opposite signs, Cauchy on m_b−m_c similarly forces Q_bc<0, i.e. nonadjacency and at least one common C point.

These conclusions constrain genuine simultaneous labels at every surviving rank, conditional only on an actual Hoffman coclique; they do not exclude the graph.
