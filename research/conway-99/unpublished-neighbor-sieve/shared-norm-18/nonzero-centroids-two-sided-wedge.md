# Nonzero centroids strengthen all four masses; the smallest tuple requires a larger configuration

Assume the rank-42 N18/N24 two-type face. Use the [Johnson double graph](norm22-johnson-double-graph.md) on L=N22/2 lines, with D doubles and S=2,5,8,11. A signed norm-18 residue class beta contains precisely n=50,51,52,53 oriented vectors. Let e count its unordered dot-4 pairs. Its actual integral graph-field centroid A satisfies
```
||A||²=14e−3n(n−7),            [A]=n beta.
```
Since 7 does not divide any n, A is not zero. Its seven-residue norm is 18 n² modulo 7, which is respectively 4,2,1,1. The squared norm is an even integer, is at least 18, and must be respectively at least 18,30,22,22 (in the second case norm16 is excluded). Thus the four signed classes chosen one per antipodal pair each require at least e=ceil((3n(n−7)+minnorm)/14), a gain of 1,2,1,1 at each class over the previous zero lower bound. Summing and accounting for at most two decompositions per norm-28 line exactly as in the [Johnson positive-mass note](norm22-johnson-positive-mass.md) now gives D≥113,143,169,199 against the four original scalar upper bounds on N28 (3470,3578,3686,3794), and the shared bound D+L≥291,330,365,404 from N28=−1386+90n+2L. Combining D≤3L+9S gives L≥ceil((K−9S)/4). The [perpendicular class parity theorem](rank42-even-weil-q11.md) for the original q11 shell gives 4|N22, i.e. L is even. Rounding to the next even integer gives respectively
```
L                 ≥70  72  74  78
N22               ≥140 144 148 156
G333              ≥84  80  76  76
```
by G333=2L−8(19+S)/3. The last step uses that actual parity theorem, not integrality of each W-orbit average.

For S=2 in particular, either (i) some q has a triple of source indices with all three pairwise double differences unit (literal union of six fields has 43 sites); or (ii) a double c23 with exactly ONE doubled site has a unit wedge at both endpoints q and s. The latter yields a 49-site configuration. To prove the alternative, if (i) fails each local graph U on m=mu(q) source indices with unit double edges is triangle-free. Let h_q be the number of nonunit pairs and z_q the number of unordered distance-two pairs in U. As in the [42/43-site unit-wedge proof](forced-unit-wedge.md), z_q≥|E(U)|−floor(m/2), so C(m,2)≤1+5(h_q+z_q)/4. Let N1,N2 count double lines with precisely one or two doubled sites. Their actual slot mass obeys N1+2N2≤6S. If (ii) also fails, each one-slot line enters at most one z_q and each two-slot line at most two. Thus Σz_q≤N1+2N2≤6S and Σh_q=2(N1+N2)≤12S. Summing gives D≤L/2+45S/4. With S=2 and L≤178 this says D≤111.5, contrary to D≥113 above.

Here is the exact support dictionary in (ii). Fix q=a2+b2=a3+b3, s=a2+a3−q. Write its extra decompositions q=a+b and s=a′−b′, with a,a′ in the same signed class as a2,a3, and b,b′ in the same signed class as b2,b3. The additional fields in each wedge are distinct from the anchor pair; within any one source set their dot with each appropriate anchor is 4. The chosen wedges are unit, so a,a′ agree in sign at every overlap with a2 or a3, and b,b′ likewise with b2 or b3. Now q·a′=s·a=4+4−11=−3. Thus a≠a′, and
```
b·b′=(q−a)·(a′−s)=−6−a·a′.
```
The two permitted distinct same-class products are 4,−3; the right side cannot be −10, hence a·a′=b·b′=−3 (b=b′ is excluded by the same formula). Their sums have norm30, hence are signed-unit: a doubled site would translate to raw (1,25), forbidden, or a larger entry below its minimum. Consequently both pairs have exactly three opposing overlap sites and no same-sign overlap.

The base a2,a3,b2,b3 occupies the 22 Q sites plus two off-Q seven-site panels meeting at the single doubled site: 35 sites. At q, the extra seven-site panel H_a avoids the two anchor panels by unitarity of the wedges, so it lies outside the entire base. The same is true at s, since the base is the same union of four fields. Off this base b=−a and b′=a′; if a,a′ both were nonzero there, one of the two pairs would have a forbidden same-sign overlap. So the two extra panels of seven are disjoint and 35+7+7=49.

More precisely let X,Y be the base sites where respectively a2=a3=q or b2=b3=q are nonzero, each of size 4+d, d=d(c23). (The following conclusion also holds at d=0,2 if both wedges exist.) All three a/a′ intersections lie in Y: no site supporting an anchored a2 or a3 can contain opposite signs of a,a′, while outside the base the two extra panels are disjoint. At base sites where a2=a3=0 the only option is Y. Symmetrically the three b/b′ intersections lie in X. On X, q=s, each extra pair of constituents chooses exactly one constituent to carry that sign; the a and a′ selections are disjoint and leave exactly three sites unselected by either. Hence r_q+r_s=|X|−3=1+d, where r records the triple bit-111 occupancy. On Y, q=−s, so the a and a′ selections cover Y with precisely three in common. Neither alternative rules out S=2 or implies existence of the graph.

[If no fully unit source triple occurs](unit-triple-or-charge-three.md), all four tuples have much larger actual charge-three norm-33 populations and a small budget of exposed norm-24 edges.
