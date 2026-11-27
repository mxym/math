# Size 34 over F_17³: moments through five

Assume the prior size34 no-layer and uniform-pencil/plane results, in particular cap2 on affine lines, cap6 on affine planes and cap7 on projective U-pencil sizes ([FugledeF17Size34PencilCapSeven.md](FugledeF17Size34PencilCapSeven.md)). Let D(B')⊂U_B be the partner difference-direction inclusion. We prove conditional two-blocking for a nonzero degree-five form F vanishing on U_B, then use incidence to rule out F.

## Low pencil and radial factor reduction

A projective line has at least one U point. If some line has just one, every parallel affine slice of B' has at most two sites and is collinear, hence consists of precisely two sites by averaging. Those seventeen supports share one direction e. Their quotient sites q_i in the plane modulo e have cap3, since four full pair supports in a plane would have eight sites. Fix projective coordinates [X:Y:Z] with e=[1:0:0]. Write the pair on site q_i as having axial coordinates α_i±β_i, β_i≠0, with the sign of β_i irrelevant. A chord of q_i,q_j gives at least three transverse projective roots from the axial differences α_i−α_j±β_i±β_j, and e adds another U point on the same radial projective line. Call two pairs of different squared half-lengths β_i²≠β_j² mixed; their difference set has four distinct finite roots.

Let k be the number of distinct rational factors through e. If k≥3, a nonfactor radial line contains at most 1+5−k≤3 U points, so all quotient directions would force factors. But a 17-point cap3 quotient determines more than five directions: its 136 pairs give at most 16 pairs in a direction. This is impossible.

## Two radial factors

Let the two factor slopes be exceptional and divide them from F, leaving H of degree three. The graph on the 17 quotient sites using ordinary (nonexceptional) chords is connected, since each vertex loses at most four edges by cap3. Every ordinary chord gives three finite roots of H so H(e)≠0 and we can make it monic in X. The root bound implies every ordinary pair has the same squared half-length, hence by connectivity one global value β². The mean coefficient is binary linear, so a global shear centers H. Its X coefficient Q is binary quadratic and takes the same nonzero value −4β² on every ordinary quotient difference.

Use the exact two-exception quadratic test in [verify-fuglede-f17-size51-f7-radial.js](verify-fuglede-f17-size51-f7-radial.js). After scaling the fixed value to one and linearly normalizing the quadratic, the rank-two cases have no compatible six-site cap3 example. In rank one any such six-site example lies on only two lines parallel to the radical, and the radical is necessarily an exceptional slope. The zero form cannot take value one. Thus every six-subset of our quotient has the rank-one property, which puts all sites on only two lines parallel to the radical (otherwise a six-subset meets three). Cap3 excludes 17 sites. This rules out k=2.

## One radial factor

The sole factor slope is exceptional. Let H be the residual homogeneous quartic. If H(e)=0 then its finite axial degree is≤3; all ordinary chords have exactly three roots, so the pairs have one common squared half-length by connectivity of the ordinary graph. Any two parallel ordinary chords then yield the same centered AP3 root set in the same coordinate, and their step magnitudes, detected by the second centered power sum, are equal up to sign. This forces their quotient vectors to agree up to sign. If the exception slope occurs, normalize an actual pair in it to the marked vertical side of a triangle (0,0),(1,0),(0,1); otherwise the ordinary equal-chord constraint is even stronger and one may choose a triangle with any side made vertical. The exact one-exception cap3 search in [verify-fuglede-f17-size34-moment-five.js](verify-fuglede-f17-size34-moment-five.js) excludes a 17-set after 3722 states. Thus H(e)≠0.

Scale H monic in X and shear its linear total root mean to zero. If all pair lengths are equal, then on an ordinary chord the four centered roots consist of r,r±2β,−3r, where r is the post-shear axial centroid difference, and β² is the common squared half-length. The second power sum is 12r²+8β². Thus its binary quadratic P2 gives a ternary quadratic P2−12r² with constant value 8β²≠0 on each augmented (quotient position, axial centroid) cross difference between distinct exceptional groups. Cap3 yields at least six such groups. Choose one representative per group. After translating one to the origin, the nonzero constant equidistance condition gives the Gram matrix proportional to I+J of rank five on any six representatives. Dimension three precludes this.

If at least two pair lengths occur, use the graph of mixed ordinary chords. It has a connected component of at least fifteen sites. To see this, if the largest length class has size≤6 then every vertex has at least 16−5−2=9 mixed ordinary neighbors, and the graph is connected. If one class has at least seven sites, any two vertices outside it share a neighbor in it (each excludes at most two of its sites from ordinary chords), so all outside vertices are in one component. All vertices of the large class join this component except possibly sites in a single exceptional group containing all the outside sites; there are at most two such vertices by cap3. This proves the claim.

A mixed ordinary chord has exactly four roots symmetric about the axial centroid difference, which is therefore zero after the common mean shear. Hence all centroids within the component coincide. Its ordinary mixed roots are ±β_i±β_j; on ordinary equal-length chords the three roots are 0,±2β_i, and the fourth (possibly repeated) is forced to be zero by the centered mean. The X² coefficient Q of H therefore obeys Q(q_i−q_j)=−2(s_i+s_j) on all ordinary chords in that component, where s_i=β_i²≠0. Choose one site from each of at least five exceptional groups met by these fifteen sites. Translate one to zero (its s-value denoted s_0). The polar Gram matrix on the m−1 difference vectors is −2(diag(s_i)+s_0 J); its rank is at least m−2≥3, since the diagonal part has all entries nonzero and J has rank one. This contradicts the binary form. Thus k=1 is impossible in all cases.

## No radial factors

Here every radial line has at most five U points. No three quotient sites can be collinear: their six points in B' would be coplanar with tangent directions on one such radial line, whereas every six-site cap determines more than five directions. This finite fact is verified by [verify-fuglede-f17-size34-moment-five.js](verify-fuglede-f17-size34-moment-five.js). Thus the quotient is itself a cap2.

If all pair lengths agree, each chord contributes a transverse AP3. On any fixed radial slope the corresponding polynomial has ≤4 finite roots, so two AP3s there share at least two distinct roots. Their normalized steps are therefore in ratio ±1,±2,±1/2 (a difference between shared sites is a one- or two-step difference in both progressions). Since the physical axial steps are the same up to sign, the allowed ratios for their quotient chord vectors are likewise ±1,±2,±1/2. The exact normalized triangle search in [verify-fuglede-f17-size34-moment-five.js](verify-fuglede-f17-size34-moment-five.js) enumerates this condition with affine cap3, and finds no 17-point set (11258 states). This settles the all-equal case.

Suppose some pair lengths differ. A site in the smallest length class has at least nine mixed neighbors (the smallest class has ≤8), all in distinct quotient slopes by cap2. Expand F=A(Y,Z)X⁴+B(Y,Z)X³+C(Y,Z)X²+D(Y,Z)X+E(Y,Z), with coefficient degrees 1..5 (F(e)=0). On every mixed slope, A is nonzero and the four roots are symmetric about their mean. The first odd centered coefficient is zero; shifting X by −B/(4A) and clearing denominators gives
```
16 A²D−8ABC+2B³=0.
```
This homogeneous degree-six polynomial vanishes in at least nine slopes, hence identically. Reducing modulo the nonzero linear A gives A|B. Thus one global shear centers the mean, and the centered X³ and X coefficients are zero throughout. Every mixed chord now has centroid difference zero; the mixed graph is complete multipartite with at least two classes, so all axial centroids coincide. On equal-length chords the three roots are 0,±2β, and the fourth, when present, is forced to be zero. On all actual quotient differences A is nonzero: otherwise the centered axial degree is at most two and it cannot contain three distinct finite roots. We have in actual, unnormalized chord coordinates
```
C(q_i−q_j) = −2 A(q_i−q_j)(s_i+s_j).
```

Choose quotient coordinates y=A and z independent, so the quotient is a full graph over all 17 y values. Its coordinate functions 1,y,z are independent by noncollinearity. Write C=aY³+bY²Z+cYZ²+dZ³. Regard functions on the 17 sites as vectors; let (f∧g)_{ij}=f_i g_j−g_i f_j. Expanding the displayed chord equation gives the alternating tensor identity
```
(C(q)+2ys)∧1 + y∧(3a y²+2b yz+c z²+2s) + z∧(b y²+2c yz+3d z²)=0.
```
Project its second factor modulo span{1,y,z}: independence of these three first factors makes b y²+2c yz+3d z² belong to span{1,y,z}. If d≠0, this is a quadratic equation in z valid along the full graph, with nonzero constant coefficient of z² and discriminant a polynomial of degree≤2 in y. That discriminant is a square value at every y. A polynomial of degree≤2 with this property is a polynomial square: a nonconstant linear polynomial takes nonsquare values, and for quadratic a(y−h)²+b with b≠0, the character sum of its values is −χ(a), not the ≥15 that all square values would give; the sum follows by counting (u−v)(u+v)=constant. If b=0 the leading coefficient must be a square too. Hence the quadratic graph lies in the union of two affine lines, contradiction to the cap and its size17. Thus d=0.

Now A divides C, so Q=C/A is binary quadratic with Q(q_i−q_j)=−2(s_i+s_j) for every pair. As in the one-factor case, the Gram matrix on the sixteen difference vectors from one site has rank at least fifteen, contradicting the existence of a binary polar form. This completes k=0.

## M5

Every projective line meets U_B in at least two sites if F exists. Since U-pencil cap is seven, only at most five rational factor lines can contribute positively to the quadratic sum
```
Σ_L (n_L−2)(n_L−5)=|U_B|²−109|U_B|+3070.
```
Their total contribution is at most 5·(7−2)(7−5)=50, while the quadratic has minimum100 over integers. Contradiction. No such nonzero F exists; lower degrees lift by multiplication, so uniformity forces every mixed moment through degree five to vanish. In particular the reduced occupancy profile degree is at most ten in every normal.

This does not exclude size34.
