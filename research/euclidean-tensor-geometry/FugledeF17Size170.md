# Size 170 excluded in F_17^3

**Theorem.** There is no spectral subset of F_17^3 of cardinality170. This makes no claim about smaller cardinalities.

Assume a pair of size17m for m=10. As in [FugledeF17Sizes187204.md](FugledeF17Sizes187204.md), the plane cap is17, and if every projective line of the uniform-normal set of each member contains at least r sites, then the spatial line cap is floor((306−170−7r)/17). The general initial r≥1 gives cap7. The normalized exact 17×17 planar checker finds no ten-site subset of cap7 determining at most eight directions (3003 masks, 1235865 visited states, maximum9). By a partner slice averaging ten sites, r≥9, now giving line cap4. The same exact check then excludes ten-site subsets of cap4 with at most nine directions (5005 masks,6554445 nodes, maximum9), so r≥10. The marked-triangle normalization and mask enumeration are as described in [FugledeF17Sizes187204.md](FugledeF17Sizes187204.md), and the two cases are replayed in [verify-fuglede-f17-size170.js](verify-fuglede-f17-size170.js).

The same projective degree-thirteen incidence argument as for sizes 187 and 204 now applies verbatim: for a nonzero degree-thirteen form vanishing on the uniform normals, the incidence quadratic lower bound508 exceeds the positive contribution upper bound364 of its thirteen potential factors. Thus all mixed moments through degree13 vanish. The reduced plane profiles have degree≤2. No nonconstant affine profile can have mass170 (its mass is136 or153), and a nonuniform constant residue profile is a layer with ten entries17 and seven entries zero.

In the projective polarity pair-count identity use w_B(v)=(Σ_t binom(n_t(v),2)−17 binom(10,2))/17. Its support is the nonuniform set V_B, and:
```
T_B=P w_B−35·1,        Σ_v w_B(v)=1395.
```
For any d∈V of the partner, spectrality forces T_B(d)=0, so the pencil has total weight35. Call it tight. A layer has weight35. The exact centered quadratic census tests all a t²+c, a≠0, and allowed zero lifts, with prescribed integer mass170; minimum positive weight is eight. Thus every tight pencil has at most four nonuniform profiles.

The only tight pencil containing a layer consists of the layer alone. Any other tight pencil has genuine quadratics only. By the leading Vandermonde equation at least four are necessary; hence exactly four. The integer planar Radon identity in a b-profile tight pencil is Σ_i g_i(l_i)=10(b−1)+17 f. One common planar translation centers the first two quadratics, and the linear congruence then forces the remaining two centers zero by independence of their two linear forms. Thus the four centered constants must sum to 30≡13 mod17. The same exact census checks every multiset of four (weight, centered constant) catalog entries. Among those with weight sum35 and constant sum13 modulo17, only [(8,2),(9,8),(9,8),(9,12)] survives. This is a necessary pattern; realizing it is not assumed.

Mark as special the layer normals and the weight-eight normals of B. Every vertex on the opposite nonuniform support has exactly one special neighbor, either the sole layer or the unique weight-eight quadratic. Double-count their weighted incidences: the total opposite weight is 1395, while each special normal receives total opposite weight35 by tightness with the roles reversed. Hence 1395=35·(number of special normals), impossible modulo35.
