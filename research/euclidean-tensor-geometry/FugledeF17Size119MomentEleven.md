# Size 119 in F_17^3: ruling out degree-five and degree-six profiles

Assume the spectral pair and results in [FugledeF17Size119MomentNine.md](FugledeF17Size119MomentNine.md): affine caps line7 and plane17, at most one layer per member, all moments through nine vanish, and U_B is six-blocking whenever a nonzero form of degree≤10 vanishes on it. This note gives all moments through eleven. A separate lower-degree endgame is still needed for cardinality119.

## Planar caps and conditional six-blocking at degrees eleven and twelve

The exact verifier [verify-fuglede-f17-size119-high-degree-caps.js](verify-fuglede-f17-size119-high-degree-caps.js) uses the same marked-triangle affine normalization and six mask symmetries as at136. It gives the following planar bounds: with line cap7, at most eight or nine directions allows at most nine or ten sites, respectively; with at most ten directions, line cap7 allows at most fourteen sites, cap5 allows at most thirteen, and cap4 allows at most twelve. The target11 for (nine directions, cap7), target15 for (ten dirs, cap7), and target14 for (ten dirs, cap5) scans reach no completion with respectively 368754, 878988, 1105838 states.

In particular the six-blocking implication for moment forms extends to degrees eleven and twelve. A low line of at most five U_B sites generates seventeen collinear seven-sites slices in its partner, and at least four parallel seven-supports. Their distinct quotient directions force k≥4 factors through the common axis e, since their radial lines contain at least fourteen D(B') directions by Cauchy–Davenport. For degree11, if k=4 the radial nonfactors have at most eight U_B sites and corresponding planes have cap9, giving total pencil occupancy at most 4·17+14·9=194<238. If k≥5 they have at most seven directions, so any plane through an actual seven-support contains exactly that support; the total is ≤126+10k≤236<238. For degree12, k=4 or5 likewise gives nonfactor caps ten or nine, giving upper208 or202. If 6≤k≤11, the same exact-seven argument applies. Finally k=12 would put all D(B') on twelve radial lines. The projection along e has at least seventeen points because each fiber has at most seven. If it has more than seventeen points it determines all eighteen quotient directions. If exactly seventeen, every fiber has seven points, so that three collinear quotient sites would violate plane cap17. It is a cap and its 136 pairs determine at least seventeen directions. Both contradict at most twelve. Hence all degrees≤12 have the needed six-blocking implication.

If a homogeneous nonzero degree-d form vanishes on a six-blocking set, for 10≤d≤12 it has at most 17(d−1)+2 projective zeros. As in [FugledeF17Size136ConditionalM11.md](FugledeF17Size136ConditionalM11.md), remove rational line factors. A remaining no-line curve of degree j≥2 contributes ≤17(j−1)+1 by [Sziklai/Homma–Kim](https://arxiv.org/html/1410.3174#S1); union of k line factors contributes at most17k+1. If only rational lines, their maximum concurrence t≤d−5, and the two same line-union inequalities bound total by ≤17(d−1)+2. (For d=10 the maximum line-union bound in this finite range is153.) The elementary zero bound 17d+1 also always applies.

## Polarity and profile bounds

The normal weights are w_B=(Σ_t binom(n_t,2)−357)/17. The total W=987, and every nonuniform vertex opposite B has a neighbor pencil of total C=35, called tight. A layer weighs35, and there is at most one. Nonconstant affine profiles cannot have mass119 since least affine residue mass is136. Univariate exact profiles give lower weights 8,6,4 for genuine degrees 2,3,4, and lower weights3 through degree5 and 2 through degree6 for any nonuniform profile in these ranges. The latter two are certified by the low-variance interpolation as at136: for weight1 or2, enumerate the first d+1 integer deviations from seven with squared sum≤34w, fill in by degree-d interpolation, and test the prescribed total and variance. The only possible representatives of these small deviations are within [−7,8], so no zero can be lifted to17 in these scans. Positive weights are integers by the degree≤6 variance identity.

For any nonlayer tight pencil, if b is its number of nonuniform profiles then b≥4 and the Radon Vandermonde restriction is degree≤b−2. At b4,5,6,7 the local squared-weight bounds from the above minima are respectively313,265,305,343. At b≥8 the minimum two gives maximum469 at b8; if all profiles have degree≤5, the minimum three instead gives ≤259 at b≥8. Consequently if all profiles of a member have degree≤5 then its weight norm squared is at most
```
343·987/35 + (35²−343)=10554.6.
```
This uses weighted double-counting of neighbor square sums and the at-most-one layer, which is alone in any tight pencil that meets it.

For a member with support of size N, indicator-versus-weight polarity yields
```
||w_partner||² ≥ W²/307 + (18W−35·307)² N/[17·307(307−N)].
```
This is the centered Cauchy–Schwarz bound from P²=17I+J and the equality 1_{V_B}^T P w_partner=35N. The lower bound increases in N, and N=307 separately contradicts the row-sum identity.

## Excluding sextics

A genuine sextic profile makes the degree-ten moment form nonzero, and its nonzero projective evaluations are exactly the genuine sextic normals (pair the profile's top coefficient with t^10). The crude projective bound then gives N≥136. If only one member has genuine sextics, the preceding opposite norm upper10554.6 contradicts the indicator bound at N136 (approximately 10685.15).

Suppose instead both members have genuine sextics. Their two degree-ten moment forms are nonzero, hence both uniform-normal sets are six-blocking. For a secant of direction e in one member, put k for the number of rational factor lines of the partner's degree-ten moment form through e. As above k≤5. For k=0 or1 the radial nonfactor has at most ten difference directions; for k≥2 at most nine. In a pencil through an actual six-site line, the at least six uniform occupancies are seven. With initial line cap7, the other planes are bounded by14 for k=0/1 and by10 for k≥2, except that k factor planes may have17. This bounds the pencil by210/213 for k=0/1 or at most 162+7k≤197 for k≥2, all below the required119+6·17=221. Thus both members have line cap5. For a five-site line, the tighter ten-direction planar cap thirteen gives bounds198/202 for k=0/1, and the previous bound≤197 for k≥2. All are below119+5·17=204, so both members have line cap4.

Call a normal of B heavy if its occupancy profile has peak≥13. A corresponding affine plane of B now determines ≥11 directions by the cap-four planar census. Its direction line is then a factor of the degree-ten moment form of the partner. There are at most ten such normals for each member. Every nonheavy profile has n_t≤12; the variance bound n_t²≤12 n_t and mass119 imply its integer weight is ≤17. In a nonlayer tight pencil containing no heavy normal, the previous local squared bounds stay unchanged for b≤7, and for b≥8 the weights now lie in [2,17]. Its maximal squared sum is at b8, with (17,6,2,2,2,2,2,2), giving349. Any nonlayer pencil that meets a heavy profile has general bound469, a surcharge120. The total opposite weight of such pencils is at most 35·10 by summing incidences over the heavy normals, each of which sees total35. One layer carries a further surcharge 35²−349=876. Thus
```
||w_B||² ≤349·987/35 +120·10+876=11917.8.
```
The degree-ten six-blocking zero bound gives N≥152 in both members. The indicator lower bound at N152 is approximately12435.57, contradiction. All genuine sextics are excluded.

## Excluding quintics

Now all profiles have degrees≤5, so the norm bound10554.6 applies to both members. A genuine quintic implies a nonzero degree-eleven moment form, with support of its nonzero values exactly the genuine quintic normals. The six-blocking and Sziklai bound above give N≥135. The indicator lower bound at N135 is approximately10586.56, strictly greater than10554.6, contradiction. Hence no genuine quintic occurs. The remaining residue profiles have degrees≤4, which is equivalent to the vanishing of all moments through eleven. No full cardinality119 exclusion is asserted by this note.
