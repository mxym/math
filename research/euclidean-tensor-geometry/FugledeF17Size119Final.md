# Size 119 excluded in F_17^3

**Theorem.** No subset of F_17^3 with 119 points is spectral. This assertion is specific to cardinality119; smaller remaining candidates are not addressed here.

The proof uses [FugledeF17Size119MomentNine.md](FugledeF17Size119MomentNine.md) for at most one layer and the degree-nine moment vanishing, and [FugledeF17Size119MomentEleven.md](FugledeF17Size119MomentEleven.md) for eliminating higher occupancy degrees five and six. Thus all reduced occupancy profiles have degree at most four. The standalone [verify-fuglede-f17-size119-weighted.js](verify-fuglede-f17-size119-weighted.js) is the arithmetic checker for both the high-degree step and this endgame.

For each member B, let w_B be its normal weight vector (plane pair counts minus357, then divided by17). Its positive support V_B is the nonuniform set and sum of weights W=987. Every opposite nonuniform vertex neighbors weights of total C=35 in the projective polarity-incidence graph. Such a neighbor pencil is tight. A layer has weight35 and is alone in every tight pencil meeting it. A nonconstant affine profile is impossible because its least residue mass136 exceeds119. A constant nonuniform residue profile must be a layer.

The exact centered univariate catalogue gives minimum positive weights 8,6,4 for genuine reduced degrees two, three and four, and maxima 15,19,21, respectively. A tight pencil without layers has b≥4 nonuniform profiles by the Radon Vandermonde relation (positive degree j requires at least j+2 participating directions). For b4 it has only quadratics; minimum eight and sum35 give squared sum at most313. For b5 its profile degrees are at most3, minimum six gives squared sum at most265. For b6 maximum degree4 and minimum four give squared sum at most305. For b≥7 the minimum four gives an even smaller bound. Thus every nonlayer tight pencil has squared-weight sum at most313. At most one layer per member yields
```
||w_B||² ≤ 313·987/35+(35²−313)=9738.6.
```
This is weighted double counting: 35||w_B||² is obtained by summing local neighbor square sums against their opposite weights. The opposite weight incident to one layer is exactly35.

For any support size N=|V_B|, the indicator-versus-weight polarity bound is
```
||w_partner||² ≥ 987²/307 + (18·987−35·307)² N/[17·307(307−N)].
```
It follows by centering 1_{V_B}^T P w_partner=35N and using P²=17I+J. The expression increases with N and at N=307 tightness itself contradicts the row-sum identity. In particular at N131 it exceeds 10203, and at N151 it exceeds 12315, both larger than9738.6; the checker uses exact integer comparisons.

## Ruling out genuine quartics

Suppose B has a genuine quartic profile. Its homogeneous twelfth-moment form F is nonzero, with nonzero projective evaluations precisely at quartic normal directions: pair the leading coefficient of the occupancy residue with t^12 and sum over F_17. If a tight opposite pencil sees no genuine quartic, F vanishes at every site of that projective line, both uniform and nonuniform. Thus that line is a rational factor (degree12<18), and there are at most twelve such exceptional opposite vertices. Their total weight is at most 12·21+(35−21)=266: each nonlayer profile has weight at most21, and the opposite member contains at most one layer. On every other tight pencil a nonzero quartic appears, and by the homogeneous quartic congruence and Vandermonde independence of any five distinct fourth-power columns there are at least six nonuniform profiles. Among exceptional pencils, every nonlayer pencil has at least four. The pencils containing a layer of B have degree one and total opposite weight at most35. Weighted degree counting now gives
```
35|V_B| = Σ_{d∈V_partner} degree(d) w_partner(d)
        ≥ 6·987 − 2·266 − 3·35 =5285.
```
(The term 2·266 budgets a reduction from six to four on every exceptional vertex, and the extra 3·35 lowers four to one where B has a layer.) Hence N≥151, contradicting the indicator comparison. This excludes quartics in either member, without a rare-profile census.

## Ruling out genuine cubics

If B now has a genuine cubic, use its nonzero thirteenth-moment form. An opposite tight pencil with no cubic again lies wholly on the zero set, so there are at most thirteen exceptional opposite vertices. Their total weight is at most 13·19+16=263 because no ordinary profile exceeds19, and there is at most one opposite layer. Every nonexceptional pencil sees at least five cubic normals by the cubic homogeneous relation. Exceptional pencils have degree at least four unless they contain a B layer; those degree-one vertices again have total opposite weight at most35. Thus
```
35|V_B| ≥ 5·987 − 263 − 3·35 =4567.
```
Hence N≥131, contradicting the same indicator bound. Genuine cubics are excluded.

## The quadratic divisibility endgame

Both members now have residue degree≤2. Each nonlayer tight pencil consists of exactly four quadratic profiles: fewer are impossible by Vandermonde, and more have weight at least40. A common translation centers the first two profiles; the linear homogeneous relation then centers the remaining two, as their forms are independent. Thus their centered constants must sum to 7(4−1)≡4 mod17 and their weights to35. The exact catalogue yields only the multiset of (weight,constant) pairs [(8,15),(9,5),(9,9),(9,9)]. This also follows by complementing the centered profiles for size170, preserving weights and negating constants.

Mark as special the layer normals and the weight-eight normals of B. Every tight pencil opposite B sees exactly one special neighbor, either its unique layer or the unique weight-eight quadratic. Sum the weighted incidences over special B normals. The opposite total is987, while each special receives total35. Therefore 35 divides987, contradiction (remainder7). This completes the size119 exclusion.
