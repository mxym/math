# Size 85 over F_17³: moments through nine

Assume the size85 M8 and no-layer reductions. This note rules out all genuine degree-seven reduced occupancy profiles, hence proves M9. It does not exclude size85.

## Weighted incidence

For a plane-normal profile g(t) use w=(Σ g(t)^2−425)/34. All weights are integers, positive on the nonuniform support V, and zero elsewhere; W=Σw=710. The pencil of each opposite nonuniform normal is tight, with total weight C=30. These are the polarity identities from [FugledeF17Size85MomentEight.md](FugledeF17Size85MomentEight.md). In any such pencil let b be its number of positive profiles; b≥6 (no layers and the ≥13-U-pencil theorem), and all profiles have degree at most b−2 by the Radon homogeneous Vandermonde argument. A degree-seven member means its moment form F9 is nonzero and precisely the degree-seven normals have nonzero evaluations. Consequently there are at most nine tight pencils that have no degree-seven profile in that member: each is a distinct rational factor of F9. All other tight pencils have at least nine positives. If the opposite individual weights are bounded by w_max, weighted incidence gives
```
30 |V| ≥ 9·710 − 3·9·w_max .
```
The factor 3 comes from the weaker b≥6 at exceptional pencils.

With |V|=N, the opposite norm satisfies
```
||w_opposite||² ≥ 710²/307 + (18·710−30·307)² N / [17·307(307−N)] .
```
This follows by Cauchy–Schwarz after centering the support indicator and the opposite weight, using P²=17I+J for the polarity matrix and 1_V^T P w_opposite=30N. The case N=307 would force every line to be tight and 18W=30·307, which is false. The lower bound increases with N.

## Profile bounds and heavy normals

No full plane occurs, so there are no lifts of zero residues to 17. The cap-16 degree-at-most-six catalogue of [verify-fuglede-f17-size85-moment-eight.js](verify-fuglede-f17-size85-moment-eight.js) gives genuine cubic through sextic minima 6,4,3,2 and maxima 13,15,17,19. There are no affine or quadratic profiles. For cap 10 and profile degree at most six the maximum weight is 8; for cap 9 and degree at most seven it is 6. These are the only additional profile catalogues needed. The verifier [verify-fuglede-f17-size85-septic-profiles.js](verify-fuglede-f17-size85-septic-profiles.js) enumerates all centered profiles by interpolating from the first d+1 values, solving one of those values using the zero penultimate coefficient, and checks the other levels and total mass.

Suppose exactly one member has a genuine septic profile. In the nonseptic member mark normals of peak at least 11. There are at most nine: such an affine plane determines at least ten directions by the cap-five, nine-direction planar census, so its projective direction line is a factor of the septic member's nonzero F9. Each heavy normal sees total opposite weight 30. Hence the weighted mass of tight pencils through any heavy normal is at most 9·30. The local squared sum on other tight pencils is at most 200 by the cap-10 weight bound; on all tight pencils it is at most 284 according to the lower weights and b. These integer envelopes are checked in [verify-fuglede-f17-size85-septic-mixing.js](verify-fuglede-f17-size85-septic-mixing.js). Weighted double counting gives
```
||w_nonseptic||² ≤ 200·(710/30−9)+284·9 = 16468/3 .
```
The septic member has N≥196 (opposite maximum weight 19). The lower bound at support 196 is strictly larger than 16468/3, contradiction.

## Two septic members

[FugledeF17Size85DegreeNineGeometry.md](FugledeF17Size85DegreeNineGeometry.md) gives spatial line cap four and plane cap fifteen. Mark normals of peak at least 10; there are at most nine on either side by the cap-four, nine-direction planar census and the opposite nonzero F9. A tight pencil avoiding them has local squared sum at most 156 by cap 9 and individual weight at most 6. For a general pencil every weight is at most 21: its nonconstant reduced polynomial has degree at most seven, so it has at least ten strictly positive levels; concentrating total mass 85 subject to cap 15 and this support lower bound gives squared sum at most 1165, at 15^5,6,1^4. Weight 22 would require 1173. The general local squared sum is at most 452, confirmed by integer partitions of 30 subject to weight cap 21 and minimum weight 4,3,2,1 when the allowed maximum degree is 4,5,6,7 respectively. The latter degree is at most min(7,b−2).

The weighted mass of heavy-incident centers is at most 9·30. Therefore either weight norm satisfies
```
||w||² ≤ 156·(710/30−9)+452·9 = 6356 .
```
The indicator bound at N=203 exceeds 6356, so both supports N,M are at most 202, and the degree-weight incidence inequality above with w_max=21 gives both at least 195.

Let E=1_V^T P 1_{V'} be unweighted incidence. For the opposite tight centers define the deficit δ=Σ(below 9)(9−b), and let τ be its weighted version. At most nine pencils are exceptional, all have degree b≥6, hence δ≤27 and τ≤21δ. The total weighted excess above degree nine equals 30N−9·710+τ, and all weights are at least one. Therefore
```
E ≤ 9M−δ+30N−6390+21δ ≤ 9M+30N−5850 .
```
Use also its symmetric version. By P²=17I+J the centered unweighted estimate is
```
|307E−18NM| ≤ sqrt(17NM(307−N)(307−M)).
```
For every unordered pair N,M in [195,202], even the largest incidence satisfying both preceding upper bounds is too small for this inequality. The finite certificate checks with squared integers and positive numerator differences. Thus two septic members are impossible. The two contradictions prove all reduced occupancy degrees are at most six, equivalently moments vanish through degree nine. The size 85 cardinality exclusion additionally requires the lower-degree endgame.
