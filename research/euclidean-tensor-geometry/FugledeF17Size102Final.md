# Spectral cardinality 102 excluded in F_17^3

**Theorem.** There is no spectral subset of F_17^3 of size102. This does not assert the conjecture at other remaining sizes.

The preliminary proof [FugledeF17Size102MomentNine.md](FugledeF17Size102MomentNine.md) supplies affine line cap6, affine plane cap17, at most one layer per member, and vanishing moments through degree nine. Thus each plane-occupancy residue profile has degree at most six. Any nonconstant affine profile has least residue mass136>102 and is impossible. A nonuniform constant profile is necessarily a layer (six planes of size17 and the rest empty).

## Profile weights and degree-support bounds

For either member B put w_B(v)=(Σ_t binom(n_t(v),2)−255)/17, with support V_B the nonuniform directions. The total W=Σ_v w_B(v)=849. Weighted polarity gives T_B=P w_B−33·1 where T_B is the unordered pair count by difference direction. Since D(B) is uniform for the partner, every opposite positive vertex has a neighbor pencil of total weight C=33, called tight. A layer weighs33 and is alone in every tight pencil meeting it. Its weighted incident mass on the opposite side is33.

The checker [verify-fuglede-f17-size102-profile-and-mixing.js](verify-fuglede-f17-size102-profile-and-mixing.js) enumerates all centered genuine degree d profiles for 2≤d≤6, with allowable lifts of zero to 17 determined from mass102. It obtains respective minima 8,6,4,3,2 and maxima12,16,19,20,23. Positive weights are integers, either by this catalogue or because the degree-at-most-twelve variance square sums to zero modulo17 and has even total variance. Centering loses no profiles: translate the argument to kill the penultimate coefficient. The checker efficiently enumerates constants for each choice of other coefficients by shifting the residue histogram.

In a tight pencil with b nonuniform normals, the planar Radon identity is Σ_i g_i(l_i)=6(b−1)+17f; the positive-degree homogeneous coefficients of residue profiles vanish for each degree≥b−1 by independence of distinct projective powers. If a positive degree j occurs then at least j+2 profiles have genuine degree j, provided j is the largest degree present, since any j+1 projective jth powers are independent. Thus a nonlayer pencil has b≥4 (affine profiles do not exist here). At b4 all profiles are quadratic. Translate to center the first two; the homogeneous linear relation then centers the other two. The exact centered catalog gives (weight,constant) pairs (12,2),(9,4),(11,12),(8,14), so weight sum33 forces (8,8,8,9) with constants 14+14+14+4≡12, not the required 6·3≡1 mod17. Thus b4 is also impossible, and every tight pencil has degree one (a layer) or at least five.

For B having maximum genuine profile degree R≥3, the homogeneous moment form of degree d=16−R is nonzero; its nonzero projective values are precisely the degree-R normals (top profile coefficient detected by multiplication by t^d and summing over the field). An opposite tight pencil seeing none of these normals has the entire projective line in this zero set. The line is a rational factor because d<18. Therefore there are at most d such exceptional opposite vertices. Let τ_B be their total opposite weight. A nonexceptional tight pencil has b≥R+2 by the Radon identity. An exceptional pencil has b≥5 or is a sole-layer pencil with b=1; all pencils seeing B's at-most-one layer have total opposite weight at most33. Weighted degree counting gives
```
33 |V_B| ≥ (R+2)·849 − (R−3)τ_B −4·33.
```
Here the reduction by R−3 accounts for dropping the degree to five in all exceptional pencils, and the final term further drops five to one on the layer-incident mass.

For any N=|V_B|, indicator-versus-weight mixing gives
```
||w_partner||² ≥ W²/307 + (18W−33·307)² N/[17·307(307−N)].
```
It follows by centering 1_{V_B}^T P w_partner=33N and P²=17I+J. This bound is increasing in N, with N=307 separately impossible by the row sum 18. The comparisons below are verified by exact integer cross multiplication.

## Excluding genuine sextics

If exactly one member has sextics, the other has ordinary weights at most20 and at most one layer of weight33. With R=6 there are at most ten exceptional opposite vertices and τ_B≤10·20+13=213. The degree-support bound gives N≥183. For the other member, every nonlayer pencil's squared neighbor sum is at most279: b5 gives at most225 from minimum6, b6 at most249 from minimum4, b7 at most279 from minimum3 and b≥8 smaller. Layer pencils have squared neighbor sum1089. Weighted double count yields norm squared at most 279W/33+(1089−279), less than the indicator lower bound at N183. Therefore this case is impossible.

Suppose both members have sextics. Then τ_B≤10·23+10=240 for both. For any nonlayer tight pencil, at b≥9 the minimum weight two gives squared sum at most321; for b5,6,7 the earlier bounds apply. At b8, the only multisets of weights summing33, minimum2, with squared sum >329 are (2,2,2,2,2,2,2,19) and (2,2,2,2,2,2,3,18). If the pencil has no sextic, minimum3 would give squared sum at most207. Otherwise all eight profiles are genuine sextic, since any seven distinct sixth-power columns are independent. One projection-plane translation centers the first two; the degree-five homogeneous congruence then centers the remaining six by independence of their six fifth-power columns.

The exact checker [verify-fuglede-f17-size102-sextic-pencils.js](verify-fuglede-f17-size102-sextic-pencils.js) enumerates the 56 centered weight-two sextics by interpolating the polynomial from its first seven deviations from six, with partial squared sum at most68, verifying both total deviation zero and squared sum68. It normalizes the direction masks to 17 PGL orbits and the common leading coefficient scalar to its two sixth-power classes. For each candidate bad weight multiset, it chooses the weight-two profiles at their positions. The remaining homogeneous lower coefficients are then forced by the equations in every positive degree and the constant equation, leaving only one free constant when two high profiles remain. Exact checks give zero tuples of the second shape and one normalized tuple of the first. Its heavy profile is 4t^6+13t^4+t², with integer mass102 already and maximum occupancy16. These normalizations preserve the integer peak.

Call a B normal heavy if its profile has peak at least15. Any corresponding affine plane must determine at least eleven directions, since a cap-six planar set with at most ten directions has at most fourteen points by the exact census in [verify-fuglede-f17-size136-degree-ten-caps.js](verify-fuglede-f17-size136-degree-ten-caps.js). Its direction line is therefore a factor of the partner's nonzero degree-ten form; at most ten heavy normals exist per side. All tight pencils with squared sum389 see a heavy profile, hence their total opposite weighted mass is at most 33·10 by summing over heavy sites. Thus the local squared sum can be bounded by 279 on exceptions with no sextic, 329 elsewhere, a +60 surcharge on the heavy bad shape, and a +810 surcharge for one layer relative to the 279 bound. Weighted double count gives
```
||w_B||² ≤ (329W −50τ_B)/33 + 810 + 60·10.
```
Choose the side B with smaller τ_B; the opposite norm upper bound may use this smaller value as well. Use N≥ceiling((8W−3τ_B−132)/33) in the indicator lower bound. The exact checker compares for every integer 0≤τ_B≤240; the smallest positive lower-minus-upper gap is approximately42.757 at τ_B=240,N=180. This contradiction excludes both members having sextics. Consequently all profiles now have degree≤5.

## Excluding genuine quintics and quartics

If some B has quintics, use R=5, τ_B≤11·20+13=233, giving N≥162. Each opposite weight norm squared is at most 279W/33+810 as above, which is smaller than the indicator lower bound at N162. Thus all profiles have degree≤4.

If some B has quartics, use R=4, τ_B≤12·19+14=242, so N≥144. In a nonlayer tight pencil, b5 has squared sum ≤225, and b≥7 with all weights at least four gives an even smaller bound. For b6, if no quartic, the minimum six is incompatible with sum33. Otherwise all six are genuine quartics, centered by the common translation and independence of the remaining four cubic columns. Minimum weight four, sum33, and squared sum >225 give exactly (4,4,4,4,4,13) and (4,4,4,4,5,12). The exact checker [verify-fuglede-f17-size102-quartic-pencils.js](verify-fuglede-f17-size102-quartic-pencils.js) uses the ten PGL mask orbits and the four leading scalar classes, and its lower-profile tuples (8208 and 37728) give zero Radon-compatible arrangements. Consequently any nonlayer pencil has squared sum ≤225. Weighted double count with one layer gives norm squared at most 225W/33+864, below the indicator lower bound at N144. Therefore no quartic occurs.

## Final divisibility

All profiles on either side now have degree≤3. A tight pencil has degree one if it contains a layer, and otherwise degree at least five as proved. Since all ordinary weights are at least six, nonlayer degree at most floor(33/6)=5, giving exactly five. The weighted degree sum on the opposite side is therefore 5W−4·33 L_B, where L_B is the number of B layer normals (possibly zero). It must equal 33|V_B|. But 5·849 is not divisible by33. This final contradiction proves the theorem.
