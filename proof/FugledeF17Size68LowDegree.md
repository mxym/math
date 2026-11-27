# Size 68: maximum degree ≤5 impossible for either member; at least one degree ≥7

Assume the [moment-seven](FugledeF17Size68MomentSeven.md) and [pencil-cap](FugledeF17Size68PencilCapEleven.md) results: no full planes or layers, line cap four, projective uniform pencils have cap eleven, profiles have degrees at most eight by M7, and no ordinary profiles of degree≤3. Write V for nonuniform support, w=(Σ g(t)^2−272)/34, W=570 and C=26. Opposite nonuniform normals index tight pencils of weight sum26; every tight pencil has b≥7 positive profile weights.

## A degree-at-most-five member cannot occur

The exact centered profile census at mass68 and no zero lifts ([verify-fuglede-f17-size68-low-degree.js](verify-fuglede-f17-size68-low-degree.js)) gives weight ranges 4..11, 3..12, 2..16 for genuine reduced degrees four, five and six. If a member's highest degree is ≤5, every positive weight is at least three, so b≤8. At b=7, all the profiles must be genuinely quintic: otherwise the fifth homogeneous coefficient relation and independence of any six fifth powers would eliminate all quintics, and seven quartics weighing at least four would exceed26. The seven prospective weight patterns consist of seven entries at least three summing26.

The verifier [verify-fuglede-f17-size68-quintic-tight.js](verify-fuglede-f17-size68-quintic-tight.js) classifies these b=7 pencils by their ten PGL direction-mask orbits. The one-dimensional leading nullspace has all coefficients nonzero and can be normalized to one free coordinate by common dilation (fifth powers permute F17*). One planar translation kills the fourth coefficients in two profiles, and the remaining five coefficients vanish by the homogeneous degree-four Vandermonde relation. Thus all quintics are centered. At each remaining degree j sort the constrained positions by their admissible coefficient counts, leave the designated highest-weight profile unconstrained, and choose j+1 pivot columns with that column first. Enumerate all allowed free choices, solve the pivots, and filter the candidate polynomials independently in each constrained position. Evaluate the designated profile at the end and keep only the requested integer weight. This checks every candidate obeying the homogeneous finite-field Radon congruence; at degree zero the target is 4(b−1). The seven patterns give 70,420,420,1050,1050,1400,210 placement tests and zero congruence hits.

Hence every tight pencil of this member has exactly eight profiles. Counting its support incidences with opposite weights gives 26|V|=8·570=4560, impossible modulo26. This rules out a highest degree≤5 in either member, independently of the partner.

## Both highest degrees six is also impossible

If both highest degrees are six, every tight pencil has local square sum at most172. Indeed at b=7 the degree bound b−2=5 gives minimum weight three and square sum at most 8²+6·3²=118. At b≥8 all weights are at least two, so the worst case is b=8 with weights 12,2^7 and square sum172. Weighted double counting gives ||w||²≤172·570/26 for either member.

The degree-ten moment form vanishes at uniform and nonsextic normals, and is nonzero at precisely the genuine sextics. At most ten tight pencils can lack sextics, as their entire projective lines then divide the form. Every other pencil has b≥8, while the exceptional ones have b≥7. Individual weight≤16 yields the lower bound 26N≥8·570−10·16 for N=|V|, so N≥170 for both members. The centered indicator-versus-weight estimate is
```
||w_opposite||² ≥ 570²/307 + (18·570−26·307)² N/[17·307(307−N)].
```
This exceeds 172·570/26 when N≥225, so the possible supports lie in 170..224.

Let their sizes be N,M and the unweighted incidence count between their supports be E. At most δ≤10 pencils have b=7; each such pencil's deficit relative to eight is one and weighted cost at most16. Each positive excess b−8 costs at least two. Consequently
```
E ≤ 8M−δ+(26N−8·570+16δ)/2
  ≤ 8M−10+(26N−8·570+160)/2,
```
and similarly after exchanging N,M. The centered unweighted polarity estimate gives
```
307E ≥ 18NM−sqrt(17N(307−N)M(307−M)).
```
The exact integer comparison in [verify-fuglede-f17-size68-low-degree.js](verify-fuglede-f17-size68-low-degree.js) checks 1540 unordered support pairs; after clearing the denominator, the minimum squared difference is 1229865025>0. Thus both members cannot have highest degree six.

This forces at least one highest degree seven or eight in the hypothetical size68 pair. It does not exclude size68.
