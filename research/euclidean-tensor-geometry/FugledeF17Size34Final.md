# Spectral cardinality 34 excluded in F_17³

**Theorem.** No subset of F_17³ of size 34 is spectral.

Assume a spectral pair of size 34 exists. The [earlier reductions](FugledeF17Size34MomentFive.md) give no layers, affine line cap two, plane cap six, and degree at most ten for every reduced plane profile. The [tight-pencil result](FugledeF17Size34TightCapTwelve.md) gives at least twelve positive profiles in each tight pencil. We write q=17w for the scaled weight, with total ordinary weight W=287 and each tight pencil weight C=15.

## The last five- or six-point plane

The [planar mask and lower-degree calculations](FugledeF17Size34SixDirectionsLowDegree.md) show that a plane with five or six points would force a tight pencil of the partner with the twelve slope indices [0,1,2,3,4,5,6,7,8,9,11,15]. That pencil's projected multiplicity is Boolean, because the pole is nonuniform in the first member and therefore absent from the partner's differences. Its exact integer Radon identity is Σ_i g_i(x+s_i y)=22+17f(x,y), and Σ_i q_i=255. The branches of maximum degree at most nine have been excluded. Only genuine degree ten remains.

A degree-ten profile forces all twelve profiles to be genuine degree ten by Vandermonde independence of any eleven tenth powers. For each position s_i let λ_i=1/∏_{j≠i}(s_i−s_j); the leading vector is scalar times (λ_i). A common dilation gives the two classes 1 and 3 modulo tenth powers. Translate in two independent direction coordinates to remove two degree-nine coefficients, and the remaining ten vanish by degree-nine Vandermonde independence. Thus all profiles are centered.

The mask's twelve projective symmetries are checked by [the stabilizer verifier](verify-fuglede-f17-size34-six-directions-symmetry.js). A coordinate change which sends (1,s_i) to a scalar ω_i times (1,s_{i'}) scales the coefficient of degree j at i by ω_i^j while moving it to i'. Six symmetries preserve the square class of the leading scale, and six swap it; all preserve profile mass, cap, weight and the Boolean condition. Therefore one only needs leading scale 1. After a compensating common dilation for each of the six preserving symmetries, their action on the degree-eight coefficient vector is exact. It suffices to test its lexicographically least orbit representative. Common reflection (x,y)↦(−x,−y) preserves the resulting degree-eight tuple and reverses the degree-seven coefficients, so the first nonzero degree-seven coefficient may be chosen in 1..8.

The [exact degree-ten verifier](verify-fuglede-f17-size34-six-directions-decic.cpp) generates all 53,264 centered cap-six mass-34 decics by interpolation and stores their possible coefficients in a trie. At every degree it evaluates the homogeneous Vandermonde equation using barycentric interpolation from free coordinates, keeping only coefficients that occur in the current lists. The true minimum weight in each remaining list gives a necessary bound on whether total scaled weight 255 can occur. The constant equation at the origin requires integer sum 22 or 39. A complete tuple is tested at every planar point for the integer Boolean Radon equation. No heuristic counts or numerical approximations enter the rejection.

The exact output is recorded in [the transcript](verify-fuglede-f17-size34-six-directions-decic-transcript.txt). The eight disjoint ranges cover all 833 canonical degree-eight prefixes. There is exactly one Boolean grid, at zero-based prefix 497. Its line (x=6) has the six ordinates (6,7,12,13,15,16).

To lift this grid to either member of a spectral pair, injectivity forces those six points to lift to a spatial affine plane with these same six ordinates, at heights (h_0,\dots,h_5) in `F_17`. Such a plane must be a cap-two set with exactly six determined directions, by the same tight-pencil argument. Subtract from all heights the affine function of the ordinate interpolating the first two heights. The third height is then nonzero, by cap two. A nonzero scaling makes it 1. Both edits are invertible affine maps of the plane. This leaves exactly (17^3=4913) possible height vectors `(0,0,1,h_3,h_4,h_5)`. The verifier computes the 15 quotients `(h_j-h_i)/(y_j-y_i)`, all finite because the ordinates are distinct. It rejects a collinear triple or a number of distinct quotients other than six. No vector passes. [An independent replay](verify-fuglede-f17-size34-decic-witness-nonlift.js) using affine images of the normalized planar templates gives the same rejection. Thus there is no valid spatial lift of the only Boolean survivor.

It follows that no plane can contain five or six points, giving plane cap four.

## Weighted and unweighted counting

At cap four the exact [centered profile verifier](verify-fuglede-f17-size34-cap-four-profiles.cpp) gives centered counts (0,16,20,112,2096) for degrees 6, 7, 8, 9, 10 respectively. Translates preserve weights and lower nonconstant degrees were already excluded. Every positive scaled weight q lies in [8,32]. The [exact final incidence check](verify-fuglede-f17-size34-final-incidence.js) finds that for any tight pencil with at least 12 entries and integer sum q=255, the local sum of q² is at most 6993 even allowing any integers in this range. Thus the squared norm of either ordinary weight vector is at most (6993·287/(17²·15)) by double counting over tight poles. Baseline pencil degree twelve implies each support has at least ceil(12·287/15)=230 normals. To obtain the squared-norm bound, sum the local squared-weight bound multiplied by the opposite weight at each pole. Reversing the sums counts each squared weight with total opposite weight exactly 15. For the lower bound, center the opposite weighted vector and the support indicator. The centered polarity matrix has operator norm √17 because its square is 17I there. Cauchy–Schwarz, using the tight total 15 at each supported pole, gives the centered indicator-versus-weight lower bound
```
||w_partner||² ≥ 287²/307 + (18·287−15·307)² N/[17·307(307−N)]
```
already exceeds the norm upper bound at N=235. The two supports N,M therefore lie in 230..234.

Let E be their unweighted one-step polarity incidence. Each positive neighbor beyond twelve costs at least 8/17 in opposite weight, so
```
E ≤ min(12M+floor((15N−3444)17/8),12N+floor((15M−3444)17/8)).
```
Centering both support indicators under P²=17I+J instead gives
```
307 E ≥ 18NM−sqrt(17NM(307−N)(307−M)).
```
The exact integer verifier checks all fifteen pairs of possible supports; if E_max is the incidence upper bound, then 18NM−307E_max>0 and its squared difference from the radicand is at least 1,531,336,876. This contradiction excludes size 34.
