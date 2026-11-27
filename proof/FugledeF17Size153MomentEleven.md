# Size 153 in F_17^3: moment rigidity and a nonlayered weighted obstruction

Assume a spectral pair of size153=9·17. As in [FugledeF17Size221CapBootstrap.md](FugledeF17Size221CapBootstrap.md), for each member B its difference directions D(B) belong to the partner's uniform-normal set U, each affine plane contains at most17 points, no U contains a complete projective line, and every projective line meets U. A pencil through an affine line containing a points of B has total occupancy 153+17a. With r uniform normals on all projective lines of both members, the line cap is floor((153−8r)/17), so the initial cap is8.

## Exact planar cross bootstrap

The checker [verify-fuglede-f17-size153-cross.js](verify-fuglede-f17-size153-cross.js) uses the same triangle normalization and slope-mask DFS as the other F17 sizes. It certifies the following:
- A cap-eight planar set with at most five directions has at most five sites (105 masks, 1413 states). Consequently every 9-point slice gives at least six directions and both members have at least six U normals per projective line. The line cap therefore improves to six.
- At cap six, a planar set with at most eight directions has at most nine sites (3003 masks, 1226352 states).
- At cap six every nine-site set with at most seven directions has exactly six directions. Its two distinct five-point affine lines have axial coordinates affinely equivalent to H={0,±1,±4}. The twelve normalized completions in six-direction masks and 144 in seven-direction masks all have this property. For each a≠0, |H−aH| is at least thirteen.
- A planar six-site set of cap3 has at least five directions (15 four-direction masks,69 states, max five sites).

Suppose a nonzero homogeneous degree d≤11 form F vanishes on U_B and some projective line L meets U_B at most seven times. In the partner B', every affine slice parallel to L has at most nine sites by the cap-six planar bound and D(B')⊂U_B. Their total mass forces every one of the seventeen slices to have exactly nine. All are the crosses above, with two long five-point arms and only six difference directions per slice. In fact the union of the axial directions used by the arms lies in L∩U_B and has at most seven directions. The 34 arms therefore include at least five parallel arms. Five suffice for the following degree-eleven argument.

Choose a parallel group of k0≥5 arms along e. Their quotient sites have cap3, since four collinear five-point arms would place ≥20 sites in a spatial affine plane. The group determines at least four quotient directions. If k0≥6 then it has at least five quotient directions by the checker. For each quotient pair, the axial difference of the arm parameters has at least thirteen values (both affine copies of H), plus the axial direction e. Thus the associated radial projective line through e has at least fourteen D(B') points and is a rational factor of F. Let k be the number of distinct rational factors through e; it is at least four. Every nonfactor radial line has at most 1+d−k points of U_B and D(B'), and since U_B is six-blocking we have k≤d−5.

For degree d≤11, the nonfactor radial upper bound is at most 8, even with only four factors. All such radial direction planes have slices of size at most nine, so have uniform9 occupancy in B' by total mass. There are at least eighteen−k≥12 uniform B' normals through e (since k≤6). The pencil of an actual five-point arm in B' would have total occupancy at most 306−8·12=210, below the required 153+17·5=238. This is impossible. Thus for degree d≤11 any form vanishing on U_B forces U_B to meet every projective line at least eight times.

For d=11 set N=|U_B| and let n_L=|L∩U_B|. Projective incidence gives
```
Σ_L(n_L−8)(n_L−11)=N²−325N+27016 ≥610.
```
At most eleven rational line factors contribute positively, each by at most (17−8)(17−11)=54; the total is at most594. Thus no nonzero degree-eleven form vanishes on U_B. The usual moment form argument gives all mixed moments through degree eleven, so all reduced residue plane profiles have degree at most four.

## If no layer exists, exact weighted polarity is a contradiction

A layer means a profile with nine planes full of seventeen sites each and eight empty. Suppose neither member has a layer. Let w_B=(Σ_t binom(n_t,2)−17 binom(9,2))/17, supported exactly on the nonuniform normals. Projective polarity gives T_B=P w_B−36·1 and Σ_v w_B=1260. Every nonuniform normal of the partner induces a tight pencil of weight36. Centered exact univariate profile evaluation (enumerate a t^d with a≠0 and all coefficients of degrees≤d−2, and account for zero lifts) gives minimum positive weights 12 for nonconstant affine profiles (the unique zero lift is needed for mass153), 8 for genuine quadratics, 6 for genuine cubics, and 4 for genuine quartics.

In a tight pencil, the Radon homogeneous Vandermonde congruences make its degree≤b−2 in a pencil of b positive profiles. The no-layer hypothesis then makes b≤2 impossible; b=3 is all affine and its squared neighbor-weight sum is 432. With b=4 the weights are at least eight (only degrees≤2), so the squared sum is at most 3·8²+12²=336. With b=5 they are at least six, making the maximum 4·6²+12²=288. With b≥6 every weight is at least four; at given b the convex-square maximum is (36−4(b−1))²+(b−1)4², maximized at b=6 with value336. Thus every tight squared neighbor sum is at most 432.

Weighted double count gives ||w_B||²≤432·1260/36=15120. On centered vectors P has operator norm √17 because P²=17I+J. Consequently
```
w_E^T P w_A ≥ 18·1260²/307−√17(15120−1260²/307) > 36·1260,
```
contradicting tightness. The arithmetic is exact by squaring positive sides. More generally each layer in B increases the squared norm bound by at most 864: every tight opposite pencil containing a layer has that sole neighbor of weight36, and the total opposite weight of these pencils is 36 times the number of B layer normals by weighted count. Therefore the same polarity contradiction still holds if each member has at most one layer (replace 15120 by 15984). The [final two-layer analysis](FugledeF17Size153TwoLayersFinal.md) proves that each member has at most one layer, so this weighted inequality completes the exclusion.
