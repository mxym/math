# Size153 in F_17^3: exact two-layer exclusion and final theorem

**Theorem.** No subset of F_17^3 of size153 is spectral. This concerns only this cardinality.

Use [FugledeF17Size153MomentEleven.md](FugledeF17Size153MomentEleven.md) for affine line cap six, plane cap seventeen, and moments through eleven; its weighted-polarity endgame excludes a spectral pair whenever each member has at most one layered normal. A layered normal has nine parallel planes of occupancy seventeen and the other eight empty. It remains to eliminate two distinct layered normals in one member.

Choose their two independent affine normal coordinates as x,y. The member projects to a count array f on a 9×9 grid X×Y, where X and Y are nine-site subsets of F_17. Each row and column has integer sum17, and each cell is the count on an affine line, so lies in {0,...,6}. All moment equations Σ_x,y x^a y^b f(x,y)=0 in F_17 for a+b≤11 hold by the global mixed moments. For x∈X set λ_X(x)=1/∏_{t∈X\{x}}(x−t), and similarly λ_Y(y). The joint moment annihilator on this grid is exactly
```
f(x,y) = λ_X(x) λ_Y(y) Q(x,y) in F_17,     total degree Q ≤4.
```
Indeed the evaluated powers with a,b≤8 and a+b≤11 are independent, by the product Vandermonde system, and their codimension is fifteen. The weighted evaluations of every polynomial monomial of total degree≤4 lie in their orthogonal complement: the product monomial has total degree at most15, so at least one coordinate degree is at most seven, which sums to zero against the one-dimensional barycentric weights. The fifteen monomials of total degree≤4 are independent on the grid, proving equality.

The exact verifier [verify-fuglede-f17-size153-two-layers.js](verify-fuglede-f17-size153-two-layers.js) enumerates the affine orbits of all 9-site level sets in F_17, finding 95. Affine normalization of each axis and swapping the axes preserve all constraints, so take one of 4560 unordered pairs of representatives. For any Y, list all possible rows by assigning their first five entries in {0,...,6}, dividing these entries by λ_Y, and interpolating a degree-at-most-four polynomial R_i(y)=λ_X(x_i)Q(x_i,y). The remaining four row entries must again lie in {0,...,6}, and the row's integer sum must be17. The row catalog sizes range from131 to200.

For a fixed X and Y, choose rows in increasing x order. The coefficient of y^j in R_i(y), divided by λ_X(x_i), is a polynomial in x of degree at most 4−j. Once 5−j prior x values are known, use interpolation to fix that coefficient for the next row. The checker indexes the allowed rows by the already-determined prefix of high coefficients and tries all matches, also rejecting any partial column sum above17. This is exhaustive because all coefficient constraints are eventually enforced, and a genuine row is determined by its first five entries among allowed values. Final column sums are checked exactly. The depth counts are [4560,672251,5902324,3073973,93012,437,8,2,2,2], with precisely two complete normalized matrices.

Both matrices use X=Y={0,1,2,4,5,6,8,9,10}. For the first matrix an oblique projected line has mass33 in each form x+4y and x+13y; for the second, in x+y and x+16y. Oblique projected lines correspond to spatial affine planes, so mass33 contradicts plane cap seventeen. Consequently each member has at most one layered normal.

The weighted endgame in [FugledeF17Size153MomentEleven.md](FugledeF17Size153MomentEleven.md) now completes the result. With at most one layer per member, the tight-pencils square sum estimates give ||w_B||²≤15984. Writing the projective polarity matrix on 307 sites and centering both weight vectors, its centered operator norm √17 yields
```
w_E^T P w_A ≥ 18·1260²/307 − √17(15984−1260²/307) > 36·1260,
```
where the exact integer check of the last inequality is in [verify-fuglede-f17-size153-weights.js](verify-fuglede-f17-size153-weights.js). Tightness gives equality to 36·1260, contradiction.
