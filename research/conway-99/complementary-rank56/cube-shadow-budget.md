# Cube shadows add actual primal norm-eight vectors

Use the [complementary rank-56 lattice](README.md), and let y4 count its vectors of squared norm eight. Write N16,d for the actual oriented neutral −4 norm-sixteen count of deficiency deck d, where the decks are ordered as 8, 6+2, 4+4, 4+2+2, and four double edges. Put
```
W = N16,1 + N16,2 + 2N16,3 + 2N16,4 + 4N16,5.
```
At any rank, **y4 ≥ 40,592 + ceil(W/10)**. At rank 42 the stronger bound is **y4 ≥ 40,592 + W**. These compare actual graph populations in opposite eigenspaces; no complete rank is ruled out.

## A new, disjoint class of lattice vectors

Let z be a signed parity indicator of an actual induced three-cube Q. Its shadow h=(A+4I)z has squared norm 56 by the [cube shadow calculation](../unpublished-neighbor-sieve/shared-norm-18/n16-matched-partitions.md#genuine-cube-shadows). The vector h/√7 is exactly the sum of the complementary centered marks a_i with coefficients z_i. It lies in the primal lattice's M summand and has squared norm eight, so every distinct oriented shadow yields one y4 vector.

None is in the [40,592 mandatory-mark census](README.md#3-mandatory-primal-marks). A coincident mandatory mark would have signed-unit coefficients c of support at most six, with coefficient sum s of absolute value at most five, plus an integral shift in the binary glue plane. Its binary projection must vanish. Since the glue class has order eleven this forces s=0 and the binary shift is zero. Equality of the M projections then gives d=z−c in the kernel of A+4I, with sum zero, and d is nonzero since z has eight sites. Each sign's coefficient mass in d is at most 4+3=7. An entry of magnitude at least two would require opposite neighbor mass at least eight by the eigen-equation, so d is unit. It has support at most fourteen, and the [neutral minimum and Fano classification](../short-support-packing/README.md) make it a norm-fourteen Fano field. In particular c and z must be disjoint, so the signed support of d contains Q.

A Fano field cannot contain such a signed cube. In the standard model its two shores are nonzero vectors and nonzero covectors on the three-dimensional binary space, with edge evaluation one. If four chosen covectors have degree three on four chosen vectors, they all evaluate to one on the sum v of the four vectors, so v is nonzero and the four covectors are exactly those evaluating to one at v. Any chosen vector equal to v then has degree four; every other chosen nonzero vector has degree two, since its defining binary condition and the one for v are independent. Neither yields the desired degree three of a cube. This proves disjointness from the mandatory census.

## Exact census identity and discriminant refinement

Let k_h count the oriented cubes with shadow h. Two distinct cubes with a common shadow are disjoint and mutually matched, preserving their shadow signs. Conversely a matched partition of a norm-sixteen support supplies an ordered equal-shadow pair with difference the given oriented field: orient one cube as the field and the other as the negative of the field. Reversing the roles and both cube signs produces a second ordered pair (at the opposite shadow) with the same difference. These are exactly the two ordered pairs for that partition. By the [five partition counts](../unpublished-neighbor-sieve/shared-norm-18/n16-matched-partitions.md) it follows that
```
sum_h k_h(k_h−1) = 2W.
```
The [six-cube exclusion](../unpublished-neighbor-sieve/shared-norm-18/norm16-no-six-cubes.md) gives k_h≤5 everywhere; hence each shadow contributes at most twenty to the sum and at least ceil(W/10) new lattice points are needed.

At rank 42 there cannot be even three such cubes with one shadow. Their differences from a common base cube have ordinary Gram with diagonal sixteen and off-diagonal eight, so modulo seven their two-dimensional Gram has diagonal two and off-diagonal one, determinant three, a nonsquare. The pairing on the original seven-discriminant is this dot product modulo seven, up to a common nonzero scalar. Its anisotropic plane has square determinant over F7 (equivalently, the split plane has determinant −1, a nonsquare), and a common scale does not change its square class. The nonsingular two-dimensional Gram could not span that plane. Thus k_h≤2, so each shadow contributes at most two to the sum and at least W new primal points occur. The ceiling and orientation conventions are literal, not averaged over extensions.
