# The 26-point equal-frame obstruction eliminates one signed split

Assume the surviving rank-42 {018,121,125} aggregate from [the four-coclique calculation](cost21-four-coclique-walk.md). Its Hoffman rank is exactly 16. Indeed at most 16 was proved; were it ≤15, at least 12 copies of eigenvalue 2 would be forced for its 27-vertex one-overlap graph. Even after removing those copies the shifted square budget must include a Perron contribution (the common hole puts all 12 dependencies in the zero-sum subspace). Thus 2e−84≥(2+2e/27)², impossible at every integer 55≤e≤60 (the difference of the left and right sides is increasing there and already negative at 60).

Suppose now the signed sizes are 33,26. The two perpendicular signed classes of size 26 both have 12-dimensional difference span, and those spans coincide. In fact the orthogonal-span proof gives dimensions at least d(33)=14 and d(26)=12 for the two pairwise sums of difference spans, plus two independent residual directions. The total budget outside the actual 16-dimensional Hoffman span is 28, so every bound is attained. The same reasoning on each 26-group forces its own span to be the full common 12-space U.

Let A be its graph of dot-four pairs with average degree x. The previously proved centered trace inequality is sharp: d(26)=12 equals 24(26−1)/(26+24). Consequently the square (5x−3(26−1))² in its derivation vanishes, so x=15; the squared-degree Cauchy bound must also be equality, giving a regular graph. Its centered, unscaled Gram H(3I+A)H has trace 60 and rank 12, and equality in the Frobenius rank bound gives all 12 nonzero eigenvalues equal to 5. The ordinary integral-field Gram is 7(3I+A)−3J. Its class mean has squared norm 24/13 from the regular row sums, is orthogonal to U, and the centered vectors (rows of T) form a tight frame on U with T^t T=35 I_U. The second size-26 group similarly has centered row matrix R and mean of squared norm 24/13.

Write S_{ij}=t_i·u_j/7 for the **uncentered** fields of the first and second groups. All S_{ij} are integers: the two residue classes are perpendicular. Since both means are perpendicular to U, both are also perpendicular to the other group's centered vectors. Every row and column of S therefore sums to the same integer h, and |h|≤(26/7)(24/13)=48/7, so |h|≤6. Subtracting (h/26)J from S gives TR^t/7. Thus
```
SS^t = (35/49) TT^t + (h²/26)J
     = 5(3I+A) + ((h²−90)/26)J.
```
The last equation uses TT^t=7(3I+A)−(3+24/13)J. Integrality forces h²≡12 mod26, impossible for |h|≤6. The (33,26) split is excluded; the (30,29) split is not excluded by this argument. At that remaining split both pairs' within-fiber difference spaces coincide within the pair and are exactly 13-dimensional, by the same saturated 28-dimensional budget.

The [shared-plane comparison](cost21-final-plane.md) excludes the remaining `(30,29)` split, completing this rank-42 support exclusion.
