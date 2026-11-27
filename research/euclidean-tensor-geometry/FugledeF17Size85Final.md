# Cardinality 85 excluded over F_17³

**Theorem.** There is no spectral subset of F_17^3 of size85=5·17.

**Prior-art clarification.** The [classical cyclotomic determinant obstruction](FugledeCyclotomicDeterminantObstruction.md) already excludes cardinality 85. The geometric argument below is an independent proof for that cardinality.

Suppose there is a spectral pair. Prior size85 deductions give M9, at most sixteen sites on each affine plane, no profiles of degree one or two, and all nonconstant reduced occupancy profiles have degrees at most six. Use the degree-nine proof in [FugledeF17Size85MomentNine.md](FugledeF17Size85MomentNine.md) and its prerequisites. For a member write V for its nonuniform plane normals, and w=(Σ g(t)^2−425)/34 for the corresponding integer profile weights. The total weight is W=710, and every tight pencil (the polarity neighborhood of a nonuniform normal of the other member) has total weight C=30. Each member's uniform normal set has at most twelve sites on any projective line, so every tight pencil has at least six positives. If b is the number of positive profiles on a tight pencil, the Radon Vandermonde argument bounds profile degrees by b−2.

## Norm bounds and support intervals

The exact centered univariate catalogue in [verify-fuglede-f17-size85-moment-eight.js](verify-fuglede-f17-size85-moment-eight.js) gives minimum weights 6,4,3,2 for genuine degrees 3,4,5,6, respectively, and maxima 13,15,17,19. With no full planes there are no zero lifts. In particular any tight pencil must have a degree at least four (otherwise six positives of minimum weight six would sum to more than thirty). For maximum degree R=4,5,6, the local sum of squares bounds S_R are 180,198,284: b≥6, each entry is at least the minimum for degree min(R,b−2), and entries sum to30. The integer checker below enumerates all such nondecreasing weight tuples. Weighted incidence counts each normal's squared weight C times when local sums are weighted by opposite weights, so ||w||²≤S_R W/C.

The degree-(16−R) moment form of a member whose highest degree is R is nonzero, vanishes on uniform directions, and is nonzero precisely on its degree-R normals. If a tight pencil has no degree-R profile its projective line divides this form (its degree is <17). Thus at most 16−R tight pencils are exceptional, and all other tight pencils have at least k=R+2 positives. Let N=|V| for this member, and suppose the opposite weights have maximum ≤a. Weighted incidence with the pencil cardinalities yields
```
C N ≥ k W − (k−6)(16−R)a .
```
The centered indicator-versus-weight polarity estimate is
```
||w_opposite||² ≥ L(N) = W²/307 + (18W−307C)² N/[17·307(307−N)] .
```
This uses the identity P²=17I+J for the incidence polarity P; N=307 is impossible by the row sums. The right side is strictly increasing in N.

If only one member has degree six, bound the other weights by19 in the support estimate, so that N≥177 and L(N)≥4966.92, while the other has norm at most S5 W/C=4686. If neither member has degree six and only one has degree five, use a=17, giving N≥160 and L(N)≥4300, while the other has norm at most S4 W/C=4260. Both instances contradict the estimate. The only possibilities left have a common maximum degree R for both members. The lower support bound and the upper norm bound combined with the indicator estimate then give:
```
R  S_R  a   possible support sizes in either member
4  180  15  142..158
5  198  17  160..170
6  284  19  177..207
```

## Unweighted incidence eliminates the remaining intervals

Write M for the opposite support size. Let E be the unweighted incidence count of the two supports under polarity, i.e. the sum of cardinalities b over the M tight pencils of the first member. Separate exceptional pencils (no degree-R profile) from the others. Let δ be the sum of the nonnegative deficits k−b over the exceptional pencils with b<k. All other pencils have b≥k. Then 0≤δ≤(k−6)(16−R)=δ_max. Put m=8−R, a lower bound on every positive weight of the opposite member since both now have the same maximum degree R. In the identity C N=Σ w_opposite b, the negative part relative to kW has magnitude at most aδ, whereas the positive part is at least m times the sum of the nonnegative excesses b−k. Therefore
```
E ≤ kM − δ + floor((C N−kW+aδ)/m)
  ≤ kM − δ_max + floor((C N−kW+aδ_max)/m).
```
The last expression is monotone nondecreasing in δ because a≥m. Use the symmetric bound with N,M exchanged as well. At R=4, the additional bound E≤7 min(N,M) follows from every positive weight being at least four and each pencil's weight sum30.

Independently, applying centered polarity to both indicators and using Cauchy–Schwarz gives
```
307 E ≥ 18 N M − sqrt(17 N(307−N) M(307−M)).
```
The exact checker [verify-fuglede-f17-size85-final.js](verify-fuglede-f17-size85-final.js) enumerates the three short support intervals. With E_max the minimum of the applicable upper bounds, it checks T=18NM−307E_max>0 and T²>17N(307−N)M(307−M). Across 153,66,496 unordered support pairs, the minimal positive squared differences are 947123244,4709678404,7957470700, respectively. Thus all pairs of supports contradict the lower bound. This completes the cardinality85 proof without any additional classification of sextic or quintic pencils.
