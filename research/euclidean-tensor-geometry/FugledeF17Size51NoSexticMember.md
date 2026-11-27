# Size 51 over F_17³: neither member can have maximum profile degree six

Assume the conclusions of [the size-51 degree-six reduction](FugledeF17Size51MomentSix.md). In particular the affine plane cap is nine, every tight pencil has at least nine positive profiles, and all occupancy profiles have degree at most nine. The cap-nine centered catalogue in [verify-fuglede-f17-size51-no-sextic-member.js](verify-fuglede-f17-size51-no-sextic-member.js) gives no quartic, 16 quintics all of weight four, 120 sextics of weights 2..5, and 1,712 septics of weights 1..6. There are no nonconstant profiles of lower degrees. Thus a member of maximum degree at most five is impossible (every tight pencil would have weight at least 9·4>21).

Let W=429, C=21, P the projective polarity matrix, and N=|V|, M=|V'| the support sizes for the two members. On a tight pencil with b positive profiles the weighted total is C. In a degree-six member, all weights are at least two, so b=9 or10; the maximum local square sum is 57, attained within the unconstrained weight model at (5,2^8). The weighted norm bound is therefore 57W/C. For a member of maximum degree at most seven, cap-nine weights are at most six; b≥9 and every positive weight is integral. Enumeration of partitions of 21 gives local squared sum at most 87, hence norm bound 87W/C.

For a degree R member, a tight pencil with no degree R lies entirely in the zero set of the nonzero degree-(16−R) moment form and is consequently a line factor. All other tight pencils have at least R+2 positives. Bounding weights on the opposite support by M_w, the weighted support inequality is
```
21N ≥ (R+2)·429 − (R−7)(16−R) M_w     (R≥7).
```
If one member has maximum degree six, take M_w=5 for the other member's support estimate. For opposite R=8 or9 this gives support at least 203. The centered weighted polarity inequality is
```
||w_opposite||² ≥ 429²/307 + (18·429−21·307)² N/[17·307(307−N)].
```
At N=203 this already exceeds sextic norm bound 57W/C. Thus a sextic member could only face a sextic or septic one.

The baseline b≥9 gives support at least 184 in either member. The weighted estimate bounds the support opposite a sextic by 197 and the support opposite a septic by 242. If both members are sextic, with E their incidence count, the weighted degree identity gives
```
E ≤ min(9M+floor((21N−9W)/2), 9N+floor((21M−9W)/2), 10M, 10N).
```
The first two bounds follow because each excess beyond nine costs at least two of opposite weight. If the first member is sextic and the other septic, the bounds instead are
```
E ≤ min(9M+21N−9W, 10M, 9N+floor((21M−9W)/2)).
```
The first term uses minimum opposite weight one in this orientation; the last uses the opposite (sextic) minimum two in the other orientation. On the other hand, P²=17I+J and row sum 18 imply the centered unweighted estimate
```
307E ≥ 18NM−sqrt(17 N(307−N) M(307−M)).
```
The exact checker compares all permitted supports (both in 184..197, or sextic support in 184..242 with septic support in 184..197). In each case the integer upper bound on E strictly violates this inequality. This excludes any degree-six member. A putative size-51 pair therefore requires maximum degree 7, 8 or 9 on both sides. Size 51 remains unresolved by this reduction.
