# Fano difference packing in the neutral graph eigenspace

Let N_t count both orientations of all integral neutral fields of squared norm t. The following bounds hold in every prospective SRG(99,14,1,2), irrespective of its Seidel rank:
```
132 N20 ≥ 7 N14(N14−198);
660 N20 + 132 N24 ≥ 38 N14² − 4290 N14.
```
The first inequality strengthens the [Fano square cap](rank36-four-types.md) from a zero-norm-20 statement to a quantitative result. The second gives N14≤112 if N20=N24=0. Here norm-20 and norm-24 fields are necessarily unit: an exceptional entry of absolute value at least two would, after orienting and subtracting the site field, give a charge-one field of norm at most 19, below the charge-one minimum 21.

## Uniqueness of oriented differences, with the antipodal symmetry accounted for

By [three-point generation](../../short-support-packing/README.md#the-fano-configuration-is-determined-by-three-vertices-of-one-sign), two different oriented norm-14 Fano fields have at most two common positive sites and at most two common negative sites. Consequently Fano fields t and u on different antipodal lines satisfy |t·u|≤4 (apply the positive bound to u and −u).

Let d=t−u be a difference of two distinct, non-antipodal Fano fields. Then t·d=14−t·u≥10. For another representation d=r−s by Fano fields, r,s cannot both belong to antipodal lines different from t's: otherwise t·d≤8. If r=t or s=−t, the possibilities are exactly (r,s)=(t,u) or (−u,−t). The cases r=−t or s=t are impossible since they give t·d≤0. Conversely both displayed representations always occur and are distinct. This proves global uniqueness up to the specified antipodal swap, without a mod-seven class restriction or an automorphism hypothesis.

For each nonedge xy count by h_xy the oriented Fano positives containing x,y, so that Σh_xy=21N14 over 4158 nonedges. Each ordered pair counted by h_xy(h_xy−1) has exactly two common positive and two common negative sites and no conflicts, hence yields an actual norm-20 difference, by [the square argument](rank36-four-types.md). No such ordered pair is counted at any other nonedge. Each oriented difference has exactly two preimages, so
```
2N20 ≥ Σ h_xy(h_xy−1) ≥ (21N14)²/4158 − 21N14.
```
This proves the first inequality. A sharper discrete bound is 2N20 ≥ 4158 q(q−1)+2qr, where 21N14=4158q+r, 0≤r<4158, by balancing integer multiplicities.

## A rank-44 Gram constraint

Two different antipodal lines cannot have absolute inner product 3. Orient representatives t,u to have t·u=3. Then t−u has norm 22 and no entries of magnitude two or greater by the site-shift minimum, so there are exactly three common sign agreements and no opposite agreements. Two agreements of one sign force two agreements of the other sign, because their two actual common neighbors lie on the opposite Fano sides in both fields. Contradiction.

Choose m=N14/2 representatives and let c_j be the number of unordered pairs of *lines* with absolute dot product j∈{0,1,2,4}. For each pair with j>0 choose the sign so that the two oriented fields have dot j. Their difference and its negative have norm 28−2j. By difference uniqueness, no distinct unordered pair of lines emits either of these fields. Hence 2c4≤N20 and 2c2≤N24. In fact 2c1≤N26 and 4c0≤N28 by counting both sum and difference when the dot is zero. Similarly the long differences give 2c4≤N36, 2c2≤N32 and 2c1≤N30.

These line representatives belong to the 44-dimensional −4 eigenspace, and their Gram matrix has diagonal 14. Cauchy on its nonzero eigenvalues yields
```
196m² ≤ 44[196m+2(c1+4c2+16c4)]
      ≤ 44[196m+m(m−1)+6c2+30c4]
      ≤ 44[196m+m(m−1)+3N24+15N20].
```
Subtracting the first two terms on the right and putting m=N14/2 proves the second assertion. Integer multiplicities and all inequalities are for the whole graph, not an averaged maximal extension.
