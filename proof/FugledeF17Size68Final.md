# Cardinality 68 excluded over F_17³

**Theorem.** There is no spectral subset of F_17^3 of size68=4·17.

Suppose a spectral pair exists. Use the [degree-eight and plane-cap-twelve reductions](FugledeF17Size68MomentEight.md) and their no-layer and uniform-pencil prerequisites. These give line cap4, plane cap12, no zero lifts, and reduced occupancy degrees at most seven in both members. The low-degree reduction in [FugledeF17Size68LowDegree.md](FugledeF17Size68LowDegree.md) rules out either member having highest degree≤5, and also rules out both highest degrees being six. Its certificate that no tight b=7 pencil exists applies globally, since any such pencil in any member has degrees at most b−2=5. Therefore every tight pencil of either member has b≥8. It remains to exclude the degree pairs (6,7) and (7,7).

## Weights and polarity facts

For a member with integer plane occupancy profile g(t) in a normal direction, its weight is (Σ_t g(t)²−272)/34. Every nonuniform normal has positive integer weight (the moment degree bound makes the square sum congruent to272 modulo17; parity adds the factor two). Uniform normals have zero weight. Write V_B for the nonuniform support. The total weight is W=570 in either member, and a tight pencil (orthogonality neighborhood of a nonuniform normal in the partner) has total weight C=26. Let N,M denote support sizes in the respective members, E the unweighted incidences between the two supports under projective polarity, and P the incidence matrix of that polarity on the 307 projective points. Both sides of the weighted incidence identity follow by double counting:
```
26 N = Σ_{v in opposite support} w(v) b(v),       E = Σ_{v in opposite support} b(v),
```
where b(v) is the number of positive profiles of the first member in the pencil opposite v. If S(v) is the local sum of squared weights, then 26||w||²=Σ w(v)S(v).

The polarity satisfies P²=17I+J with row sum18. Applying centered Cauchy–Schwarz to one support indicator and the opposite weight, then to both support indicators, gives
```
||w_opposite||² ≥ L(N) = 570²/307 + (18·570−26·307)² N/[17·307(307−N)],
307 E ≥ 18NM − sqrt(17 N(307−N) M(307−M)).
```
The case N=307 directly contradicts the row-sum identity; L is increasing.

A genuine degree-seven profile detects a nonzero evaluation of the degree-nine moment form, and all other profiles give zero. Thus in any septic member at most nine tight pencils lack septics: their entire projective lines divide its nonzero degree-nine form. Every other pencil has b≥9 by the degree restriction b−2. Therefore an exceptional tight pencil can have a deficit of at most one relative to the baseline nine, and only if b=8.

## Profile bounds and local norms

The centered residue catalogues give minimum positive weights two in a sextic member and one in a septic member. A sextic member has individual weight≤12: through each positive weight there is a tight pencil (by symmetry of the polarity identities), and its other at least seven weights are each ≥2. Its local square sum is at most172, from C=26 and b≥8 with positive weights at least two, with extremal multiset (12,2^7).

The cap12 exact centered catalogue in [verify-fuglede-f17-size68-septic-profiles.js](verify-fuglede-f17-size68-septic-profiles.js) gives maxima 8,9,10,11 for genuine degrees four through seven. The same catalogue for cap 9 gives maxima 4,4,6,6. It determines the first d+1 values of each centered polynomial by interpolation, with two linear constraints on the highest coefficients. Argument dilation permits one leading representative for each coset of the d-th powers. In a septic member call a normal heavy if its weight is at least seven. Such a profile must have peak≥10. The exact cap-four planar fact that at most nine directions permits at most nine points (see [verify-fuglede-f17-size85-degree-nine-geometry.js](verify-fuglede-f17-size85-degree-nine-geometry.js)) implies a ≥10-point plane determines at least ten directions. Its direction line in the partner normal space is therefore a factor of the partner's F9 if the partner is also septic: the difference directions belong to U and exceed the degree. There are at most nine such heavy normals in each member in the (7,7) case.

For a tight pencil in a septic member, b≥8 and all weights are ≤11. At b=8 the local degree bound b−2=6 gives minimum weight two; at b≥9 use minimum one. The exact partition envelope for squared sums at heavy count h=0,1,2 is 122,172,192; h≥3 cannot occur since three weights≥7 and the remaining at least six weights≥1 already exceed26 for b≥9 (b8 minimum two also suffices). Therefore every local square sum is bounded by 122+50h. In the (7,7) case each heavy normal sees opposite weight26, so weighted double counting gives
```
||w||² ≤ 122·570/26 + 50·9.
```
Whenever (6,7) holds we may simply use the weaker local bound212 for the septic member.

## Final support-incidence comparison

For (6,7) let N be the sextic size and M the septic size. The baseline b≥8 for the first member gives N≥176. The septic baseline b≥9 has at most nine exceptional deficits each costing at most12 of opposite weight, so M≥194. The opposite norm bound and L give N≤240, M≤224 (using the local ceilings212 and172). For the sextic member every positive excess beyond eight costs at least one of opposite weight, giving E≤8M+26N−4560. For the septic member every positive excess beyond nine costs at least two, and if there are δ≤9 exceptional unit deficits then their weighted cost is at most12δ. Hence
```
E ≤ 9N−δ + floor((26M−5130+12δ)/2)
  ≤ 9N−9 + floor((26M−5130+108)/2).
```

For (7,7), the septic support baseline and opposite individual weight≤11 yield both sizes≥194. The above refined norm bound and L yield both sizes≤207. For each orientation the baseline nine with δ≤9 unit deficits of cost ≤11δ and positive excess of cost at least one gives
```
E ≤ min(9M−9+26N−5130+99, 9N−9+26M−5130+99).
```

The exact integer check [verify-fuglede-f17-size68-final.js](verify-fuglede-f17-size68-final.js) verifies the local envelopes, interval bounds, and that these upper bounds on E contradict the centered unweighted lower bound. It checks 2015 ordered asymmetric pairs and 105 unordered symmetric pairs with respective minimum cleared squared gaps 6257479076 and 1617026409. All cases are excluded.
