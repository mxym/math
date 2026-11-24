# A five-way hit at every remaining rank

At Seidel rank 38 at least one of **018, 127, 228, 230, 337** is positive among the selected unit populations. Together with the previously checked ranks 36, 40 and 42, this gives one rank-independent requirement on every hypothetical graph. Equivalently, no graph can use only the six selected types `020,024,026,121,125,226`: the additional type 016 also disappears because it forces 127. This does not exclude any rank outright or assert a positive lower bound on a specified one of the five terms.

## Rank 38 certificate

Use the [205-variable original-site chart](original-site-populations.md), averaged over maximal determinant-49 extensions at 7; here the extension-mean to graph scaling for anisotropic shell populations is 344. Its normalized selected **unit** columns are `V(a,t)`, `u[a,t]` in the checker, so the corresponding actual graph unit populations are `344 V(a,t)`. Raw and unit need not coincide: in particular if 127 is absent and 016 is absent, the raw 127 mass can still be `2W226`. Nothing here sets that raw mass to zero.

Besides rows directly exported by the chart, only three inequalities are used. Let `M=C222` count original zero-seven-class Hoffman cocliques and write `Y1=C014`, `Y2=C028+2C339` for the *original* primal theta coefficients. The factor two counts both charge signs; these are not the averages of the extension coefficients. At `h=100,128`, the [original-zero-class coclique tangents](rank38-three-hit-sets.md) give
```
9 Y2 + 18 Y1 − (369+10h) M + 5h²−4158 ≥ 0.
```
These are exactly the published `('Ct',h)` rows of [the rank-38 checker](rank38_three_hit_sets.py). In particular they do not assume Y2≥968, that all graph cocliques are original, that M exceeds any chosen threshold, or that there is no Fano.

For the third inequality let `N14,N20` be actual signed (both orientations) neutral graph populations, without requiring original class. The [integral Fano nonedge-slot counting argument](fano-difference-packing.md) gives for nonnegative integer (h)
```
2 N20 − 42h N14 + 4158h(h+1) ≥ 0.
```
Indeed the multiplicities of oriented Fano positive shores containing a given unordered nonedge, summed over all 4158 nonedges, are nonnegative integers with sum `21 N14`, and their ordered collision count is at most `2 N20`; apply `j(j−1)≥2hj−h(h+1)` at each nonedge. We use exactly `h=3`. Thus the positive shell in this row is graph-wide `N20=344 W020`; the negative one is full `N14=344 W014−343 C014`, not a folded Fano population.

The [standalone exact checker](ranks_all_five_family.py) tests the coefficient identity
```
sum over six displayed unit-column weights w_k V_k
  = 16,924,142,964,305,920 + sum over the 14 explicitly weighted nonnegative rows.
```
The six unit types on the left are 016, 018, 127, 228, 230 and 337. All coefficients on both lists are positive integers written out in the checker. The other rows are the marked-site compatibility or nonnegativity rows and two original triangle/path coordinate floors from the native chart, the nonnegative raw `W444`, original `Y1`, and the unit columns 121, 226 and 125. These do not assume absence of the corresponding shells. Vanishing of all six left masses is impossible. The [rank-independent lift](common-unit-hits.md) `V(0,16)≤V(1,27)` then removes 016 from the hit set.

## Crossing the ranks

At rank 36 the [rootless hit sets](rank36-rootless-hit-sets.md) already force at least one of 018, 127, 228, 337 (even without 230); the [earlier four-hit table](rank36-four-hit-sets.md) also contains exactly the stated five-type clause. At ranks 40 and 42 apply the previously established [six-type large-Hoffman exclusion](high-rank-five-hit.md) and the same 016-to-127 implication. The three inputs concern the same twelve graph-wide **unit** types.
