# A rank-eight discriminant bound for mixed norm-16/18 seeds

At mod-seven Seidel rank **36**, assume only `N20=G026=0` (raw `G026=U026+8U121`). Write `F=N16, N=N18`, both actual oriented graph-field populations. Then
```
72 N ≤ 3,880,800 + 47 F,
81 N ≤ 4,656,960 − 29 F,
N ≤ 56,220.
```
This is an upper bound, not an unconditional rank exclusion. Here is its additional ingredient over [mixed soft seeds](norm18-mixed-soft-seeds.md).

The original seven-discriminant space is nonsplit, dimension eight at rank 36. Use the scale where the scalar products of neutral graph fields reduce to their real scalar products modulo seven (a common scalar does not change the determinant type in dimension eight). Its determinant is a nonsquare because `(−1)^4=1`. At an actual seed, join two distinct norm-18 fields in a graph if their dot is 7 or 9. This graph is [triangle-free](norm18-triple-remaining-bridges.md), and as norm 20 is absent every nonedge has dot 10. An independent eight-set would give the nonsingular full-dimensional Gram `I+3J` with determinant `1+3·8=25≡4`, a square. Thus independent sets have at most seven elements, and since every neighborhood in a triangle-free graph is independent, its maximum degree is at most seven.

At any seed of occupancy `m`, let `b` be the number of unordered dot-ten pairs. Mantel and the degree bound give
```
b ≥ floor((m−1)²/4),     b ≥ m(m−8)/2.
```
In particular `8m−b≤70` and `9m−b≤84`: for `m≤14` use the first bound (its displayed differences increase through 14); for `m≥14` use the second (both displayed differences decrease thereafter). The expressions agree at 14, with `b≥42`.

By the [mixed occupied-seed proof](norm18-mixed-soft-seeds.md), each oriented norm-16 field f marks eight distinct seeds, none shared with another f, and at least six of its seeds have `m≤4`. At every f-seed, each marking t has `f·t=8`, all distinct markings have mutual dot 10, and hence `b=binom(m,2)`. In fact all eight f-seeds have `m≤6`. Otherwise choose seven markings and consider `z_i=2t_i−f` in the original seven-space. Each is perpendicular to f, each has norm zero modulo seven, and distinct pairs have dot `4·10−2·8−2·8+16=24≡3`. Their Gram is `3(J−I)`, of square determinant `3^7·6≡4`. But `f²=16≡2` is a nonzero square, so its seven-dimensional perpendicular space has nonsquare determinant. This contradiction proves the six bound even when some potential marking classes coincide (the tested Gram is nonsingular).

Designate six sites of each f as the `m≤4` type and its two remaining sites as the `m≤6` type, even if either is actually empty. On these two types, respectively, the maxima of `8m−binom(m,2)` are 26 and 33, and those of `9m−binom(m,2)` are 30 and 39. There are 55,440 seeds with total occupancy `9N`, of which exactly `6F+2F` were designated. Total `∑b≤385F` by the oriented-difference and root packing proved in [the preceding note](norm18-mixed-soft-seeds.md#from-seed-occupancies-to-the-actual-population). Consequently
```
72N ≤ 385F + 70(55440−8F) + (6·26+2·33)F,
81N ≤ 385F + 84(55440−8F) + (6·30+2·39)F.
```
Multiplying the first by 29 and the second by 47 cancels F, giving `N≤56220` after flooring. Neither this combination nor the local argument substitutes a shell average for the actual oriented graph count.

## Six-type consequence

The [native exact verifier](norm18_rank36_mixed_discriminant.py) proves that, if the five selected types `020,024,026,226,230` vanish, **151N+75F≥9,042,952**. This scalar implication also allows U121 and U337 and does not require a Fano-free hypothesis. Indeed, multiply by 42, retain the five absent unit terms with nonnegative coefficients, and subtract only nonnegative original angular-atom/marginal and compatibility counts as specified in the executable identity. The fixed factor 2402 converts the native anisotropic class coordinates to actual oriented N16 and N18, not counts per seed. From [F≤5,196 when N20=0](norm16-four-good-bad.md), the same oriented N must be at least 57,308. If U121 is absent as well, then the graph bound of 56,220 applies. Thus at rank 36 no support is contained in **{016,018,125,127,228,337}**. In particular the four-type candidate {016,018,125,127} is excluded; this is not a rank-36 exclusion.

Combining with the [previous mixed comparisons](norm18-mixed-soft-seeds.md), only `{018,020,024,026}` and `{018,020,026,125}` pass the accumulated four-type filter. Higher-cardinality support remains possible as far as these conditions show.
