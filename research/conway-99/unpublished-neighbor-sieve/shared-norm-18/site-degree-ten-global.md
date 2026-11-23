# The unconditional form of the degree-ten site inequality

Let N_t and U_(a,t) count graph-wide signed neutral labels (both signs) and positive-charge unit labels, respectively, as in [the short shell dictionary](../short-shell-moments.md). For each of the possible Seidel ranks put p=7^((44−r)/2)+1. Then
```
6120N16+2940N18+580N20+300U(0,26)+3420U(1,21)+600U(1,25)+1920U(2,26)+240U(2,30)
 >= 210p+920U(2,28).
```
Here U(0,26) is the unit part of the neutral norm-26 population, not raw N26; their difference is 8U(1,21). Thus even the four-type support {N24,U(1,27),U(2,28),U(3,37)} cannot occur by itself at any of the four ranks.

**Lifting the rank-48 row.** Let F denote the eight-term expression in the [site certificate](site-degree-ten.md), with the two compulsory populations subtracted from its last two terms. Their graph proofs show F≥0 for any graph, without assuming a short type absent. Each other term is a nonnegative site count. In the direct witness below the zero rows are set in the **sorted** order 016,018,020,026,121,125,226,228,230. Every such row is written with the sign +V(k), i.e. raw minus its known nonunit transfers, which is the actual folded unit population V(k) after averaging site coordinates. All other equations (including normalization, translations, harmonic equations and site marginals) remain exact unconditionally. The orbit controls never discarded a signature by assuming that one of those nine unit populations was absent. They only used the rank-independent universal minimum and degree bounds.

The [direct rational row witness](site-degree-ten-dual.json) for F=−70 in the sparse case has coefficients on those nine rows, respectively,
```
2040, 980, 580/3, 100, 1140, 200, 640, −920/3, 80.
```
No rank-36 multiplicity or group action enters these coefficients. When the unit rows are retained as actual variables, the very same identity thus gives
```
210+3F = 6120V016+2940V018+580V020+300V026+3420V121+
         600V125+1920V226−920V228+240V230.
```
Every listed type has nonzero norm in the residual seven-plane. Its mean V over maximal extensions equals the corresponding actual graph-wide unit population divided by p, by the finite-space averaging in [affine-witness.md](../affine-witness.md). Averaging and using F≥0 proves the graph inequality. The negative sign on U(2,28) is why this family may be allowed in the enlarged four-type exclusion.

The [direct checker](site_degree_ten_global.py) regenerates all 282 rows, checks the 164 nonzero numerator coefficients in the rational witness by exact multiplication across all 172 variable columns **and the constant**, and then reads and verifies the nine lifted coefficients. Place the JSON alongside it; no RREF or optimizer is needed for this check.
