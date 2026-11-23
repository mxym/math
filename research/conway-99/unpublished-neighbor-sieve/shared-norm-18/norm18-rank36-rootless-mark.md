# At rank 36 an N18-free graph needs at least five selected unit types

Every rank-36 graph must hit **{016,018,230,337}**, without other support assumptions. In particular, if just N16, U230 and U337 vanish then the graph has **at least 5,260 oriented norm-18 fields**. Combining with the [39 native rootless hitting conditions](rank36-rootless-hit-sets.md), this rules out the only N18-free exact-four candidate, {020,026,125,228}. At most seven exact-four supports remain. This does not assert N18 for graphs with five or more types. Adding this hit to the earlier 39 and retaining `N16>0 ⇒ U127>0`, the numbers of supports surviving these necessary tests at sizes 0 through 12 are `0, 0, 0, 0, 7, 72, 236, 371, 325, 171, 56, 11, 1`.

## Exact marked identity

The [small checker](norm18_rank36_rootless_mark.py) verifies a single identity directly in the [original single-site chart](original_site_populations.py), not by invoking a numerical program, combining independent feasible controls, or setting any selected unit column to zero. The optional `export=True` returns that same exact chart before the original routine's per-certificate loop; its standard calculation and ranks are unchanged (205 columns, 295 generated equalities of rank 184). There is no change of basis in the certificate.

In this native convention, W counts raw graph types normalized in the determinant-49 extension, averaged over extensions and site choices; U is the unit part after the four proven nonunit subtractions. The original-zero seven-class sector is C, not W. On the isotropic sector the graph total is 2402 W−2401 C; on the anisotropic sector it is 2402 W. All four displayed unit types are anisotropic. In the checker `glob((0,14))` is the actual oriented graph-wide Fano population; `c((0,14))` is its zero-original-class part (the original Y1). The former vanishes by the [rank-36 Fano theorem](../rank36-no-fano.md).

With native U (not graph totals) the exact left side is
```
  90517361060407208 U016 + 32492184832883716 U018
+   250429011864588 U230 +  2465831431509517 U337 − 71137281214783553.
```
It equals the following nonnegative rows with the positive integer multipliers in the source, plus one negative multiple of the vanishing graph-wide Fano population:

* raw W022,W024,W121,W226,W333,W335,W444 and original C014;
* the original chart's proven N16-to-U127 lift;
* W−C in the isotropic one-site orbit represented by (−4,46,2), nonnegative because the zero original class survives in every extension;
* true zero-original-class incidence lower bounds from the ordinary edge marks at (2,36) with site entry −2, ordered nonadjacent-pair difference marks at (0,42) with entry 1, and positive three-path marks at (3,53) with entry 1, in the unmodified native chart's `mark` convention;
* two individual nonnegative marked counts: maximal-folded W at orbit (−4,44,−1), original C at (−2,36,−1).

For the nonadjacent-pair row, `d_i−d_j` has +3 at `i`, −3 at `j`, and twelve entries of each unit sign, since the two common neighbors cancel. Its ordered endpoints are recovered from its two extreme entries, giving 99·84 = 8,316 distinct marks. Its cost is 42 and its original seven-class is zero as it is a difference of two single-site marks.

Multiplication by 2402 converts all four coefficients to a comparison of the corresponding actual graph-wide populations. With 016,230,337 absent, the resulting lower bound for N18 exceeds 5258 and N18 is even. On the former exact-four N18-free candidate this is a direct contradiction, not a comparison of N20 to N18.
