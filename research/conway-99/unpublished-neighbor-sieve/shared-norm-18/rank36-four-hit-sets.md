# Rank 36: 49 necessary hit sets leave 16 of 495 four-type supports

For a hypothetical graph of mod-seven Seidel rank 36, at most **16** of the 495 possible positive four-element supports of the [twelve selected unit types](../short-shell-moments.md) remain. This does not rule out those 16 supports or any whole rank. In the finite linear relaxation specified below, all 16 supports really do have nonnegative rational solutions with all four listed coordinates **strictly positive**. The rational solutions are not graphs or lattice constructions.

The [exact verifier](rank36_four_hit_sets.py) reads [49 sparse dual witnesses](rank36-four-hit-sets.json) and [16 rational controls](rank36-four-controls.json). From this directory run `python rank36_four_hit_sets.py` with python-flint. No numerical LP or external solver is used.

## Hit sets apply without a cardinality assumption

Each dual is a proof that the populations of the types in its set Z cannot all vanish, irrespective of how many other types are present. The smallest such sets in this catalogue have size three. The verifier confirms there are no containments among the 49 *listed* sets; no assertion of minimality among all possible graph-theoretic implications is made.

For j=0,…,12, the numbers of supports passing the indicated necessary tests are:

| Test | Number of supports at each cardinality j=0,…,12 |
|---|---|
| Intersect every one of the 49 sets | 0, 0, 0, 0, 19, 214, 552, 662, 471, 218, 66, 12, 1 |
| Also apply the support implication N16>0 ⇒ U(1,27)>0 | 0, 0, 0, 0, 16, 156, 392, 478, 354, 173, 56, 11, 1 |
| Also require at least one of N16,N18,N20 | 0, 0, 0, 0, 16, 145, 365, 456, 346, 172, 56, 11, 1 |

The second test is the [norm-16 injection](exclusion.md) U(1,27)≥N16. It matters: three of the nineteen provisional sets included N16 without U(1,27), so cannot be the actual positive support. The last test is the independent [original-lattice coefficient identity](rank36-four-types.md). For j≥5 these numbers count sets passing the specified filters, not certified feasible points. The actual graph has still more necessary conditions. In the following compact list, 16,18,20,24 are neutral norms, 26 is the **unit** neutral norm-26 population and a three-digit entry like 125 is U(1,25).
```
16 18 24 127        16 18 125 127       16 24 127 337
18 20 24 26         18 20 24 121        18 20 26 125
18 20 121 125       18 20 125 127       18 24 26 230
18 26 125 230       20 24 26 228        20 24 26 337
20 26 125 228       20 26 125 337       20 26 228 230
20 125 127 337
```

## Exact linear system

Use the two scalar theta pairs, raw W, graph-wide populations, graph zero-class coclique count M0, extension-mean compatible coclique count M=W222, and one-site excess S=W123−99−7W014 as in [the primal local cuts](rank36-primal-local-cuts.md) and [the original-lattice/global-Sidon cut](rank36-primal-global-sidon-cut.md). Specifically p=2402, m=pM−(p−1)M0 counts all graph cocliques, and the mean extension norm-four count Ŷ2 is not the original-lattice coefficient Y2. The raw nonisotropic averages have been divided by eight, so after the four specified raw-to-unit subtractions the actual selected graph populations equal p times the resulting coordinates. The verifier builds the unrestricted [higher-moment rows](higher_moments.py) and the three scalar identities (Y0=1 and the two isotropic gluing equations for Y1,Y2), **without** asserting any type zero. These have rank 39 on 63 homogeneous coordinates; the 24 free coordinates use the deterministic rational reduced echelon form, including the normalized form W000=1.

The 131 nonnegativity forms used in the controls are:
* the 60 raw populations, all 12 selected unit populations, M0,m,M−M0,S,N14 and the original norm-2 population Y1;
* the [Fano cap N14≤990](../../short-support-packing/README.md), the triangle bound Y2≥462, and the [norm-six floor Y3≥44804](../../rook-array-exclusion/rectangle-class-forest.md). Y4≥3564978 is the graph norm-eight floor, not a dual-shell statement;
* W014≤4, N16≤6930, N18≤289520, 9N18−4972N16≤646800, U(1,27)≥N16, and [U(1,21)≤44352](affine-triples.md), in the [short-shell](../short-shell-moments.md) and [overlap packing](exclusion.md) normalizations;
* the unconditional [four-family coclique inequality](coclique-sidon-global.md) and [degree-ten graph-site inequality](site-degree-ten-global.md);
* the compatible-coclique tangents H_t for the determinant-49 extension mean and C_t for the original zero class, at t∈{0,8,20,34,48,64,80,100,128}. The latter slack is 9Y2+18Y1−(369+10t)M0+5t²−4158. The former includes −18S and uses Ŷ2,W014,M instead. These follow by applying the individual coclique bound before averaging as in the [compatible packing proof](coclique-sidon-cut.md);
* the [graph-wide Sidon bound](rank36-primal-global-sidon-cut.md) with overlap cut k≤4 versus k≥5, and tangents m²≥2tm−t² for t=200,1000,3000,6000,10000,15000,30000;
* tangent lines to both [Fano difference inequalities](fano-difference-packing.md), and the integer nonedge-slot lines 2N20−42qN14+4158q(q+1)≥0, q=1,…,5. Every tangent uses x²≥2tx−t² in the original graph counts.

There are four additional **conditional** slacks. Their complete type-absence prerequisites are explicitly attached when a witness uses one:
* N20 absent: N14≤198;
* N20,N24 absent: N14≤112;
* N16,N20 absent: [N18≤16166](panel-heights.md);
* N16,N18,N20 absent: [U(1,21)≤5544](rank36-two-cycle.md).

## How to check the certificate

A row named `minus,k` is the negative of the unit-population form and is nonnegative only if type k is absent. All coefficients of each listed witness are positive integers. Its omitted set Z is checked to be exactly the union of all such k and all prerequisites of any conditional slack used. After reducing by the 39 common equalities, the weighted sum is exactly −d·W000 with integer d>0. Thus a graph with none of Z would give a nonnegative number equal to −d. Exhaustion over subsets of twelve types is just finite set intersection, not a floating-point feasibility test.

For the sixteen remaining four-type supports the verifier substitutes the stored 24 free rational coordinates into every raw and selected unit form, every unconditional slack and each applicable conditional slack. It checks W000=1 and checks that the support of strictly positive selected unit coordinates is **exactly** the specified set. The controls describe only this linear relaxation; for example they do not enforce every determinant, congruence, population integrality or graph incidence. No graph symmetry or marked-class transitivity is used.

The [subsequent Fano palette cut](rank36-four-fano-palette-cut.md) excludes three of the 16 supports from the actual graph. The rational controls above remain certificates for the older relaxation only.
