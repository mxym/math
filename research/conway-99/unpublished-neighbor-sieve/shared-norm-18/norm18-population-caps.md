# Upper bounds for every norm-18 family in a maximal extension

Fix any maximal determinant-49 extension H of a hypothetical graph of any of the remaining ranks. The total number of H-eligible **oriented** neutral norm-18 graph fields is at most **2712**, unconditionally. It is at most **1588** if H has no eligible neutral norm-16 or norm-20 fields. In particular the rank-42 bounds apply directly to *all graph fields*, with no limitation on the other short types. The numbers count labels, not graphs.

Here n=W018 is the sum of the eligible oriented norm-18 populations divided by eight (no equality of residue-class sizes is assumed). The [integer certificates](norm18_population_caps.py) give
```
unconditional: n ≤ 5805113314040460 / 17122871911320 < 339.027;
no 16 or 20:  n ≤ 75103554564422 / 378203480076 < 198.580.
```
As 8n is an even integer, the two asserted bounds follow. In the first certificate the only graph upper row is [W014≤4](higher-moments.md): actual eligible Fano lines are pairwise perpendicular because all have zero residue in the final anisotropic plane, and there cannot be three mutually orthogonal lines. The other thirteen coordinates are nonnegative eligible label counts in the [common rank-48 moment dictionary](higher-moments.md). All use the standard *unit* substitutions where indicated in that dictionary.

The second certificate uses the same harmonic system, the two genuine zero hypotheses, and two more nonnegative slacks. The [disjoint canonical marks](coclique-sidon-cut.md) give W339−231−22W222−(W123−99−7W014)≥0. For the remaining row let Z=W028 and V=8W024. The [cross-centroid inequality](unconditional-cross-shell-centroids.md) with R=2,K=1 gives (12+4√2)n²≤84n+14Z+(7√2/2)V. Using √2>7/5 and 7√2/2<5 gives the rational consequence
```
88n² ≤420n+70Z+200W024.
```
The tangent n²≥2tn−t² at t=199 furnishes precisely the row T199 used in the checker. It is a graph consequence, not an assumed inequality of abstract theta series.

To verify, run `python3 norm18_population_caps.py` beside `higher_moments.py`. It regenerates all native harmonic equations. For each cap-minus-n row, the named nonnegative integer combination is subtracted; the residual is then checked to be exactly zero by rational elimination. No search, floating-point arithmetic or optimizer is used for verification.

If p=7^((44−r)/2)+1, averaging n over extensions gives N18(graph)/p. Thus the all-graph bound is N18≤339p, while if the two excluded types are absent graph-wide it is N18≤(397/2)p (round down to even). At ranks 40 and 42 these unconditional bounds are 16,950 and 2,712; the conditional bounds are 9,924 and 1,588. Retain independent sharper bounds where they apply at other ranks. These estimates alone do not exclude an additional rank.
