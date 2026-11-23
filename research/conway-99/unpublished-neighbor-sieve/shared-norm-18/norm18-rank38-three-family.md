# Three unit families cover rank 38

At Seidel rank 38, at least one of the **oriented neutral norm-18 fields**, **unit neutral norm-26 fields**, and **unit positive-charge (3,37) fields** is present. In particular, if both latter types are absent then the actual graph-wide number of oriented norm-18 fields is at least **1,496**. There is no absence assumption on the nine other selected types, no zero-Fano premise, and no symmetry hypothesis. This does not exclude rank 38.

Use the [native original/extension site chart](original-site-populations.md) and its [exact export](original_site_populations.py), with rank 38 and p=344. Write W for a folded raw population averaged over maximal determinant-49 extensions, V for its unit part, C for the original zero-class population, and G for the graph-wide raw count. Each selected type here is nonisotropic, so its actual unit count is 344V. In particular V026=W026−8W121: the exclusion concerns the unit shell only. The neutral N18 includes both signs.

In these chart units the [exact checker](norm18_rank38_three_family.py) gives
```
1085141120 V018 + 45559360 V026 + 107685760 V337
    = 4715981872 + nonnegative terms.
```
Raw positive terms are W020,W024,W222,W226,W333,W335. Further nonnegative terms are V125, graph-wide G222 and G014, original C014, the [N16 cap and lift to V127](exclusion.md), one difference of compatible and original counts and two nonnegative one-site orbit populations at folded charge −4 and cost 46, and E=W339−231−22W222−S with S=W123−99−7W014. As in [the disjoint marking injection](coclique-sidon-cut.md), E counts the remainder after three disjoint families at each maximal extension: ordinary triangle marks, 22 labels per compatible Hoffman coclique, and at least one label per compatible extra unit (1,23) mark. All three of these isotropic counts are **literal compatible counts in that extension**, not counts divided by eight; their averages retain the inequality. The positive G222 term is instead the actual count 344W222−343C222. No rootlessness conclusion for rank 36 is used or transplanted.

The checker writes out every positive coefficient and verifies the identity by rational row reduction in the 205 native marked columns. With V026=V337=0 the unrounded bound is 344·4715981872/1085141120>1495, so antipodality gives at least 1496 oriented fields. This lower bound is not larger than the previously proved 12,320 upper bound under the **additional** assumptions N16=N20=0. Run `python norm18_rank38_three_family.py` beside the checked-in site-chart sources with SymPy and python-flint.
