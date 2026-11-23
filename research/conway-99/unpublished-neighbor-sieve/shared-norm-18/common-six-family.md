# A six-family population identity at every rank

In the coordinates of [the fixed-extension harmonic identities](higher-moments.md), including the four standard substitutions to unit counts V, there is a rank-independent exact identity:
```
20360 V018 + 16532 V020 + 888 V026 + 444 V127 + 6964 V226 + 5016 V230
= 82192 + 8531 W014 + 34068 V016 + 4572 V125 + 8012 V228
  + 132 W234 + 296 W335 + 631 W446 + 1200 S + 74 E.
```
Here E=W339−231−22W222−S≥0 and S=W123−99−7W014≥0. The nonnegativity of E is [the disjoint ordinary, coclique, and extra-mark construction](coclique-sidon-cut.md); these labels are all compatible in the same maximal determinant-49 extension. W339 is isotropic and is an actual count in that extension. All coefficients refer to folded populations, not unweighted graph totals.

The [exact arithmetic verifier](common_six_family.py) imports the common harmonic rows, inserts the definitions of E and S, and reduces the asserted zero identity by rational elimination. It uses no rank-42 Fourier equations or graph-wide-versus-fixed-extension identification. Averages over all maximal extensions retain the inequality at each rank; the six nonisotropic V then count the graph fields divided by p=7^((44−r)/2)+1. If the six named types are absent graph-wide, they vanish in every eligible subfamily, and the positive constant gives an immediate contradiction. This last argument would also work without taking the average.

Combined with the [32 common support constraints](common-unit-hits.md), this removes the triple {24,121,337} everywhere, leaving at most **eighteen of the 220** exactly-three-type supports. It also cuts four- and five-type possibilities: after the usual norm-16 implication the combined counts, in order of cardinality zero through twelve, are
```
0, 0, 1, 18, 115, 333, 537, 545, 371, 175, 56, 11, 1.
```
The lone pair is 18/24, separately excluded. Neither that result nor any other rank-specific exclusion is an input. No survivor is a claimed graph.
