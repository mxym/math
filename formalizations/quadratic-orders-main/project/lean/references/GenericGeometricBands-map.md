# Uniform actual band endpoint entropy

Implementation: `Entry002/GenericGeometricBands.lean`.
The module combines the proved actual scalar construction in
GenericGeometricScale, the exact real-mean band definitions in
GenericBandParameters, and the actual geometric endpoint iteration in
GenericGeometricEnrichment. The source chain follows the pinned OpenAI
family028 MultiscaleSchedule, commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` (Apache-2.0).

`uniform_band_geometric_entropy` proves a positive lattice threshold U₀ fixed
before any actual prime batch, walk, starting time, or finite band schedule.
For every actual batch with `1≤μ≤2X`, true dyadic prime bounds, and every actual
injective bounded-step walk, its remaining scale conditions at each stage are
`U₀≤bandScale(g,U,j)`, `1280X≤g⁵*bandScale(g,U,j)`, and the genuine batch
capacity `bandSize(μ,g,U,j)≤|S|`. It constructs all geometric margins and
fresh-information bounds and proves

`(1−2^(−l)−80g)*bandSize(μ,g,U,l)*μ ≤ PE(P.run z (bandLength g U) l)`.

`uniform_band_common_geometric_entropy` proves the analogous bound, reduced by
an explicit suffix error, for the literal common endpoint schedule followed by
its true uniform smoothing kernel. The suffix cost is the actual finite
metric-ball alphabet entropy. Neither theorem assumes a fresh-information or
geometric-margin conclusion.

`explicit_band_geometric_entropy` and
`explicit_band_common_geometric_entropy` strengthen these statements with
the quantitative stage threshold
`geometricGuardConstant(data,b,e,hArith,D)≤g²*bandScale(g,U,j)`.
They apply for varying g; the lattice constant is fixed before g and every
actual batch or walk. Each stage calls the proved explicit scalar construction,
then the genuine geometric iteration and smoothing cost inequality. The result
and remaining relative-size/capacity conditions are identical to the uniform
band statements above.

The remaining final-engine application must instantiate numerical relative
scale/capacity conditions using actual density-selected batches and accurate
window parameters. That arithmetic application is not claimed by this module.

Validation: Lean 4.34.1 and pinned mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
Logs: `logs/GenericGeometricBands-build.log`,
`logs/GenericGeometricBands-axioms.log`.
The explicit varying-grid additions also appear in
`logs/GenericGeometricExplicit-build.log`.
