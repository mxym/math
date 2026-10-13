# Uniform finite-dimensional lacunary weighted graph bound

## Exact statement

Fix a finite descending positive scale list ds with factor-two separation, nonnegative energies e(d)<=B, and epsilon>0. There is one natural M such that for every integer m>=M, every nonnegative real vector s on Fin m with sum(s_i^2)=1, and every family of fractional edge weights w_d on unordered pairs satisfying 0<=w_d<=1 and sum(w_d)<=exp((2-d)log m),

    2 sum_d sqrt(e(d)) exp((d/2-1)log m) sum_(i<j) w_d(i,j) s_i s_j
      <= sqrt(sum_d e(d)) + sqrt(2B) + epsilon.

The final theorem is `lacunary_weighted_graph_eventual`. The dimension threshold is uniform over ALL vectors and weight families. No supplied limiting measure, finite-support approximation, spectral ansatz, favorable edge arrangement, or graph-limit hypothesis occurs in this endpoint. The scale list and energies are fixed before the dimension threshold. This is the actual nonnegative Rayleigh/Schmidt form needed by the multiscale physical argument, not a claim of already completing the isolated spike or the APPT state construction.

## Finite localization and exact measure bridge

WeightedLocalization proves a low/middle/high estimate for fractional selections using their total weight budget. FiniteProbability constructs an actual probability measure from nonnegative trace-one finite weights; repeated coordinates and zero weights are allowed. FinitePairMass derives its exact product mass and proves the factor-two unordered-pair bound, retaining the nonnegative diagonal contribution.

The common coordinates are max(0,1+2 log(s_i)/log(m)), with weights s_i^2. Zero s_i use the total real logarithm but have exactly zero measure weight; no positive logarithm identity is applied at zero. LogScaleCoordinates proves that nonnegligible coordinates with a middle-size product fall in |x+y-d|<=4 eta. PairLocalization handles the remaining pairs using their actual exceptional probability mass, not a cardinality approximation. SchmidtEmpirical bounds that mass by exp(-eta log m).

For one normalized layer, SchmidtLocalization proves the exact bound

    exp((d/2-1)L) sum_(i<j) w(i,j) s_i s_j
      <= 2 exp(-eta L) + sqrt(exp(-eta L))
         + sqrt((mu x mu){|x+y-d|<=4 eta}/2),

where L=log m and mu is the SAME explicitly defined empirical probability for every d. The rank budget is exp((2-d)L). Weighted square-root normalization and both tails are proved algebraically. The prior common-measure compactness theorem controls all middle bands simultaneously. The error tends to zero independently of vector and edge choices, yielding the final quantified bound.

## Controls and scope

A weight four with budget four violates the Cauchy bound when the essential cap w<=1 is removed. A real atomic probability with coincident coordinates and a zero weight has full expected product mass; this guards against treating coordinate multiplicity as distinct atoms. Earlier nonlacunary-triangle and missing-loop controls remain.

The mathematical modules passed isolated compiler diagnostics before committing. Those diagnostics are NOT certification. Complete fresh build, original module paths, trust-zero replay, exact-type corruption tests and independent source binding are required and recorded separately by tested commit. The separate compiler workflow does not weaken the proof workflow or appear in this mathematical target.

Remaining: the isolated-spike estimate, actual finite-dimensional APPT lower states with the matching centered-purity limit, the final coefficient-eight lower theorem, entropy extrema and dimension-varying rigidity. No preprint, immutable Release or original quantum definition is modified.
