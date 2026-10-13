# Canonical lacunary sparse-matrix localization

For a fixed finite positive lacunary scale list ds and fixed nonnegative energies e_d<=B, the new theorem `lacunary_sparse_matrix_bound` proves that one dimension threshold works for every larger m and every symmetric fractional family 0<=w_d(i,j)<=1 with total ordered weight at most 2*m^(2-d). The actual matrix A_ij=sum_d sqrt(e_d)*m^(d/2-1)*w_d(i,j) satisfies C*I-A>=0 and ||Ax||_2^2<=C^2||x||_2^2 for every real vector, C=sqrt(sum e_d)+sqrt(2B)+epsilon.

This is the canonical-power version. It does not assert an arbitrary varying number of levels or silently replace integer rounding/asymptotic coefficients by their limits. Simple graph adjacency matrices are a subclass, but fractional weights are included to support the later physical compression argument.

## Proof dependencies

WeightedLocalization proves exact fractional Cauchy and low/middle/high splitting. FiniteScaleMeasure constructs the actual atomic probability and verifies its product and measurable pushforward even when locations coincide. PairLocalization retains both endpoints of discarded pairs. LogAmplitude proves the logarithmic scale bound, clipping into [0,1], and exponentially small lost mass, including zero amplitudes. SparseScaleAlgebra cancels the exact exponential powers. SparseLocalization instantiates every band and mass hypothesis using the original vector, not an independently chosen measure. SparseGraphLimit uses one common measure for all levels and the already verified uniform compactness threshold. NonnegativeRayleigh handles homogeneity and zero vectors. SparseMatrixBound proves the actual PSD and Euclidean operator-square conclusion.

For L=log m and clipping width eta, one level has error at most 3*sqrt(e)*exp(-eta*L)+sqrt(4*e*exp(-eta*L)). This vanishes uniformly over all allowed vectors and weights. The nonzero error terms are not discarded before taking the dimension limit.

## Verification

Independent run 38349046520, exact source 3ae4c51210c7bf9fecfd726502954cd534929585, passed all stages: 3134 build tasks; 50610 declarations and 365 explicit roots replayed in an empty kernel at trust zero. All 131 source inputs matched the tested commit and downloaded artifact. There are 24 exact-type proof-corruption controls; the primary target is the full sparse-matrix theorem. The only axioms are propext, Classical.choice and Quot.sound. Evidence: verification/ci-3ae4c512/. Local fresh build and replay also passed; prior records retain their source bindings.

Mathematical controls reject omitting the weight cap, deleting small nonzero products, halving the lost-pair error, using an insufficient clipping width, and inferring an operator norm bound from a nonsymmetric Rayleigh bound. Standalone elaboration errors were repaired before the full audits; neither build failures nor timeouts count as successful proof checks.

## Remaining scope

At this checkpoint the single-spike decoupling and projection-rank quantum bridge are not included in the verified closure. The coefficient-eight APPT construction, its matching purity lower limit, full entropy laws and dimension-varying rigidity remain separate. No release, preprint or original quantum definition is changed.
