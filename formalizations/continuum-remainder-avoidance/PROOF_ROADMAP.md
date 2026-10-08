# Proof roadmap

This guide follows the preserved Lean source, from the exact family-first statement to the unconditional periodic theorem and compact corollary. It explains the mathematical obligations discharged by each layer. The detailed independent, line-referenced review is [SEMANTIC_REVIEW.md](audit/independent/SEMANTIC_REVIEW.md); machine-verification scope is in [VERIFICATION.md](VERIFICATION.md).

## 1. Read the endpoint before the construction

[Specification.lean](project/ContinuumRemainder/Specification.lean) defines the target without asserting any existence result. [FinalProof.lean](project/ContinuumRemainder/FinalProof.lean) proves `robustCompactBlockerSpec_proved`, uses it to obtain `continuum_power_target`, and derives `compact_power_avoidance`.

The useful intermediate task is a **robust compact-parameter blocker**. Fix one configuration `A`, a compact exponent interval `[s₀,s₁]` with `0<s₀<s₁`, a positive lower remainder rate `α₀`, an integer coefficient scale `k`, natural error/tail bounds `q,h`, and a small positive budget `p`. Construct one open, one-periodic set `H` of unit density at most `6p` such that every real center `x`, every `s∈[s₀,s₁]`, every normalized coefficient `t∈[1,2]`, and every error function satisfying the bound have a positive input `a∈A` below `2^(-h)` with

`x + t*2^k*a^s + e(a) ∈ H`.

The error bound is `|e(a)| ≤ q*a^(s+α₀)` on the designated tail. The construction below proves this blocker specification. It is an intermediate theorem, not an extra assumption in the final endpoint.

## 2. Select actual points and count strict activations

[Sampling.lean](project/ContinuumRemainder/Sampling.lean) starts with bounded gaps among occupied dyadic bins. It chooses actual positive points of `A` in any specified tail. Their logarithms `z=-log₂(a)` increase to infinity with controlled upper gaps and sufficient lower separation, and the sampled inputs tend to zero. The source proves the exact power identity connecting these logarithms to `a^s`.

[Counting.lean](project/ContinuumRemainder/Counting.lean) counts points in windows whose **two activation endpoints are strict**. The count is uniform over each compact exponent interval. Finite potential labels include every pair active for any permitted real parameter, while their cardinality retains the absolute-position factor. Neither exact endpoint activity nor the cost of moving a window to a late absolute position is discarded.

## 3. Connect real-log geometry to exact finite routing

[LogGeometry.lean](project/ContinuumRemainder/LogGeometry.lean) obtains the actual output offsets, grid separation, and earlier-grid agreement at stable centers. [LogRouting.lean](project/ContinuumRemainder/LogRouting.lean) turns these facts into the own-address and terminal-address separation conditions used by the inherited routing model.

The inherited [RoutingModel.lean](project/ContinuumGeometric/RoutingModel.lean) and [RoutingSeparation.lean](project/ContinuumGeometric/RoutingSeparation.lean) use actual selector tables and terminal bits. Shared auxiliary reads are permitted; the argument establishes the precise separation it needs rather than assuming that whole paths are independent.

[LogSignatures.lean](project/ContinuumRemainder/LogSignatures.lean) reduces the continuum of compact real parameters to finitely many representatives of **exact activation and grid signatures**. The arrangement proof keeps negative, zero, and positive strata, so cuts, intersections, coincident cuts, and rectangle boundaries are represented. It uses the inherited chain through [LocalSignatures.lean](project/ContinuumGeometric/LocalSignatures.lean), [GridCutBridge.lean](project/ContinuumGeometric/GridCutBridge.lean), and [Planar.lean](project/ContinuumGeometric/Planar.lean).

This is not an approximate rational grid of exponents or centers. Signature equality preserves the actual miss event for every table assignment; representatives are selected before that universal quantifier.

## 4. Prove the finite probability bound

[LogRoutingProbability.lean](project/ContinuumRemainder/LogRoutingProbability.lean) applies the genuine finite joint law, whose all-miss factor is `(1-p/2)^m`. [SampleLocalProbability.lean](project/ContinuumRemainder/SampleLocalProbability.lean) inserts the actual active counts and representative bounds. [SampleStableProbability.lean](project/ContinuumRemainder/SampleStableProbability.lean) combines local misses, center-exposure atoms, and the no-default event to control the missed-center probability at every stable real center.

The inherited [FiniteRoutingProbability.lean](project/ContinuumGeometric/FiniteRoutingProbability.lean) first fixes selectors and averages the injective terminal reads, then averages free own selectors. Its normalized nonnegative weights are concrete finite product weights. No step divides by an atom's mass, so zero-mass atoms do not create a hidden positivity assumption.

## 5. Choose the schedule without circular dependencies

[SampleSchedule.lean](project/ContinuumRemainder/SampleSchedule.lean) chooses samples and structural routing parameters before selecting a sufficiently late output origin. It retains the absolute-position entropy factor and proves all output, gap, length, and grid guards consumed by the later arguments.

[ErrorSchedule.lean](project/ContinuumRemainder/ErrorSchedule.lean) makes the routing span sublinear in that origin. The actual double-buffer cost is `4*N*r`, with `N=2^(U+T+2)` and a strictly positive error radius `r`. The positive lower remainder rate makes this cost tend to zero while the entropy and exceptional-density requirements are satisfied at the same late position.

[ErrorDomination.lean](project/ContinuumRemainder/ErrorDomination.lean) proves that the allowed nonlinear remainder fits the chosen radius at active points. The proof keeps the upper exponent bound and the nonnegative shifted-origin guard; replacing this by an informal “take the error small enough” would omit essential work.

## 6. Absorb closed error bounds and repair every center

[RobustRepair.lean](project/ContinuumRemainder/RobustRepair.lean) defines the true set of missed centers using compact real parameters and finite active tests. The inherited [ClosedProjection.lean](project/ContinuumGeometric/ClosedProjection.lean) makes this projection closed. Compactness concerns the parameter factor; centers themselves need not lie in a finite grid or compact search set.

Two open buffers absorb the **closed** inequality `|e|≤r`: a strict inner distance plus a weak error bound gives a strict outer distance. Equality at the error bound is included, as [ZeroErrorBuffer.lean](project/ContinuumGeometric/ZeroErrorBuffer.lean) verifies.

[RobustAssembly.lean](project/ContinuumRemainder/RobustAssembly.lean) integrates the finite-law estimates and selects one actual outcome. The expected outer density is at most `2p` and the missed-center density at most `3p`. [PeriodicRepair.lean](project/ContinuumGeometric/PeriodicRepair.lean) covers the closed exceptional set by an open periodic set with sufficiently small excess. The resulting blocker has density strictly less than `6p`, implying the specification's weak bound.

At a center outside the exceptional set, one finite active input hits a buffer. At an exceptional center, the **full infinite perturbed sampled sequence** tends to that center and eventually enters its open cover. Repair does not confuse the finite routing candidates with the infinite sequence. This closes every-center coverage for every admissible error function.

## 7. Exhaust only countable bounds, then introduce real parameters

[Exhaustion.lean](project/ContinuumRemainder/Exhaustion.lean) indexes blockers by `(l,N,j,k,q,h)`: family member, compact exponent/rate bounds, coefficient scale, error magnitude, and tail bound. A strict summable budget chooses all blockers and their reflected copies before the eventual target function or real parameters are introduced.

For any `s>0` and `α>0`, choose a compact range `[1/N,N]` containing `s` and `1/j≤α`. Choose `q≥M` and a sufficiently small tail below both the requested radius and the bound-validity radius. Since inputs there are below 1, `a^(s+α)≤a^(s+1/j)` has the required direction. Exact dyadic coefficient normalization treats `c>0`; reflection treats `c<0` while preserving period and measure.

Thus only a countable collection of bounds is enumerated. Real exponents, translations, arbitrary functions, and error families remain universal inside each blocker and after the common set is chosen. This is where the family-first quantifier order is preserved.

## 8. Obtain distinct outputs, topology, and strict density

The exhaustion first gives a miss in every positive input tail. [DistinctMisses.lean](project/ContinuumRemainder/DistinctMisses.lean) separately proves, on a sufficiently small tail,

`0 < (|c|/2)*a^s ≤ |f(a)-y| ≤ (3|c|/2)*a^s`.

Consequently there are noncentral missed values arbitrarily close to `y` inside each requested tail. Their set is infinite. This step uses `c≠0`, `s>0`, and `α>0`; repeated inputs or repeated output values alone would not suffice. The same module supplies the partial-domain extension lemmas, combined explicitly in the independent [SemanticProbe.lean](audit/checks/SemanticProbe.lean).

[TopologyConclusion.lean](project/ContinuumRemainder/TopologyConclusion.lean) takes the closed complement `E` of the common small open periodic union. An affine zero-error instance from one family member proves empty interior. A strict measure budget gives density greater than `1-ε`, and periodic interval splitting with null endpoint corrections transfers it to every real translate `[x,x+1]`.

Finally `K=E∩[0,1]` is compact, nowhere dense, and has the required strict measure. Shrinking the avoided set preserves all misses. [FinalProof.lean](project/ContinuumRemainder/FinalProof.lean) ties the construction together with no remaining blocker, schedule, or probability premise.

## What this route does not prove

The construction is an existence argument using classical choice and very large finite objects. It supplies neither a practical numerical realization of `E` nor one set valid for all possible configuration families. The exact hypotheses and exclusions are in [THEOREM.md](THEOREM.md). Boundary tests and kernel replay strengthen confidence in the stated theorem; they do not extend its quantifiers or regularity class.
