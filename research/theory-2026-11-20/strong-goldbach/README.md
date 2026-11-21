# Strong Goldbach: central operator and proof audit

The target is the unconditional assertion that every even integer at least four is a sum of two primes. **The conjecture is not proved or refuted here.**

- [Mean-square central kernel and exact finite-wheel variance](CentralMeanSquare.md): a density-one operator bound for the actual primes, by established linear forms asymptotics. It does not give the signed uniform estimate for every even target.
- [Two specific tests of arXiv:2611.09007v1](AntidiagonalAudit.md): the asserted transition equality fails on an infinite progression, and the universal growth assertion omits an unbounded local factor. These facts test that paper's argument, not the conjecture. Run `python3 -O check.py` for the elementary finite arithmetic.

[Li–Liu's distinct November conditional proof](https://mrc.sdu.edu.cn/english/info/1018/1514.htm) assumes Dirichlet GRH and an additional spectral hypothesis. The operator note isolates what averaging can establish without either assumption; it is not an assertion that their uniform hypotheses follow.

## Pointwise progress on the divisor-switch route

- [Sharp shifted-squarefree margin](SharpPointwiseSquarefreeMargin.md): an unconditional pointwise worst-case constant for the number of primes whose complement is non-squarefree. This does not count two primes.
- [Centered divisor switch](CenteredDivisorSwitch.md): an unconditional `O(N/B)` discarded arithmetic tail and corrected moving endpoint. The improvement of the logarithmic modulus buffer is at the same scale, not a weaker all-scales ordinary Elliott–Halberstam conjecture.
- [Annihilating moduli](AnnihilatingModuli.md): the original all-modulus Möbius-twisted hypothesis forces its own total to be small; conditional Hardy–Littlewood asymptotics follow. A smaller sufficient hypothesis tests only the squarefree twisted moduli and required endpoints, but is still unproved.

Run `python3 -O check_switch.py` for the finite exact identity checks. The checks are not evidence of the missing analytic distribution estimate.

## A signed estimate in the balanced block

- [Balanced factor-count bounds](BalancedTwistFactorCounts.md) localize the large absolute contributions for each even target.
- [Signed balanced transition](SignedBalancedTransition.md) saves a power of log on the full balanced block for actual primes, including the middle factor counts. As a scoped conditional consequence, ordinary Bombieri–Vinogradov plus a **still-unproved Möbius-twisted** distribution bound slightly below the square-root level would yield individual Goldbach asymptotics. The unconditional result does not estimate the smaller twisted moduli or prove Goldbach.
- [Smoothed signed transition](SmoothSignedTransition.md) extends that range to a fixed exponent `δ<1/9` in the scale `sqrt(N) exp(−(log N)^δ)` for the still-unproved twisted input. No smaller-modulus pointwise theorem is claimed.
- [Unweighted interior Möbius primitive](InteriorMobiusPrimitive.md) gives a pointwise-in-target `L^1` saving on a single interval throughout polynomially interior divisors. It cannot simply be integrated over a full logarithmic width to bound the weighted switch.

The [moving endpoint correction](https://doi.org/10.5281/zenodo.21939906) in the earlier Huang–Li argument was already documented by Ramón Moya in August 2026; the centered tail and signed bounds here are separate.

## Global localization to rough complements

[An unconditional pointwise theorem](GlobalRoughLocalization.md) controls the full log-weighted divisor switch on every squarefree complement with a prime factor at most `exp((log N)^δ)`, for fixed `0<δ<1/9`. After the small-divisor term is evaluated by ordinary Bombieri–Vinogradov, the only remaining signed term is supported on complements without such a factor. That support is sparse, but the weighted signed remainder has not been bounded at the required scale; strong Goldbach is still open.

[Iterating disjoint rough layers](RoughLayerIteration.md) extends the cutoff and the smooth signed block to every fixed stretch exponent below one, not to a fixed power of N. [Centering each complement at its own square root](SymmetricParityReduction.md) eliminates all odd-factor squarefree composites exactly, preserves the ordinary-prime small-side main term, and isolates even rough complements. Rough semiprimes have a negative kernel, and four-factor complements have a nonnegative kernel. The remaining weighted sum is unbounded at the needed scale here; this is not a proof of strong Goldbach.

[Fixed-power stopping sieve](FixedPowerStoppingSieve.md): for sufficiently small fixed τ, the relative discarded error is bounded by an absolute constant times τ^η, leaving even-parity complements with every prime factor greater than `N^τ`. The analogous whole balanced block bound makes an **unproved twisted** hypothesis at some fixed power strictly below the square-root level conditionally sufficient for eventual positivity. No unconditional lower bound for all even targets and no conditional full asymptotic at a fixed τ is asserted.

[Largest-factor sign restriction](OneSidedLargestFactor.md): a higher even-factor complement can have negative kernel only if at least three smaller prime factors are below the square-root cutoff divided by the largest factor. Three such factors admit an exact sign test. The semiprime terms with smaller prime at most `N^τ` contribute at most `O(τ)` of the main scale. None of these statements bounds the entire negative remainder.

[Exponential tail in the number of prime factors](ExponentialEvenTail.md): in the normalized limsup over even targets, the absolute weighted kernel mass from complements with at least `M` prime factors is `O(exp(−0.0154M))`. This is not an effective small numerical cutoff, and still leaves the signed contributions at low even factor counts.

[Explicit bound for exactly six prime factors](SixPrimeNegativeSector.md): the total negative contribution of these complements alone is less than `0.608 NS(N)` in the normalized limsup. A positive upper-bound sieve transfers a nonnegative geometric integral to the actual reflected primes; it does not transfer the signed simplex average. Run `python3 -O check_six.py` for the exact rational enclosure of the constant. The semiprime and other even-factor terms are not jointly controlled, so strong Goldbach remains open.

[Cutoff rigidity](CutoffRigidity.md): for continuous normalized cutoffs at or below the square root, making the semiprime charge smaller necessarily creates positive three-factor charges. Those charges have nonzero reflected-prime mass on average. The total signed geometric reference integral is exactly `−1/2`; this integral is not a uniform estimate for actual prime correlations.

[Quadratic cutoff and two-weight criterion](QuadraticLowDegreeReduction.md): all even-factor terms beyond semiprimes cancel, and the five-factor term has the favorable sign. The actual remaining positive high-factor tail is less than `0.13132 NS(N)` in the normalized limsup. This leaves a single combined upper bound on two explicit weights for two- and three-factor complements. Proving that bound at 1.11 times its geometric reference would suffice for eventual Goldbach; that input is **unproved**. The exact reference constants replay with `python3 -O check_quadratic.py`.

[Upper comparison and what standard switching proves](QuadraticUpperAndSwitchingScope.md): the same normalized combined statistic lies between `0.86868` and `1.266` asymptotically, unconditionally. The latter is not a small enough upper bound for the low-factor sum to prove positivity. The note states the needed uniformity and factor size in the primary switching lemma.

[Arithmetic parity witness for the two-weight criterion](ArithmeticTwoWeightParityWitness.md): an explicit integer weight satisfies Goldbach's ordinary divisor data through every fixed power below one, plus ordinary reduced-class progression data through every fixed power below one-half. It still has no weight on prime complements, and its two-factor statistic tends to the full main term. This specializes the classical parity obstruction to the quadratic criterion. It is not a model of all prime-specific bilinear estimates and is not a counterexample to Goldbach.

[Exceptional-zero effects on the genuine low-factor weights](ExceptionalZeroTwoWeightTransfer.md): conditional smoothed means on multiples of a hypothetical exceptional conductor and on proper-divisor strata. Arbitrarily close odd exceptional zeros, and even ones with a conductor divisible by 3 or 4, would force the two-factor weight alone to reach at least the full main term along some targets. No such zero is asserted to exist; no pointwise asymptotic or Goldbach counterexample follows.

[Fixed-target sparse Type II estimates](FixedTargetSparseTypeII.md): the exact determinant shift is proportional to the growing Goldbach target, not logarithmically small as in the cited predecessor-prime argument. Sparse harmonic centering nevertheless gives unconditional cancellation at the correct support scale with up to three genuine prime slots and a remaining rough proxy. A second long prime residual or arbitrary marked residual is not covered. The note also identifies the exact residue stratum left open by the known pointwise exceptional-zero theorem.

[Prime-only spectral threshold and asymmetric probes](MinimalPositivitySpectralInput.md): an exact positive-cone gap measures existence of even one pair, with a threshold from a deterministic continuous model. The equivalent criterion supplies no independent bound for that gap. A wider nonsymmetric compression has a larger attainable model threshold, but its actual arithmetic norm is not bounded here. The original full Li–Liu hypotheses also imply unrelated pointwise prime-difference asymptotics, explaining why the whole-operator conditions are stronger than needed for positivity.

[Optimal periodic removal of proper prime powers](OptimalDensePrimePowerWheel.md): the least possible order of `log W` for a nonempty unit mask excluding all actual proper prime powers up to `N` is `sqrt(log N)`. At this optimal order an even squarefree-wheel mask loses an arbitrarily small fraction of locally admissible Goldbach pairs, and a signed lower filter uses only `O(sqrt(log N)/loglog N)` total Fourier cost. These are local and exact identities, not prime-pair positivity. Run `python3 -O check_dense_wheel.py` for the dense-block finite controls. The [simpler one-test wheel](OptimalPrimePowerWheel.md) is also retained.

[Central-window obstruction](CentralWindowWheelObstruction.md): the same square-root logarithmic modulus lower bound holds even if the mask is required to eliminate powers only in one entire central interval of length at least `N exp(−D sqrt(log N))` for fixed `D`. This uses effective short-interval prime distribution in reduced residue classes, and does not restrict nonperiodic subtraction or sparse probe nodes.

[Sharp size–retention tradeoff](DenseWheelPrecisionBarrier.md): to lose at most `exp(−(log N)^b)` of the local unit-pair mass for fixed `0<b<1`, the optimal order of `log W` increases to `sqrt((log N)^(1+b)/loglog N)`. The lower bound holds even for a filled central window and the matching upper removes all powers up to `N`. This does not estimate genuine prime pairs.

[Fixed-target signed mixed cancellation at the square root](BalancedSignedMixedCancellation.md): in a balanced variance with a structured Möbius weight, summing the rough variable in a fixed column gives arbitrary logarithmic saving for prime–rough and rough–rough terms without averaging over the target. The signed variance is thereby reduced to the actual two-prime variance. The off-diagonal two-prime term is not controlled, nor are absolute errors for each individual pair of rows.

[Exactly one isolated even failure in an additive model](IsolatedAdditiveException.md): a wheel-sampled finite set prescribes one missing even target while representing every other even target in range and matching the Hardy–Littlewood weighted main term at every other power-scale target. This is a limit on exception propagation from such additive data alone, not a result on the actual primes.

[A single one-sided prime-row test](SinglePrimeRoughRowCriterion.md): exact factor subtraction and ordinary Type I estimates leave a specific signed sum with a prime row below exponent 1/3. A fixed one-sided bound would imply eventual central binary Goldbach. The required bound is **open**; this is a conditional reduction, not an existence result for actual prime pairs.

[Flat-passband analytic route](FlatPassbandMajorArcs.md): a fixed-scale Fourier cutoff and Sobolev treatment give an unconditional moving-target mean-square estimate. A restricted zero condition gives a pointwise major-arc main term. An individual target's signed minor-arc term is still uncontrolled; this is not a new Goldbach or exceptional-set theorem.

[Unconditional bound on the high prime rows](HighPrimeRowBound.md): product-distribution and sieve estimates control all rows at or above x^(4/15) in the one-sign criterion. The precise remaining uniform low-row inequality would still need to be proved.

[What real-prime thinning preserves](GenuinePrimeThinning.md) and [a single hole in an algebraically rigid model](QuadraticRingOneHole.md): diagnostics for least-exception/additive or algebraic propagation. Neither is a result on the absence or presence of a binary representation in the complete set of primes.

[Two-smallest-factor cancellation in selected low rows](VariableLevelTwoSmallestRows.md), with [adaptive sieve ratios](AdaptiveTwoSmallestAddendum.md): ordinary progression estimates and endpoint cutoffs unconditionally remove an explicit moving region for each even target. The adaptive choice retains positive fixed-power reach even when the original small cutoff shrinks. Other low rows remain open; an explicit Liouville model shows why the same Type I comparisons and separate upper bounds do not suffice for the surviving sign.

[Centered divisor markers for the high rows](CenteredMarkerHighRows.md): a signed square-root cutoff removes every even factor count off thin walls, and ordinary progression estimates and explicit reference geometry bound the new high remainder beginning at least-factor exponent 31/200. The changed low signed sum is unproved; this does not establish eventual Goldbach.

[Zero-gap localization at an individual target](FixedTargetZeroGapLocalization.md): exact smaller-scale null tests give a spectral phase-window reduction under Dirichlet GRH, with the functional-equation partner diagonal computed unconditionally. The localized arithmetic sign remains unproved. [A separate major-arc stability limit](SignedMajorArcWitnessStability.md) shows why polynomially bounded signed frequency multipliers satisfying the off-target sign constraints cannot simply discard the minor arcs.

[Continuous real-gap filter and its limitation](ContinuousRealGapDetector.md): under Dirichlet GRH, a signed zero-gap asymptotic holds in one nonperiodic shrinking window. The filter suppresses the arithmetic signal on every target, so that asymptotic cannot distinguish represented even integers from possible exceptions. The sharp width obstruction concerns uniform complementary leakage with bounded causal delay.

[Live real-gap filter](LiveRealGapDetector.md): adding a pole-null term produces nonvanishing prime-pair response in a slightly wider, shrinking real-gap window under Dirichlet GRH. A signed whole-family truncation restricts the remaining nonprincipal statistic to near-full conductors. A strictly positive bound at every even target remains unproved.

[Fixed-target logarithmic edge cancellation](LogConservationEdgeMarker.md), with [long-marker counts](CenteredMarkerLongOverlap.md): a new Type I logarithmic weight cancels an entire thin long-factor slice to \(o(M_N)\) despite a larger absolute mass. This replaces the observable globally, not just on the edge, and can add positive contributions elsewhere. The broad low residual remains open.

[Integral rigidity after deleting primes](RobustPrimeRigidity.md): the universal integral binary relation group and its late-prefix stabilization survive every sufficiently small relative-density deletion. A dense subset can therefore retain exactly this rigidity while missing an entire progression of even sums. This limits a structural proof strategy; it is not a counterexample for all primes.

[Odd-family zero-gap sign and its limitations](OddZeroVarianceAndSignBarrier.md): in the live filtered window the exact arithmetic diagonal leaves a single odd-character average. Termwise sign locking cannot make that average strictly negative with this delay budget, and a concrete family violates a naive sub-Poisson bound at the raw, unfiltered phase. The actual filtered estimate is open; the odd-character projection itself precedes this note.

[Polynomial log markers](PolynomialLogConservationMarker.md) suppress all squarefree smooth low terms and keep the thin-edge cancellation, but introduce positive mixed terms elsewhere. [One explicit mixed carrier](MixedCarrierTypeISeparation.md) has a level of distribution reaching exponent 0.573 by Jain’s threefold estimate, leaving a signed Type II remainder for this unweighted carrier. Neither its sign nor the full low-residual bound is established.

[One-prime stabilization of equal-weight fibers](OnePrimeCatalyst.md): any two fixed equal-degree, equal-weight prime multisets can be connected by actual binary moves after adding one shared prime from a relative-density-one family. An averaged row of Nelson’s cubic conjecture also holds without an extra variable once its fixed starting successor is represented. This does not cancel the shared variable or prove all prime successors are represented.

[A marked Möbius–prime major-arc estimate](MacroShiftBurgessMajorArcs.md) unconditionally controls the normalized major part of one actual covariance for a fixed growing Goldbach target. It combines Burgess on a long free variable with a high moment of a prime marker. [The target-index lattice count](MacroShiftRootLattices.md) does not control the remaining weighted minor arcs, so even the full signed sub-block remains open.

[Pointwise giant components of ternary prime fibers](CubicGiant.md): for every sufficiently large odd weight, central primes in each allowable mod-3 sector have one giant under actual binary moves, with a super-logarithmically small exceptional set of labels. At weight N+3 with 6 dividing N, a cross-sector bridge still requires a genuine pair summing to N; no existence of such a bridge is claimed.

[Generic one-variable localization](GenericOneVariableLocalization.md): for a density-one set of individual primes t, inverting just x_t in the full ring makes every prime variable a unit. For those t, regularity of x_t is equivalent to the full fiber-connectivity problem; the theorem does not prove regularity or the existence of missing binary weights.

[Far-angle Poisson descent](FarAnglePoissonDescent.md): the physical covariance on a comparable-label sub-block has negligible large-gcd tails and a negligible signed zero frequency, with both prime factors retained. The reciprocal frequencies collectively remain open, so this does not prove the signed sub-block estimate.

[Square-zero cubic and the fixed variable x₃](SquareZeroBridge.md): a missing sufficiently large multiple of six would yield a nonzero square-zero difference of two actual prime triples, annihilated by x₃. Reducedness or a specific injectivity statement would rule it out, but neither is proved for the full prime ring. Deleting just 7 gives an exact nonreduced example for a different prime set.

[Cancellation for the long free factor](HeathBrownLongFreeNotch.md): in the actual far-angle covariance, a rigorously identified Heath–Brown component with complementary product at most x^0.01 cancels whenever it appears on at least one side. The two-sided remainder with no such free factor remains unbounded at the required scale.

[Finite-prefix cubic socle criterion](CubicPrefixSocle.md): for the complete prime prefix through s=N+3, every prime variable annihilates the difference of the two central cubic classes via explicit pointwise paths. A missing large multiple of six would force a nonzero cubic socle and depth zero at that prefix. No lower depth bound is proved.

[Actual depth-zero prime prefix at cutoff 317](PrimePrefix317.md): 65 certified annihilators give a nonzero cubic socle at weight 615. This weight exceeds the cutoff, so the example does not refute the Goldbach-relevant weight-window criterion or say that the full ring is nonreduced.

[Power-sparse exceptional prime anchors](PowerSparseLocalization.md): an unconditional Oε(X^(7/12+ε)) bound on anchors that fail the single-variable localization test, using Pintz’s explicit formula for prime multiples and primes’ restriction estimate. This controls where nontoric prime components can be supported; it says nothing about regularity before localization.

[Seven-ring socle criterion for all even residue classes](NineProgressionSocle.md): use the full prime-prefix ring for multiples of six and six specified restricted-support rings for the other even targets. A missing large N would produce a cubic socle in the corresponding prefix, but no depth lower bound is proved and the restricted theorem does not apply to the full ring outside multiples of six.

[Low-window socle under density-one thinning](DenseThinningLowSocle.md): a single sparse deletion of genuine primes gives infinitely many prefixes with a socle cubic of weight exactly the cutoff. This rules out a proof based solely on density-robust input, not the low-weight statement for the full primes.

[Major and irrational shells of actual zeta zeros](ReflectedZetaMajorMinorShells.md): subunit interval reflection isolates a single integer; after a specified smooth spectral projection, the parity shell has an explicit sign and one badly approximable shell is small on zeta RH. The parity calculation uses nearby targets, and neither result controls the total fixed-target sign.

[Pointwise Goldbach in a small-conductor exceptional-zero regime](SmallConductorExceptionalGoldbach.md): if a real primitive character has a sufficiently close zero to 1 with the stated small conductor, this proves actual central prime pairs in the local stratum where the usual exceptional-zero main term vanishes. The assumption is conditional and the no-exception regime remains open.

[Flat-topped ζ-zero major shells](FlatTopZetaSingularSeries.md): under Dirichlet GRH, disjoint real total-ordinate windows recover the full expected singular-series main, including all rational residue classes in the stated range. The complementary signed ζ-zero aggregate at the fixed target remains open and can cancel this main.

[Polynomial-conductor extension of the exceptional-zero criterion](PolynomialConductorExceptionalGoldbach.md): under the existence of a real quadratic zero with conductor at most N^κ and (1−β)log N≤(log N)^−A, the hard local case has positive actual central prime-pair count; combining it with Matomäki–Merikoski covers the other local cases. κ>0 is sufficiently small depending on A. No such zero is asserted to exist, and this does not cover ordinary targets without the stated zero.

[Cardinal localization to one compact positive ζ band](CardinalPositiveZetaBand.md): an exact sampling identity restores the individual even target, not nearby-target averages, and confines its double-zero test to two positive ordinates of size comparable to N (zeta RH). Under Dirichlet GRH the rational cores yield the singular-series main; the signed complement in that same compact band remains uncontrolled.

[Unconditional cardinal-band version](UnconditionalCardinalZetaBand.md): the compact fixed-target expansion holds with actual real parts of zeta zeros, without any Riemann hypothesis. A logarithmic-denominator rational aggregate is strictly positive and approximates the singular series to any fixed relative tolerance. The signed minor aggregate remains open.

[Finite arity for the prime toric ideal](ToricMarkovArity.md): weak Goldbach gives an arity-four generating bound, and a five-linear-form prime gadget replaces all sufficiently heavy quartic moves by three ternary moves. This leaves the cubic family and finitely many small quartics to test for actual quadratic connectedness. [Finite reproducibility checks](check_markov_arity.py) do not establish an effective asymptotic threshold.

[Prescribed residues in the exceptional-zero windows](ExceptionalGoldbachPrescribedResidues.md): a central mixed or majority–majority prime pair can be required to lie in a single admissible residue with the stated signs. In the majority–majority case a tilted positive divisor proxy uses the real zero to cancel one hyperbola half. This is conditional; the ordinary no-exception case and the prescribed minority–minority case are not proved.

[Adaptive major shells with the full singular-series main](AdaptiveZetaSingularSeries.md): the unconditional compact zeta band has an exact absolute o(X) major-shell error with growing subpower denominators after omitting multiples of at most one exceptional conductor. The possible omitted exceptional shells are not bounded; the signed minor aggregate is open.

[Fixed-target minor packet delocalization](MinorPacketDelocalization.md): the genuine zeta packets admit an absolute summed transfer error o(X) on the complete X^0.3 mesh. At each individual target, all small-rational skirts and the absolute sum of signed packets in any fixed log-power number of deep minor tiles are negligible. Any exceptional cancellation must be spread more widely; the full deep aggregate is uncontrolled.

[Low reduced reciprocal frequencies of the actual far-angle term](FarAngleLowReciprocalPrimeSlice.md): the fixed-target signed Poisson contribution has a power saving for reduced frequency at most x^0.029, or x^0.091 with a designated prime factor near x^0.19. Some high-gcd strata are thereby covered completely; the large nearly coprime frequencies remain open.

[Complete polynomial denominator blocks](CompletePolynomialDenominatorBlocks.md): squarefree and nonsquarefree denominators through X^(1/9−ε) with q/(q,N)≥X^δ have negligible total paired block contribution at each target, by complete numerator Gauss cancellation, a weighted conductor norm, and unconditional hybrid density. Only the complete block can be bounded in this manner. Divisor-locked blocks and the remaining large frequency region are open.

[Marked-carrier Type I seam](MarkedCarrierTypeISeam.md): regrouping the two actual independent suffix factors gives maximal distribution through x^0.586 and bounds the full marked pre-Cauchy signed .09 notch at each target. The Cauchy-enlarged covariance, the unmarked seam, and the remaining Type II terms are not covered.

[Higher signed modulus strips on the actual carrier](IndependentCarrierHighModulusStrips.md): conditional on the stated convolution preprint's Proposition 2 being correct, narrowed versions of the genuine mixed carrier have additional fixed-width signed Type I strips near x^0.598, x^0.613 and x^0.618. This uses no conjectural zero assumptions and does not reach intervening moduli continuously, the remaining Type II, or full Goldbach.

[One flexible carrier with contiguous weighted Type I to 5/8−η](FlexibleMarkedCarrierFiveEighths.md): a finite family of disjoint genuine tiny prime labels allows independent factor allocation in every modulus dyad. On this selected carrier the actual marker is exactly P(S)−P(E), giving the maximal signed Type I estimate through x^(5/8−η) if the cited Jain preprint proposition is correct. The above-threshold Type II, other cells, and strong Goldbach remain open.

[Exact full-target delta expansion with linear terms removed](ExactDeltaLinearRemoval.md): one smooth δ identity covers the whole individual target, without a Farey boundary approximation. The pole model gives the singular series and both families linear in the centered error are negligible by maximal Bombieri–Vinogradov. The signed sum of the quadratic centered terms is still open.

[All-height compact factorization components](EACCompactSmooth.md): the authors' complete rational S-unit tables exclude every compact ≤53 special component except two old examples at represented centers. A hypothetical missing N has no such compact component and satisfies the stated pair-radical and closure restrictions. [Replay](check_eac_sunits.py) checks the reduction against pinned source tables; it does not resolve large components or Goldbach.

[Adaptive largest-prime descent in the weighted Vaughan sum](WeightedVaughanLargestPrimeDescent.md): both subtractions and their cross term use the actual weighted Type I range. The remaining Möbius factor is genuinely smooth; with a small reserve the whole shifted integer can also be made squarefree. The residual bilinear correlation stays signed and unbounded at the necessary fixed-target scale.

[Three large conductors in the exact delta high sector](LargeConductorDeltaSectors.md): unconditional sparse-grid and finite target-phase estimates eliminate middle moduli, strongly divisor-locked top moduli, low input or product conductors, and thin pairings. The entire small sector and the dense top covariance remain; the shared target atom explains why simple across-block multiplicity by itself would not prove a sign.

[Cubic-log moving cutoff for closed reflected factors](EACMovingCutoff.md): every nontrivial coprime factor-closed set of genuine prime labels has a label at least of order (log N)^3/(log log N)^10. Shared-factor pair counting, the Brun–Titchmarsh theorem and a three-logarithm bound give the asymptotic estimate. [Integer controls](check_eac_marking.py) check the exact bookkeeping, not the imported asymptotic bounds. This does not exclude large components.

[Positive low-sector reserve in the exact polynomial delta cover](PositiveSmallDeltaReserve.md): for one of two scales the small-denominator quadratic sector plus the entire pole model has a positive quantitative reserve unless an exceptional real zero is sufficiently close for the published separate criterion. The low-sector estimate itself is unconditional with its stated Δ-dependent error. It leaves the dense high covariance, with no sign bound.

[Asymmetric Vaughan reduction to square-root smooth shifted integers](AsymmetricVaughanSmoothResidual.md): all primes, semiprimes, and shifted integers with a factor above the specified square-root cutoff vanish from the *actual* adaptive squarefree residual of one weighted carrier. An optional subpower rough mask lowers the cutoff further. Genuine balanced prime triples retain their nonzero signed coefficient; their discrepancy is not evaluated.

[Parallel-work check on Li–Liu's spectral hypothesis R](LiLiuRParallelCheck.md): Yilin Liu's November 21 preprint refutes the full uniform R norm under Dirichlet GRH on represented even targets, using tests at the edge rather than the center. This does not refute general S, the restricted central test, or the independent arithmetic delta route.
