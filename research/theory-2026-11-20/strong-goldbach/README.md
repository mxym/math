# Strong Goldbach: central operator and proof audit

**Scope correction for the exceptional-zero notes.** The 2026 uniform exclusion of Landau–Siegel zeros, in the form of [Banks's Theorem 1.1](https://arxiv.org/abs/2610.15483v1), makes the small- and polynomial-conductor hypotheses in the conditional notes below empty for sufficiently large targets. Those calculations are archived for their method, not counted as Goldbach coverage.

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

[One-sided control on a genuine balanced triple region](WeightedTripleMarkedSieve.md): on the actual selected carrier, the signed contribution from triples with every factor at most x^0.3685 is less than 0.984 of one matched prime-reference unit asymptotically. A dual covering calculation explains why this particular one-marker sieve formula cannot bound the full positive triple sector below one unit. The outer sector, other signed sectors, and higher ranks remain open.

[All-height three-label autonomous components with two small primes](EACThreeLabels.md): no such component has both smaller labels at most 53, regardless of its largest label. Explicit logarithmic heights, rational continued-fraction controls, a separately checked finite modular ledger, and a GMP terminal enumeration certify the branch.

[At most one label above 53](EACOneLarge.md): with no bound on that one label, the only exceptional autonomous components are still the known examples at represented centers 128 and 2200. The S-unit sweep and three-label argument are separate; this does not exclude a hypothetical center with larger components.

[Moving lower threshold for almost half the labels](EACMovingMedian.md): from every nontrivial factor-closed coprime prime set, at least (k−1)/(2+η) labels exceed (log N)^(3−δ) for fixed positive η,δ in range. This is a structural restriction only.

[Half the labels escape a stretched-exponential threshold at fixed size](EACLargeMajority.md): a component of fixed size k has at least ceil(k/2) labels above exp((log N)^σ) for σ<1/(k+1); a slower growing-size companion uses a power-log threshold. The odd boundary is excluded by genuine factorizations and a second logarithm bound. This is not a classification at unspecified finite heights or an exclusion of all components.

[Moving Vaughan cuts and low-rank signs](MovingVaughanRankSigns.md): both cuts depend on the actual shifted integer without leaving the verified prefix Type I range. The revised coefficient vanishes on primes/semiprimes and negative triples, is nonpositive on squarefree rank four, and still has both signs at rank five. Bounds for its signed arithmetic discrepancy and for all other low cells remain open.

[Stronger growth for four-label exceptional components](EACFourLabels.md): for the two smallest labels, log p·log q is at least of order (log N)^(1/3)/(1+loglog N). The exact chain identities and the known two-label case exclude the coincident slope obstruction. This permits two initially unconstrained labels, but proves neither an all-height finite classification nor nonexistence of four-label components.

[Signed cancellation on an actual unmarked semiprime block](UnmarkedSemiprimeSignedBlock.md): for true n=sq over the small-prime exponent band [.10,.14], the entire natural reciprocal range cancels in one selected reflected Vaughan component with d near x^0.46 and a genuine prime mark in d near x^0.16. Keeping the other label in the exact inverse ratio is essential. Other divisor structures and Vaughan terms leave the original semiprime discrepancy open.

[Balanced components with a fixed small alphabet](EACBalancedCores.md): if exactly half the labels are in a fixed alphabet, all sufficiently large components have matched small/large pairs and a single smooth linear parameter. For the cutoff 53, [the exact table replay](check_eac_balanced_patterns.py) leaves eight explicit h = 2 families, of sizes 16, 18, 20, or 22. Their simultaneous primality remains open; components with a majority of larger labels are not covered.

[Why finite modular covers cannot eliminate the eight balanced families](EACBalancedEscape.md): an exact multiplicative ray simultaneously escapes every prescribed finite set of trial divisors and all quotient-power tests. [The small integer replay](check_eac_balanced_escape.py) verifies the relevant valuation vectors. This does not prove simultaneous primality.

[Both exact Vaughan Type I terms over the actual semiprime cell](UnmarkedSemiprimeWholeTypeI.md): for true primes s and q, with s near x^α, .10 ≤ α ≤ .14, the entire dyad-adaptive divisor interval reaches the exponent 1/2 − α/4 − Δ without any factor marker (via the exact single residue coset for each frequency). The first term has its genuine reflected-prime Euler main, and the second is negligible when the product of its two cutoffs is in range. The remaining bilinear Vaughan term is untouched, so there is no full semiprime count or Goldbach proof. This exponent is for that direct quotient argument; [full-scale convolution BV](FullScaleConvolutionBV.md) gives the stronger threshold for the actual prime product.

[Primitive integral curves for three prime labels](EACThreePrimeCurves.md): when all three labels exceed a fixed power of the even center, only finitely many centers can have a repeated largest prime in a complement or a quadratic pure-prime row. The proof uses a primitive integral curve, a ramification degree bound on other components, and [two finite-field certificates](check_eac3_fcurve.py). No numerical cutoff, and the first-power/cubic-or-higher branch and subpolynomial labels remain.

[A complete supercritical shoulder of Pan's double-divisor remainder](PanSupercriticalShoulder.md): fixed-target signed Möbius cancellation for both divisors between the original sqrt(N)/log^20(N) cutoff and N^(17/33−ε), with no average over N. Exact Poisson, genuine zero cancellation and the published Bettin–Chandee trilinear estimate control the sector. The larger-divisor complement may still cancel the positive Goldbach main.

[All fixed exponent signatures for three-label components are finite](EACThreeSubpower.md): every unbounded sequence of genuine three-label components must have a subpolynomial smallest prime. The physical positive branch forces a rational and unique point at infinity, and degree and integrality eliminate the remaining first-power signatures. This does not exclude subpolynomial labels, give an explicit cutoff, or prove Goldbach.

[Dual completion and a genuine slice of the last Vaughan term](UnmarkedSemiprimeDualWeilTypeII.md): completing a reciprocal sum and averaging the exact gcd losses raises the unmarked bound to (4−5α)/7−Δ on the true s,q cell, with a positive-width piece of the last Vaughan term beyond the previous cutoff. A largest-prime identity removes another nonpositive class for upper bounds. The remaining balanced, larger-product sector still has unknown sign. This is the dual-completion bound, not the limit for this prime-product input; see [full-scale convolution BV](FullScaleConvolutionBV.md).

[Long-divisor, short-cofactor sectors of Pan's remainder](PanUnbalancedCofactor.md): an explicit macroscopic-residue adaptation of Fouvry–Radziwiłł controls disjoint sectors in both orientations, such as divisor lengths N^.995 and N^.505 at fixed even N. A divisor-of-target exception is removed before dispersion. The remainder with larger moduli and bounded cofactors is not controlled.

[An exact limitation of positive-only bounds on the actual Vaughan residual](UnmarkedVaughanPositiveRankThree.md): balanced reflected triple products contribute on average more than .0335 of the reference mass after taking the positive part, so a uniform .010 allowance cannot be proved by discarding every negative term. This gives no lower bound on the signed residual.

[Smooth-cutoff localization of the actual Vaughan remainder](SmoothedActualVaughanRough.md): exact Möbius toggles remove reflected integers with many distinct small factors after averaging two already-valid cutoffs. An upper sieve retaining the genuine quotient prime bounds the rare remaining support in absolute value by x(log x)^(-1+o(1)), but the required strict signed bound remains open.

[All-height restrictions on three-label exponents](EACThreeExponentGaps.md): when the largest prime occurs to the first power, the last complement must be a pure power, the small base satisfies q > p^e, and b ≥ ed+1. Repeated-largest configurations obey two coprimality restrictions on the exponents. Neither surviving branch is excluded.

[Repeated-largest components with one bounded label](EACRepeatedFixedLabel.md): logarithms show d = O(log p), and for each fixed upper bound on even one label there are only finitely many centers in the repeated-largest branch. This uses integral curves and restricted-denominator approximation, not an explicit center census.

[Reverse Möbius dispersion and a double-Vaughan region](ReverseVaughanDoubleResidual.md): opening the true quotient prime now cancels its two Type I terms against the entire high reflected remainder, plus a quotient divisor slice and the genuine double sector with product below x^(1−ε). The surviving product-above-cut sector is an actual coupled signed Möbius sum, not a proven Goldbach estimate.

[Only polynomially rough inputs and nonsmooth moduli survive some centered Pan columns](PanPolynomiallyRoughSurvivors.md): at fixed even N, an absolute centered estimate removes every input with a prime factor ≤N^κ in the stated supercritical columns, and smooth squarefree moduli are handled independently. The remaining intersection still contains prime inputs and has unknown sign.

[Balanced reciprocal seam in the actual double Vaughan residual](DoubleVaughanReciprocalSeam.md): exact two-sided signs, the true logarithmic normalization, and Bettin–Chandee control all factor-exponent pairs in [.49,.51]², including above the double product hyperbola. The much larger or imbalanced boxes and the full Goldbach sign remain unresolved.

[Twelve-factor central survivor in a near-critical Pan column](PanCentralTwelveFactors.md): Fouvry's genuinely uniform Corollary 1 bridges the tag-prime interval on the literal central domain, leaving at most 12 prime factors at exponent .501 and the indicated nonsmooth modulus mask. Larger columns, the exterior and the surviving sign are not controlled.

[Eventual coprimality of the two pure exponents](EACCoprimePurePowers.md): in the genuine first-power three-label branch, only finitely many centers have gcd(b,d)>1 even with all labels and exponents moving. Asymmetric Padé uses the actual prime-power numerator; a separate exact rounding argument handles the bounded-ratio regime. The coprime branch and strong Goldbach remain open.

[Triply well-factorable signed Pan columns](PanTripleFactorableColumns.md): transfer the true double-divisor input to genuinely triply well-factorable weights below the large-residue exponent 153/256. A whole-box capacity argument covers an actual cubic-prefix part of the squarefree signed modulus column. Failed-prefix and unrestricted surviving columns remain open.

[Unmasked Pan principal means](PanUnmaskedMeans.md): a uniform coprime Mertens calculation cancels the ordinary prime term for each individual modulus at the fixed cutoff. This turns previously controlled complete modulus subcolumns into raw signed estimates; it does not remove a mean after imposing a rough-input mask.

[Whole reverse-Vaughan modulus columns](WholeReverseColumns.md): reassemble the entire reflected high branch before taking product cuts. Classical prime distribution removes all reverse columns below the square-root scale with a fixed gap; Lichtman’s three independent modulus slots also remove a specified above-half profile of exponent .510 at every label scale. The other large columns and the full Goldbach sign remain unproved.

[Logarithmic separation in three-label graph components](EACLogarithmicSeparation.md): in the first-power case, the middle prime grows faster than every fixed power of the smallest along any unbounded sequence of smallest labels. An integer-series and bounded-order differentiation argument gives a quantitative lower bound for the middle label in both branches, but does not exclude all components.

[Factored whole reverse columns](FactoredWholeReverseColumns.md): unique factorization of the actual quotient divisor into a prime and its smaller cofactor opens entire selected reverse columns at exponents .545 and .550. The reflected short divisors now cross the reciprocal seam too; an exact rational checker verifies all relevant grouping exponents. This does not cover unrestricted columns or decide their signed sum.

[Signed leakage in the double-terminal Pan sector](PanTerminalSignedLeakage.md): when both largest prime factors exceed P^(1−δ), the actual weighted prime-pair term survives, with mixed negative loss O(δ) and positive leakage O(δ²) relative to the singular-series scale, up to vanishing errors. The complementary raw sector is instead asymptotic to the negative main term when δ tends to zero slowly enough. This is not a lower bound on the prime-pair term.

[An effective height bound for pure-power graph cycles](EACPureCycleHeight.md): for any number of labels, the pure exponents are pairwise coprime and log N is at most 100 times their product cubed times the number of labels. A formal origin and integer auxiliary polynomial give the bound. Every component lying in a band of label ratio strictly below three is pure; unrestricted mixed components remain open.

[Switched long-free reverse terms](SwitchedLongFreeReverseColumns.md): truly free factors longer than x^(1/2+δ) in either exact reciprocal Heath–Brown expansion allow the full reflected high branch to be reassembled at a new modulus below the square-root scale, even when the original modulus is near x. The resulting modified coefficients are supported on smooth integers. Their remaining correlation is unbounded here.

[Rough high-rank negative-mass bound](pan-rough-rank/Proof.md): in both orientations, a true prime against a composite with at least six prime factors, all exceeding P^(333/4000), costs less than 0.896 of the singular-series scale in the limit, counting only the actual negative terms. The bound uses prime BV and an exact rational integral enclosure. Low-rank adverse profiles, small-factor inputs and both-composite terms remain outside the estimate.

[The positive main term at the intersection of both long switches](DoubleSwitchedMain.md): each whole directional switch cancels against the opposite original coefficient, but applying both requires a nonzero correction equal to the original semiprime reference main. Balanced triple products can increase, so the smooth supports do not on their own improve the signed budget.

[Removing small least factors at fixed rank](PanFixedRankSmallFactors.md): a physical prime-versus-composite estimate removes the small-prime cutoff rank by rank. In particular the entire negative part with four prime factors on the composite side is negligible, even with repetitions. The dangerous rank-three and rank-five profiles and the absence of a uniform sum over ranks are stated explicitly.

[Effective height for exactly one mixed graph row](EACOneMixedProjector.md): every fixed pattern of exponents has a computable height bound. An integral pivot handles the coprime patterns; a rational expansion handles the last noncoprime family. Consequently the least label is subpower along any unbounded sequence of these components, with no cardinality bound. Components with several mixed rows are not excluded.

[Canonical smooth-quotient reverse slabs](CanonicalSmoothWholeReverseColumns.md): when the genuine Möbius quotient is smooth, sorted prime prefixes put the original modulus into usable slots for each Heath–Brown group. Two full exponent slabs qualify, not just chosen thin profiles. The nonsmooth remainder and sign are open.

[A positive-density obstruction to negative-only budgeting](PanNegativeMassObstruction.md): exact dyadic first means for the semiprime and balanced three-prime negative rows show that even one orientation of those two rough rows can exceed the whole singular-series main term on a positive proportion of targets. Discarding all positive terms therefore cannot prove the needed all-target signed bound.

[Full-scale convolution BV for the two-factor input](FullScaleConvolutionBV.md): the classical theorem applies at the product size, not the shorter quotient size. This covers the whole below-square-root reflected range, including against every genuine reverse-high column when the independent prime-label weight is Siegel–Walfisz. Together with prior whole reverse columns, both sub-square-root ranges can be removed. The large–large signed remainder stays open.

[A uniform-residue Type II shoulder for the real double row](UniformResidueDoubleShoulder.md): a subset of the genuine quotient variables supplies the Siegel–Walfisz factor for Maynard III at the actual modulus dℓ. This cancels selected literal reflected products beyond the square-root scale even when the reverse product has exponent above .70. Many balanced boxes still have no suitable group.

[A common prime shared by every mixed row](EACSharedMixedPivot.md): when a pure occurrence of the shared prime has a small shift, the effective height bound at fixed lower label exponent is independent of how many mixed rows there are. Bounded-depth integral projection gives the result; arbitrary mixed components need not satisfy the hypothesis.

[Global signed roughness transfer at a power cutoff](PanGlobalRoughTransfer.md): at each fixed short-divisor cutoff Q=P^v below the square root, both physical inputs can be restricted to polynomially rough integers with arbitrarily small signed loss, making the surviving ranks finite. This uses a genuine signed Dickman mean and does not apply at Pan’s near-square-root logarithmic cutoff. It retains the original prime-pair term without deciding positivity.

[Positive-branch jets for the historical component signatures](EACPositiveBranchJets.md): exact rational expansions and integer-polynomial certificates give explicit finite height bounds for all five known mixed signatures, even allowing their prime labels to vary. The sixth historical signature is already covered by Bożek’s two-label classification. This is not a classification of other component signatures.

[Singularity for a semiprime-only component](EACSemiprimeStar.md): the largest label sits in a star in the cofactor graph, giving a nonzero kernel vector of the exponent matrix even at arbitrary component size. A second graph component gives a necessary multiplicative relation, not an exclusion.

[A full centered large-quotient slice on a factored reflected shoulder](WholeUpperQuotientShoulder.md): after the genuine long-free switches, every allowed quotient factor pattern has a grouped factor in the required exponent band. This cancels all large centered quotients for a specified reflected two-prime factor profile, without assuming convenient factors of the original quotients. Unstructured reflected divisors and the remaining sign stay open.

[Exact all-height rigidity for the six historical weighted graph signatures](EACHistoricalSignatureRigidity.md): five certified analytic cutoffs lie below 10^8, and a separate exact finite check finds only the historical center for each mixed signature. Together with Bożek’s known two-label case, none of the six signatures can occur at a Goldbach counterexample. Other signatures, even on the same unweighted graph, remain possible.

[Opposite-sign half switch and rank-three suppression](ParityBalancedHalfSwitch.md): separate true long-slot centers allow opposite signs in the actual reflected coefficient. Every three-factor reflected term against the real prime quotient then has negligible total magnitude. The same change shifts the reference main with its actual sign, so it gives no extra slack in the required original inequality.

[Two disjoint largest-factor populations at every even target](RoughShiftedPrimeFactorTails.md): there are many genuine central primes whose squarefree polynomially rough complements have all factors below exponent .455, and separately many whose composite complement has a prime factor above exponent .60. A first-moment argument with disjoint upper sieves proves this uniformly in the target, but gives no sign or prime complement.

[Exclusion of low-multiplicity reciprocal components](EACReciprocalFive.md): reciprocal factor support is a tree. The largest vertex and its unique neighbor cannot both have complementary rows with at most five prime factors counted with multiplicity. The exclusion uses explicit reciprocal congruences and one small exact enumeration; nonreciprocal components remain open.

[Two effective height tests for mixed exponent matrices](EACMatrixHeightTests.md): an invertible matrix with sufficiently large weight denominator relative to the special-fiber determinant admits an integral projector. A separate short congruence test also applies when the fiber determinant vanishes. These are sufficient preprocessing tests, not a bound on every mixed component.

[No homogeneous multiplicities in reciprocal components](EACHomogeneousReciprocity.md): if the largest vertex has a complementary power of exponent a, the gcd of any two pure-row exponents is strictly below a/2. Reciprocal trees have at least two pure rows, ruling out equal multiplicities at every height even with unrestricted degrees.

[A positive signed sector at a subquarter cutoff](PanMarkedCompensation.md): two marked prime factors whose joint product crosses the short-divisor cutoff produce a negative conditional short-divisor mean, hence a positive raw prime–composite contribution at every large even target. Narrow rough profiles also give an actual unweighted subset. No estimate for the rest or transfer to the near-half cutoff is inferred.

[A strictly negative four-factor sector in the opened row](NegativeRankFourCompensation.md): true four-prime reflected factors and a rough composite quotient give an actual negative contribution of at least .012 times the original reference scale, uniformly at each large even target. The opened row is globally equivalent to the true-prime test, but this is not a subset of that prime row and the rest remains unbounded.

[A mutual semiprime edge forces an isolated large label](EACReciprocalEdgeEmission.md): even in a directed component, a mutual pair with semiprime row at its larger endpoint determines a distinct prime above the square root that participates in no mutual pair. If every row is semiprime, the number of mutual edges is at most two-fifths of the number of labels.

[A net negative section with two small quotient marks](TwoMarkNegativeCompensation.md): the exact reverse coefficient is positive on a true two-mark factorization. The entire polynomially rough reflected sector on this support contributes at most −.040 of the reference, accounting for its positive ranks as well. A smaller semiprime-only subset gives −.180 instead, not in addition. The rough-quotient rank-four sector is separate, and neither choice bounds the full complement.

[Both unsigned parts grow at a fixed sub-sixth cutoff](PanSharpCutoffTwoSigns.md): disjoint shells give genuine central prime–composite pairs with each sign of the exact short-divisor weight. Each part on its own is at least a log-log factor above the natural main scale. Therefore an absolute budget fails there; the signed cancellation and prime-pair atom remain open.

[Both unsigned parts grow below the quarter cutoff](PanQuarterTwoSigns.md): uniform signed rough-divisor mean estimates and bounded label multiplicity extend the log-log excess of each physical sign to any fixed cutoff exponent below .25. This extension proves aggregate masses, not individual coefficient bounds past the earlier deterministic range.

[Physical harmonic pairing below the quarter cutoff](PanQuarterHarmonicPairing.md): fixed, unit-weight singleton and two-prime label shapes match their harmonic densities and cancel to arbitrary logarithmic precision across any set of the chosen shells. Each side individually still has divergent signed mass. This weights the whole physical coefficient, but only on its positive bounded labelled mask at fixed subquarter cutoff.

[Signed divisor-cube compensation at the original Pan cutoff](PanCriticalDivisorCubeCompensation.md): on an explicit bounded mask of actual divisor terms, two fixed mark geometries support signed compensation at joint moduli (P^{.505}) through (P^{.5151}). Exact cube algebra, full triple well-factorability and Lichtman's moving-residue theorem give arbitrary-log cancellation on the combined mask, not on all divisors of the selected complements or on the full remainder.

[Physical roughness at the original Pan cutoff](PanCriticalPhysicalRoughness.md): uniformly over every subset of primes up to (log log P)^(5/2), discarding actual inputs where either summand has one of those factors changes the full asymmetric signed remainder by O(P/log(P)^(1/5)). This includes all divisors and the target-supported prime part; it leaves the signed mass on the surviving set open.

[Polynomial roughness for the whole both-composite sector](PanCriticalCompositePolynomialSieve.md): at the original cutoff the signed both-composite mass is retained to any fixed tolerance after imposing an appropriate positive-power rough cutoff on both summands. This uses genuine signed bilinear Poisson dispersion for the allocated sieve moduli and covers no true-prime row.

[Parity transfer of the original rough mixed row to a composite covariance](PanCriticalParityTransfer.md): a moving-half complementary-divisor identity and signed true-target dispersion evaluate the tagged side. The original whole mixed row, restricted to fixed-power rough points, is reduced to one centered all-composite covariance with at most 12 prime factors on its more restrictive side. Its sign and magnitude remain open; the true prime-pair term is not estimated.

[Residue profiles at the same Pan cutoff](PanCriticalPhysicalResidues.md): entirely signed class totals, summed in total variation, match the local uniform admissible density after subtracting actual prime pairs. The three-part full comparison is valid jointly over periods up to (log P)^.1, and the simpler short rows jointly to (log P)^4. Prime-pair counts in the individual classes remain unknown.

[Full square-part projection in the original mixed Pan row](PanCriticalSquarePartProjection.md): even jointly with the tiny-prime-subset filter, the signed row is concentrated in total variation on squarefree complements, with error O(P/log(P)^(1/8)). All square parts are treated, not merely a pointwise deletion of rare large repeated primes. Squarefree parity of the surviving complements remains uncontrolled.

[Equal reverse cuts and all positive small cores](WholePositiveSmallCore.md): the original true-prime test admits a globally equivalent reverse expansion in which any quotient with only one distinct small prime has zero coefficient, apart from paid powers. All positive cores up to exponent .14 have a uniform net negative bound against the full macro-rough reflected side; this by itself does not bound the residual.

[Opposite net signs on the no-core and negative-core sectors](NoCoreAdverseSign.md): with the same equal cuts, the complete no-core sector on the macro-rough reflected side contributes at least +.030 of the reference, despite containing the negative rank-four section. Negative small cores also have the opposite net sign to positive small cores. No whole-row bound follows.

[Smooth reverse cutoff and a whole small-factor bound](SmoothReverseCoreShield.md): a smooth cutoff average preserves the globally equivalent opened row. Its full nontrivial quotient core has bounded absolute mass on the macro-rough reflected side, and an arbitrarily small prime factor of the quotient up to exp(log(x)^η) costs o of the reference there, without any cutoff on the size or rank of the core.

[Both smooth cutoffs reduce the whole opened residual to bounded ranks](DoubleSmoothBoundedRankResidual.md): the full two-variable opened row has absolute mass at most a constant times the reference. For any desired fixed tolerance, removing a sufficiently small fixed polynomial factor cutoff on both variables and then deleting squareful inputs leaves bounded ranks with that error. This is a reduction of the signed problem, not the needed signed inequality.

[Coupled cutoffs and two simultaneous negative sectors](CoupledParityCompensation.md): a single globally equivalent coefficient uses different reflected parity profiles on the uncored and marked quotient families. Their disjoint complete macro-rough sectors are at most −.16 and −.10 of the reference, respectively. The complement is still uncontrolled; older bounds from other coefficients are not added.

[Where the compensated mass goes](CompensationNeutrality.md): after summing all actual quotient values, changing the reverse cutoff also has zero total effect on each of the fixed reflected prime-product profiles used above. The signed gains on selected quotient families are exactly paid back by their complements within such a profile; they are not new global slack.

[Joint parity witness for the relaxed marginal envelope](JointMarginalParityWitness.md): a positive law on nearby, not exactly reflected, integer pairs preserves the stated short divisor moments, profilewise cutoff neutralities and both selected negative inequalities. Its residual is nevertheless above the required threshold, so those specific constraints cannot close the argument without additional input using the exact equation.

[Actual reverse dispersion on a reflected semiprime band](TrueSemiprimeReverseDispersion.md): the original affine equation survives in two independent factor placements; large-residue triple-modulus dispersion and cancellation of the signed principal part remove these blocks up to arbitrary log accuracy, reaching selected modulus exponents near 153/256. This applies neither to all factor placements nor the entire genuine prime-quotient comparison.

[Dyadic divisors and Smith torsion](EACDyadicSmith.md): a large dyadic divisor forces a large Smith invariant for a nonsingular factor matrix, or an eigenvalue-one obstruction. In the strongly connected case the latter forces two vertex-disjoint directed cycles.

[Dyadic rank with prescribed prime seeds](PrimeOrbitDyadicRank.md): short supported lattice relations and a 2-adic logarithm estimate show that any hypothetical dyadic exception must have a sufficiently large prescribed forward closure or independent seed classes and a large directed cycle hitting set. This is not a contradiction for either surviving alternative.

[Feedback generators and cyclic Smith obstruction](PrimeOrbitCyclicSmith.md): small seeds generate the unit group up to sign, so every set hitting every directed cycle must generate it too. The Smith divisibility uses only cyclic components, even with an arbitrarily large transient set. Singular blocks consume precisely the stated invariant-factor allowance. The exact checker covers represented centers and synthetic block couplings, not Goldbach exceptions.

[Square-root bound on centers with compact nonsingular components](EACNonsingularSquareRoot.md): for any size cap o(log log log X), at most X^(1/2+o(1)) centers up to X have a component below that cap with nonsingular exponent presentation. This covers every three-label component, with unrestricted labels and exponents. The count is of component-bearing centers, not Goldbach exceptions.

[Jacobian bounds with singular or nonsingular complement presentation](EACJacobianSquareRoot.md): when A itself is invertible the same square-root sparsity holds for a much wider size cap, even if I−A is singular. Fixed tiny labels and one label at most the square root suffice to isolate a physical tuple. The two nonsingular cases together cover all four-label EACs; they count centers with an EAC, not failures of Goldbach.

[Five-label doubly singular components need two heavy rows](EACFiveDoubleSingular.md): the two singularities force two disjoint mutual pairs, and exact congruences exclude both the all-semiprime and one-heavy-row branches. Combined with the square-root counts this treats five-label centers with at most one heavy row, not all five-label components.

[Supported minors and sparsity for all five-label components](EACSupportedMinorFive.md): even in the doubly singular case, a signed multiplicative relation supported only on small labels bounds the number of centers. All five-label EACs together occur at at most X^(3/4+o(1)) centers up to X. This is not a count of Goldbach exceptions or a claim that the five-label class is empty.

[Sharper two-thirds bound for five-label centers](EACFiveTropical.md): exact exponent-chart enumeration plus two integer identities exclude the large-product regime in the doubly singular branch. The supported-minor count improves to X^(2/3+o(1)) for centers with a five-label component. This neither excludes all such components nor bounds unrepresented evens.

[Square-root sparsity for every component with at most five labels](EACFiveSquareRoot.md): in the remaining doubly singular five-label case, an added first-order congruence gives a finite Laurent fiber, or the possible sign supports force a reciprocal pair with a square-root parameter count. No hypotheses on the labels or exponents remain. This improves the count of component-bearing centers, not the exceptional set of Goldbach.

[No three-label components at powers of two or twice powers of three](EACThreeTwoAndThreePowers.md): a signed order obstruction, followed by an exact 39-center replay, excludes this entire component-size class along both sequences. It does not exclude other component sizes or prove representability along either sequence.
