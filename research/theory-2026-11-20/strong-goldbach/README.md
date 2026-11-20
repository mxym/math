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
