# Manuscript-to-source correspondence

This is an author correspondence map for the unpublished revision. It records
actual declarations and scope restrictions; independent final verification is
pending. Declaration counts are not discovery counts. The old audit scopes
and frozen manuscript remain unchanged.

The source snapshot and exact types in the final independent audit, once
successfully frozen and replayed, control the verification claim. This map
does not replace that evidence. `MANUSCRIPT_CLAIMS.json` is the structured
form. Paths below are relative to this repository directory.

## Physical protocol model

**Paper:** `introduction.tex; spectral-principles.tex`.

Actual original-space global unitary, complete Kraus output channel and complete Kraus representation of its partial-transpose conjugate; the global unitary is a separate entangling resource.

- [`KrausPPTProtocol`](../../formalizations/extraction-minimax-profile/MinimaxProfile/Protocol.lean#L12) (structure).
- [`tensorInput`](../../formalizations/extraction-minimax-profile/MinimaxProfile/UniversalFinite.lean#L11) (def).

## Complete positivity semantics

**Paper:** `introduction.tex; applications-verification.tex`.

Complete positivity quantifies over every finite auxiliary amplification. Choi positivity and finite Kraus representations are derived, not supplied physical certificates.

- [`CompletelyPositive`](../../formalizations/extraction-cp-interface/CPInterface/Choi.lean#L19) (def).
- [`TracePreserving`](../../formalizations/extraction-cp-interface/CPInterface/Choi.lean#L23) (def).
- [`choi`](../../formalizations/extraction-cp-interface/CPInterface/Choi.lean#L27) (def).

## Closure LOCC model

**Paper:** `introduction.tex; asymptotic-laws.tex`.

Coefficient closure of genuine finite adaptive instrument trees. Product-local inclusion and complete-PPT inclusion are proved. No claim about the global unitary being LOCC.

- [`IsClosureLOCC`](../../formalizations/extraction-locc-interface/LOCCInterface/Closure.lean#L98) (def).
- [`IsClosureLOCC.exists_actual_protocol`](../../formalizations/extraction-locc-interface/LOCCInterface/Closure.lean#L129) (theorem).

## Rains reverse realization

**Paper:** `lem:rains`.

K >= 2 for the measure-and-prepare construction. K=1 is separately exact by protocol_fidelity_one.

- [`rainsEffect_exists_actual_protocol`](../../formalizations/extraction-rains-realization/RainsRealization/Protocol.lean#L60) (theorem).
- [`rainsEffect_iff_actual_protocol_effect`](../../formalizations/extraction-rains-realization/RainsRealization/Protocol.lean#L70) (theorem).

## Coherent packing

**Paper:** `lem:packing; prop:prefix`.

Actual original-space projection ranks and integer garbage budgets; complete local decoders, coherences and all unused coordinates are retained.

- [`heterogeneous_projection_protocol`](../../formalizations/extraction-operational-completion/OperationalCompletion/HeterogeneousDecoder.lean#L11) (theorem).

## One-shot spectral envelope

**Paper:** `thm:envelope; eq:envelope-bound`.

Actual density eigenvalues and integer Bell/garbage packing. Harmonic-prefix upper and lower bounds refer to real physical channels, retaining the local cap.

- [`oneShotSpectralEnvelope_actual_lower`](../../formalizations/extraction-spectral-protocol/SpectralProtocol/EnvelopeLower.lean#L63) (theorem).
- [`oneShotSpectralEnvelope_actual_upper`](../../formalizations/extraction-spectral-protocol/SpectralProtocol/EnvelopeUpper.lean#L75) (theorem).

## General probability ensemble comparison

**Paper:** `prop:average`.

AEStronglyMeasurable probability ensemble of actual density matrices; integrability is derived from compactness. This extends the earlier finite-ensemble interface.

- [`density_ensemble_integrable`](../../formalizations/extraction-operational-completion/OperationalCompletion/ProbabilityEnsemble.lean#L34) (theorem).
- [`measurable_physical_ensemble_bound`](../../formalizations/extraction-operational-completion/OperationalCompletion/ProbabilityEnsemble.lean#L98) (theorem).

## Polynomial orbit projection

**Paper:** `lem:orbit`.

Original tensor coordinates; arbitrary complex-matrix tensor-power span, not a supplied Young decomposition. Captured mass uses the actual eigenvalue law.

- [`tensorProjection_rank_le`](../../formalizations/extraction-minimax-profile/MinimaxProfile/UniversalFinite.lean#L37) (theorem).
- [`tensorProjection_mass_ge`](../../formalizations/extraction-minimax-profile/MinimaxProfile/UniversalFinite.lean#L45) (theorem).

## Same selected universal family

**Paper:** `prop:prefix; eq:reservation; eq:grid`.

One family fixed before quantifying over the state. Fallback cases cover every positive target. The pure and mixed-state guarantees use the same witness.

- [`reservedProtocol`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedFamily.lean#L90) (def).
- [`reservedProtocol_isProductLocal`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedFamily.lean#L96) (theorem).
- [`reservedProtocol_guarantees`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedFamily.lean#L103) (theorem).

## Exact finite overhead

**Paper:** `thm:sandwich; eq:overhead; eq:overhead-explicit`.

h = log(16 Q^2 Q_Dk), including integer floor losses. The lower sandwich uses K <= reservationLocal; 10 D^2 log(k+D) requires D>=2, k>=1.

- [`reservedTotalLoss`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedQuantile.lean#L80) (def).
- [`reservationSafeCutoff_expansion`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedQuantile.lean#L82) (theorem).
- [`reservedTotalLoss_dimension_bound`](../../formalizations/extraction-operational-completion/OperationalCompletion/DimensionLoss.lean#L20) (theorem).

## Finite and varying-law Gaussian bounds

**Paper:** `cor:berry`.

Actual family fidelity and real physical protocol suprema, with the common-family inclusion hypothesis. Positive/eventually positive variance and eventual integer local-sector caps remain explicit. Moving Gaussian threshold need not converge.

- [`reservedProtocol_gaussian_error`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedTriangular.lean#L21) (theorem).
- [`reserved_optimum_gaussian_error`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedOptimumQuantitative.lean#L11) (theorem).
- [`triangular_reserved_gaussian_error`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedTriangular.lean#L43) (theorem).
- [`triangular_reserved_optimum_gaussian_error`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedOptimumQuantitative.lean#L36) (theorem).

## Concrete shrinking-variance condition

**Paper:** `cor:berry; eq:triangular`.

D V eventually >= c>0, D T eventually <= C, and D^5 log^2(k+D)/k ->0. These are sufficient conditions, not automatic APPT properties.

- [`shrinking_variance_numerical_conditions`](../../formalizations/extraction-operational-completion/OperationalCompletion/ShrinkingVariance.lean#L46) (theorem).
- [`triangular_reserved_gaussian_shrinking_variance`](../../formalizations/extraction-operational-completion/OperationalCompletion/ShrinkingVariance.lean#L96) (theorem).

## Full asymptotic laws of the same family

**Paper:** `thm:universal-laws`.

Nonnegative rates; actual positive integer target sequences. Reliability only C0<R<C; eventual exactness only R<C0. Boundary equality is not inferred.

- [`reserved_fidelity_exponent`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedLaws.lean#L53) (theorem).
- [`reserved_reliability_limit`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedLaws.lean#L35) (theorem).
- [`reserved_eventually_exact`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedLaws.lean#L11) (theorem).

## State-aware optimal exponents

**Paper:** `thm:universal-laws; eq:holder-converse`.

The real supremum is over actual physical protocol classes containing the same common-family witness; arbitrary completely-PPT protocols supply uniform upper bounds.

- [`protocolOptimum`](../../formalizations/extraction-operational-completion/OperationalCompletion/OptimalFidelity.lean#L14) (def).
- [`optimal_fidelity_exponent`](../../formalizations/extraction-operational-completion/OperationalCompletion/SharpFidelity.lean#L76) (theorem).
- [`optimal_reliability_limit`](../../formalizations/extraction-operational-completion/OperationalCompletion/OptimalFidelity.lean#L50) (theorem).

## Actual rate-set capacities

**Paper:** `thm:universal-laws; eq:appt-capacity`.

Suprema of genuinely attainable rates, including the zero boundary via target one. No unattained fidelity supremum is used to infer exact feasibility.

- [`faithfulAttainableRates`](../../formalizations/extraction-operational-completion/OperationalCompletion/CapacitySets.lean#L29) (def).
- [`exactAttainableRates`](../../formalizations/extraction-operational-completion/OperationalCompletion/CapacitySets.lean#L39) (def).
- [`faithfulCapacity`](../../formalizations/extraction-operational-completion/OperationalCompletion/CapacitySets.lean#L48) (def).
- [`exactCapacity`](../../formalizations/extraction-operational-completion/OperationalCompletion/CapacitySets.lean#L53) (def).
- [`faithfulCapacity_eq`](../../formalizations/extraction-operational-completion/OperationalCompletion/CapacitySets.lean#L167) (theorem).
- [`exactCapacity_eq`](../../formalizations/extraction-operational-completion/OperationalCompletion/CapacitySets.lean#L179) (theorem).
- [`finiteLOCC_capacities`](../../formalizations/extraction-operational-completion/OperationalCompletion/LOCCCapacity.lean#L11) (theorem).
- [`protocol_fidelity_one`](../../formalizations/extraction-operational-completion/OperationalCompletion/CapacitySets.lean#L18) (theorem).

## Gaussian optimum and integer inverse

**Paper:** `thm:gaussian`.

Fixed dimensions, positive varentropy, strict entropy-limited local gap. Natural target maximum is eventually nonempty, bounded and attained; no target monotonicity of the selected family is assumed.

- [`reserved_gaussian_limit`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedGaussian.lean#L39) (theorem).
- [`reserved_optimal_gaussian_limit`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedOptimum.lean#L10) (theorem).
- [`reservedFixedErrorTarget_gaussian`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedQuantile.lean#L53) (theorem).

## Actual Haar average and support

**Paper:** `thm:flat-average`.

Literal normalized Haar integral over the original one-copy unitary group. Its range is the intrinsic common rank-budget support.

- [`haarOrbitAverage_range`](../../formalizations/extraction-schur-completion/SchurCompletion/HaarSupport.lean#L73) (theorem).
- [`haarOrbitAverage_rank`](../../formalizations/extraction-schur-completion/SchurCompletion/HaarSupport.lean#L108) (theorem).
- [`haarOrbitAverage_trace_square`](../../formalizations/extraction-schur-completion/SchurCompletion/HaarPurity.lean#L73) (theorem).

## Minor moment and overlap asymptotic

**Paper:** `eq:minor-moment; eq:two-moments`.

Fixed integer D and s; exact product moment and fixed-N comparison are proved internally. No uniform growing-D inverse-moment asymptotic is asserted.

- [`haarMinorMoment_product`](../../formalizations/extraction-schur-completion/SchurCompletion/HaarMinorMoments.lean#L209) (theorem).
- [`haarMinorMoment_scaled_limit`](../../formalizations/extraction-schur-completion/SchurCompletion/MinorMomentAsymptotic.lean#L75) (theorem).
- [`haarOverlapMoment_scaled_limit`](../../formalizations/extraction-schur-completion/SchurCompletion/OverlapAsymptotic.lean#L17) (theorem).

## Actual sharp rank and purity

**Paper:** `thm:flat-average`.

All 1<=s<=D in Lean, with fixed D,s. The paper separates s<D logarithmic growth from the full-rank exact finite formula.

- [`rankBudget_general_rank_isEquivalent`](../../formalizations/extraction-schur-completion/SchurCompletion/GeneralRank.lean#L123) (theorem).
- [`rankBudget_rank_scaled_limit`](../../formalizations/extraction-schur-completion/SchurCompletion/GeneralRank.lean#L157) (theorem).
- [`rankBudget_rank_times_purity_limit`](../../formalizations/extraction-schur-completion/SchurCompletion/GeneralRank.lean#L166) (theorem).

## Physical minimax profile

**Paper:** `thm:minimax; eq:minimax-finite`.

Actual product-local, finite LOCC, closure LOCC and complete-PPT protocol classes; one eventual blocklength threshold before all positive integer targets.

- [`rankBudget_class_minimax_finite`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/Finite.lean#L136) (theorem).
- [`rankBudget_target_uniform_minimax`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/Uniform.lean#L127) (theorem).
- [`rankBudget_target_uniform_relative_error`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/Uniform.lean#L151) (theorem).
- [`rankBudget_full_rank_minimax`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/FullRank.lean#L41) (theorem).

## Attained rank-budget targets

**Paper:** `cor:targets`.

Success sets quantify an actual common protocol witness before all promised inputs. Fixed error log expansion needs s<D and 0<epsilon<1. Full-rank formula needs 0<=epsilon<1.

- [`exactRankBudgetMaximum_attained`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/Targets.lean#L141) (theorem).
- [`exactRankBudgetMaximum_log_correction_limit`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/TargetAsymptotics.lean#L167) (theorem).
- [`exactRankBudgetMaximum_eventually_local`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/TargetAsymptotics.lean#L218) (theorem).
- [`errorRankBudgetMaximum_attained`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/ErrorTargets.lean#L68) (theorem).
- [`errorRankBudgetMaximum_log_limit`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/TargetAsymptotics.lean#L103) (theorem).
- [`errorRankBudgetMaximum_full_rank`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/FullRankTargets.lean#L38) (theorem).

## Known-spectrum orbit targets

**Paper:** `cor:known-spectrum`.

Exact-target conclusions apply to arbitrary actual density spectra of the stated rank. Fixed-error minimax conclusions are for flat spectra, not arbitrary nonuniform fixed spectra.

- [`orbitExactMaximum_attained`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/OrbitTargets.lean#L58) (theorem).
- [`orbitExactMaximum_log_correction_limit`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/OrbitTargets.lean#L88) (theorem).
- [`orbitExactMaximum_eventually_local`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/OrbitTargets.lean#L108) (theorem).
- [`flatOrbit_target_uniform_minimax`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/FlatOrbit.lean#L110) (theorem).
- [`flatOrbitErrorMaximum_log_limit`](../../formalizations/extraction-schur-completion/physical-minimax/SchurMinimax/FlatErrorTargets.lean#L95) (theorem).

## Same-family sharp pure profile

**Paper:** `unknown-support.tex: compatibility with the common family`.

Balanced fixed local dimensions, simultaneously all positive targets and unknown pure inputs; the selected reservedProtocol is the same as in the mixed-state laws.

- [`balanced_reserved_family_sharp`](../../formalizations/extraction-operational-completion/OperationalCompletion/ReservedPure.lean#L126) (theorem).

## Actual original-wire circuit

**Paper:** `prop:pure-circuit`.

Literal lists on the original 2k qubits, actual Bell preparation and separate local readout/discard. Gate counts refer to the whole constructed word, not an unassembled step budget.

- [`compressionCircuit_action`](../../formalizations/extraction-circuit-recursion/CircuitRecursion/Compression.lean#L47) (theorem).
- [`extractionOutput_purePower`](../../formalizations/extraction-circuit-recursion/CircuitRecursion/LocalDiscard.lean#L99) (theorem).
- [`pairwiseCoordinates_physical`](../../formalizations/extraction-circuit-recursion/CircuitRecursion/PhysicalCoordinates.lean#L90) (theorem).
- [`bellPairYield_floor`](../../formalizations/extraction-circuit-recursion/CircuitRecursion/Yield.lean#L46) (theorem).
- [`bellPairYield_cPPT_maximal`](../../formalizations/extraction-circuit-recursion/CircuitRecursion/Yield.lean#L53) (theorem).
- [`extractionCircuit_isBigO`](../../formalizations/extraction-circuit-recursion/CircuitRecursion/Growth.lean#L44) (theorem).

## Finite-library word and physical error

**Paper:** `prop:pure-circuit`.

Fixed finite inverse-closed dense SU(2) library plus CNOT. Actual word existence, operator error up to global phase and fidelity >=1-2delta. This is not a classical bit-time theorem.

- [`su2_synthesis_dyadic`](../../formalizations/extraction-circuit-recursion/CircuitRecursion/SKSynthesis.lean#L88) (theorem).
- [`finiteLibrary_extraction`](../../formalizations/extraction-circuit-recursion/CircuitRecursion/FinitePrecision.lean#L37) (theorem).

## APPT entropy and actual capacity extrema

**Paper:** `eq:appt-capacity`.

Actual complex density/APPT matrices, entropy as a CFC trace, attained min and max, and physical attainable-rate capacity. No APPT entropy optimizer is solved here.

- [`quantumEntropy_eq_spectral`](../../formalizations/extraction-appt-applications/APPTApplications/Entropy.lean#L25) (theorem).
- [`exists_appt_entropy_isLeast`](../../formalizations/extraction-appt-applications/APPTApplications/Entropy.lean#L95) (theorem).
- [`exists_appt_capacity_isGreatest`](../../formalizations/extraction-appt-applications/APPTApplications/Capacity.lean#L56) (theorem).
- [`apptMaxCapacity_eq`](../../formalizations/extraction-appt-applications/APPTApplications/Capacity.lean#L76) (theorem).

## APPT explicit example and comparisons

**Paper:** `eq:appt-purity-upper; applications-verification.tex`.

Spike example for all 2<=m<=n; square-system comparison has lower coefficient (3log3-2)/2 and upper coefficient 4. No sharp maximum-capacity coefficient is claimed.

- [`apptMaxCapacity_le_puritySup`](../../formalizations/extraction-appt-applications/APPTApplications/Purity.lean#L78) (theorem).
- [`spikeState_absolutelyPPT`](../../formalizations/extraction-appt-applications/APPTApplications/SpikeState.lean#L74) (theorem).
- [`spikeState_capacity`](../../formalizations/extraction-appt-applications/APPTApplications/SpikeCapacity.lean#L10) (theorem).
- [`spikeState_capacity_error_bounds`](../../formalizations/extraction-appt-applications/APPTApplications/Asymptotic.lean#L51) (theorem).
- [`balanced_apptMaxCapacity_first_order_bounds`](../../formalizations/extraction-appt-applications/APPTApplications/Asymptotic.lean#L243) (theorem).

## Explicitly excluded endpoints

- Uniform classical finite-precision compiler Turing bit complexity.
- Exact APPT entropy optimizer or maximum-capacity leading coefficient.
- Growing-D sharp inverse-Haar-moment asymptotics.
- Reliability at R=C0 or general cap-boundary mixed-state Gaussian laws.
