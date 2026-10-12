Public-copy note: this is the source-semantic review written before the independent rebuild and replay completed. Its final conditional sentence records that earlier review stage. The completed independent verification is reported in AUDIT_REPORT.md and FINAL_AUDIT.json in this directory. Project paths below are relative to the package root.

# Independent semantic review of the continuum remainder theorem

Date: 7 October 2026. Scope: read-only inspection of the submitted proof sources, independently of the submitted PASS reports. All 18 `ContinuumRemainder` modules (2,780 lines), README, and written reference were read. Relevant inherited definitions and proof bridges were also inspected. No submitted source or shared dependency was modified.

## Verdict

**Semantic PASS, conditional on the separate fresh compilation/kernel replay.** I found no mismatch between the main formal conclusion and the stated family-first, all-real-power, power-remainder avoidance theorem, and no unfulfilled mathematical construction premise in the public endpoints. The apparent specification-valued hypotheses in intermediate modules are explicitly discharged in `FinalProof.lean`.

This report is a source-level semantic audit, not a replacement for the main auditor's compiler, imported-closure kernel, dependency-provenance, and axiom inventory checks. It does not certify novelty, publication readiness, arbitrary slow remainders, or a result for all configurations at once.

The independently written `SemanticProbe.lean` provides additional nonvacuity and exact partial-domain probes. It compiled successfully against the independent fresh build. Its axiom outputs contain only `propext`, `Classical.choice`, and `Quot.sound`; see `audit/independent/logs/SemanticProbe.log`. An initial probe-only arithmetic normalization error was corrected before the passing run; submitted sources were unchanged.

All source references below are relative to `project/`, unless explicitly marked README or written reference.

## 1. Exact statement and quantifiers

`ContinuumRemainder/Specification.lean:35–42` defines the target with this order:

1. A type `ι`, its `Countable` and `Nonempty` instances, and `A : ι → Set ℝ`.
2. Positivity and logarithmic syndeticity of every `A l`.
3. An arbitrary `ε` with `0 < ε < 1`.
4. One existential set `E`.
5. The conclusions of closedness, empty interior, one-periodicity, strict measure in every shifted closed unit interval, and `AvoidsPowerRemainderTails A E`.

The latter predicate expands at `Specification.lean:29–33` to every family member and **all real** `s, α, y, c, M`, **every unrestricted total function** `f : ℝ → ℝ`, the hypotheses `s > 0`, `α > 0`, `c ≠ 0`, `M ≥ 0`, and every positive real tail radius. None of those parameters is a natural/rational surrogate, and none is chosen before the set as an additional outer fixed input. There is no continuity, differentiability, measurability, injectivity, or mutual-independence hypothesis on `f`.

`PowerRemainderOn`, at `Specification.lean:22–24`, is exactly an eventual positive-tail bound on members of `A`, with absolute error at most `M * a^(s+α)`. It is not a bound at all real points or a global bound away from zero. Because `M : ℝ`, its finiteness is intrinsic. `M=0` is allowed.

`TailValuesOutside`, at `Specification.lean:26–27`, is a **set of real output values** `z` satisfying `f a = z`, with `a ∈ A`, `0 < a < ρ`, and `z ∉ E`. `Set.Infinite` therefore means infinitely many distinct values. It is not merely infinitely many witnesses, input indices, or repetitions.

`FinalProof.lean:37–38` supplies the target directly from `robustCompactBlockerSpec_proved`. `FinalProof.lean:40–46` states the separate compact consequence. Neither public theorem has a residual blocker, routing, independence, or probability-bound assumption.

### Countable index type versus a set of configurations

Only the **family's index type** is countable. The individual sets `A l` may be uncountable and nonmeasurable. A nonempty countable set `F : Set (Set ℝ)` of configurations is covered by taking the index type to be its subtype and the indexed configuration to be subtype value. Finite families and repeated entries are allowed. Thus the indexed-family presentation does cover the ordinary mathematical interpretation of a prescribed countable set of configurations.

The final declaration uses `ι : Type`, rather than a universe-polymorphic `Type*`. This covers the usual family and the subtype of any `F : Set (Set ℝ)`; it does not remove any ordinary countable-family assertion about subsets of the real line. Higher-universe abstract presentations can also be reindexed by a countable small index set, but that reindexing is not itself a public endpoint here.

The statement does **not** give one `E` for every logarithmically syndetic configuration simultaneously. A new family may require a new `E`. Nonemptiness is used honestly in `TopologyConclusion.lean:106–111` to select a configuration for the empty-interior argument.

## 2. Source hypothesis and nonvacuity

`OccupiedBin` is membership in the genuine half-open interval `(2^(-j-1), 2^(-j)]`, expressed as `Ioc (dyadic (j+1)) (dyadic j)` (`Specification.lean:14–16`). The inherited `dyadic` is literally `(1/2)^n` (`ContinuumGeometric/GeometricParameters.lean:9`). `LogSyndetic` asserts some positive natural `G,J` such that every block of integer bins `j,…,j+G-1` with `j≥J` contains an occupied bin (`Specification.lean:18–20`). There is no stronger assumption that `A` itself already comes with an enumerated uniformly separated sequence.

Under `z = -log₂ a`, these bins are exactly `[j,j+1)`; this is proved with both correct endpoint conventions in `Sampling.lean:70–81`. Integer-block occupancy is the usual bounded-gap logarithmic condition near zero: it gives an occupied log in `[j,j+G)` for each integer `j≥J`; rounding the start of an arbitrary real interval changes the needed length by at most one. Conversely uniform occupancy of sufficiently late real-log intervals gives such an integer-block condition after enlarging the integer gap bound. This is not the weaker positive upper Banach density condition.

The sampling theorem genuinely selects points from the input set. `Sampling.lean:83–117` recursively selects occupied bins, and `Sampling.lean:121–165` chooses an actual point in each such bin. The result records membership, positivity, the requested strict tail bound, exact real logarithms, a positive upper gap bound, a lower gap strictly greater than `3/s₀`, and divergence of the logs. `Sampling.lean:29–62` proves the power identity, convergence to zero, and strict decrease of the samples. No sample-existence structure is left as an unproved assumption at the end.

A concrete witness is `A = range dyadic`: every bin is occupied by its included right endpoint `dyadic j`; `G=J=1` works. This positive, discrete configuration is formalized independently in `semantic_review/SemanticProbe.lean`. Exact leading powers `f(a)=y+c a^s` satisfy `PowerRemainderOn` with `M=0` for every real `s,α`. The probe combines those facts with the actual target using a nonempty `Unit` family and `ε=1/2`. Thus both the configuration and remainder hypotheses have explicit nonvacuous instances.

The main construction ignores the additional `A ⊆ Ioi 0`, `q>0`, and `h>0` arguments (`FinalProof.lean:12`). This is benign: the selected samples are positive regardless of possible other elements of `A`, and the construction works for a larger range of `q,h`. Ignoring those assumptions does not manufacture any impossible object.

## 3. Total versus genuinely partial tail functions

`DistinctMisses.lean:100–114` defines a true subtype domain `PositiveTail A σ` and a total extension equal to a supplied partial function on that domain, with an arbitrary default elsewhere. `DistinctMisses.lean:118–127` transfers a bound on the domain; `DistinctMisses.lean:131–143` proves exact equality of output sets on every smaller tail. The supplied `sampling_evidence/FinalTargetAudit.lean` combines these with the final theorem.

The full intended statement permits a function defined on `(0,σ)∩A` whose error bound holds only eventually, say below another positive `τ`. This introduces no gap: extend the function, and use `min σ τ` as the eventual-bound radius. For an arbitrary positive requested `ρ`, apply avoidance at `min ρ σ`; these witnesses lie in the domain and are included in the set for `ρ`. Hence the assertion holds for every `ρ>0` when the image is understood on the function's actual domain. It does not evaluate an undefined function outside that domain.

The independent `fully_partial_eventual_target` probe spells out all of this in Lean: eventual bound on a partial subtype, no regularity requirement, no `ρ≤σ` conclusion restriction, and a common `E` still selected before `σ,g,τ`. This also justifies the README's claim that “every sufficiently small positive tail” and “every positive tail” are equivalent by inclusion of a smaller tail.

## 4. Ordinary real, topological, and measure semantics

The endpoint refers to ordinary Mathlib `ℝ`, `Set`, `IsClosed`, `interior`, `IsCompact`, `volume`, and `Real.rpow`, through standard Mathlib imports. Inspection of the submitted new and inherited module declarations found no replacement instance for real topology, Lebesgue measure, order, arithmetic, or power. The only relevant new instances are finite-type/decidability infrastructure; local classical decidability changes proof choice, not these mathematical meanings.

`OnePeriodic S` is exactly `∀ x, x+1 ∈ S ↔ x ∈ S`; `unitDensity S` is exactly `volume (S ∩ Ico 0 1)` (`ContinuumGeometric/RoutingInterfaces.lean:14–18`). They are not abstract placeholders.

`PowerParams s₀ s₁` is the closed subtype product `[s₀,s₁]×[1,2]`, and `powerPoint input C (x,p)` is exactly `x+t*C*input^s` (`ContinuumGeometric/ClosedProjection.lean:79–93`). With positivity of the selected input, those are ordinary positive-base real powers and genuine continuous functions of the compact parameters.

`periodicGridKey N z` is `floor(N*z) mod N` (`ContinuumGeometric/BoundedGrid.lean:50–51`). This implements left-closed/right-open cells, including negative real lifts and periodic wraparound. `gridAddress` is the corresponding finite address (`ContinuumGeometric/RoutingGeometry.lean:15–35`). The routed set uses the terminal bit at the actual recursively routed leaf and actual address (`ContinuumGeometric/RoutingModel.lean:79–141`).

Probability is a concrete finite sum with fair selector-table product weights and Bernoulli-`p` terminal-table product weights (`ContinuumGeometric/FiniteRoutingProbability.lean:17–31`). Positivity and normalization are proved at lines 43–51 and 108–125. `LocalAddressSeparation` specifies own-address injection, absence from exposed coordinates, and terminal injection after selectors are fixed (`RoutingInterfaces.lean:51–55`); this requirement is proved for the samples rather than postulated at the endpoint.

The strict lower bound uses `ENNReal.ofReal (1-ε)` and Lebesgue volume. Since `0<ε<1`, this threshold is positive and exactly the intended real number; no truncation makes the assertion vacuous. Every measured set lies inside a unit interval, so there is no hidden infinity issue.

## 5. Complete construction chain

### 5.1 Actual samples and exact finite candidate coverage

`Counting.lean:28–94` counts both-strict open windows directly for an increasing nonarithmetic sequence. The lower count is obtained using the first index strictly past the lower endpoint and the first at or past the upper endpoint, so equality at either boundary does not disappear from the analysis. `Counting.lean:103–145` transfers the sample log gaps to every `s∈[s₀,s₁]`.

The canonical active labels and their equivalence with actual activation are proved at `Counting.lean:147–207`. The potential pair set includes exactly every pair active at some real compact parameter (`Counting.lean:235–269`), subject to the proved output-window bound. Its cardinality retains the position-dependent `candidateLabelBudget U T k`; it is not silently replaced by a constant. Summation across outgoing edges supplies actual active-pair counts (`Counting.lean:271–352`, `SampleLocalProbability.lean:45–90`).

### 5.2 Actual real-log geometry and routing connections

`LogGeometry.lean:8–37` links real logs to actual positive inputs and offsets. Strict activation gives offsets in the correct short positive interval (`39–76`), separation from the center and pairwise own-grid separation (`78–122`), and predecessor/all-earlier key agreement at stable centers (`124–150`). `LogGeometry.lean:152–168` uses that agreement to turn an actual local own-selector/terminal success into membership in the routed set.

`LogRouting.lean:108–141` derives the precise address-separation contract from these geometric facts. Inherited `RoutingSeparation.lean:27–66` proves terminal separation for every selector assignment, including possible shared auxiliary reads. There is no independent-path assumption.

### 5.3 Boundary-complete continuum representatives

`LogSignatures.lean:7–51` preserves the actual activation and grid crossing signs, including equality. Positive lifted boundaries are established before logarithms are used. `logGridVector` records `none` exactly for inactive pairs and the actual finest-grid key for active pairs (`74–81`).

`LogSignatures.lean:87–124` proves finite representatives preserving this entire vector, with `20*(number_of_cuts+5)^2` cardinality. It invokes the proved affine arrangement theorem, not a presumed oracle: the inherited chain is `LocalSignatures.lean:151–168` → `GridCutBridge.lean:92–122` → `Planar.lean:288–330`. `CutSign` has separate negative, zero, and positive constructors (`Interfaces.lean:11–17`); the underlying arrangement statement includes all cuts and every point of the closed rectangle (`Interfaces.lean:33–41`). Coincident and degenerate cuts, intersections, and rectangle endpoints therefore receive their actual signatures.

`LogRouting.lean:24–103` proves that vector equality preserves the genuine local miss event for **every table assignment**. Representative choice occurs before the universal table quantifier. `LogSignatures.lean:160–193` supplies the actual subtree-grid entropy bound. No exponent grid, approximate power, or center discretization is used.

### 5.4 Fixed-parameter joint law, continuum union, stable centers

`LogRoutingProbability.lean:46–104` enumerates precisely the active candidates and obtains the joint center-atom/all-miss identity with factor `(1-p/2)^m`. Its inherited proof fixes every selector before averaging the injective terminal reads, then averages the free own selectors (`FiniteRoutingProbability.lean:231–284`). No division by atom mass occurs.

The finite representative union bound is applied to these actual events (`LogRoutingProbability.lean:108–160`). `SampleLocalProbability.lean:92–118` substitutes the actual sample counts. `SampleStableProbability.lean:27–73` connects the globally defined missed-center event to such a local miss at a default vertex. The probability proof partitions into genuine center-exposure atoms, charges the no-default event, and sums the joint local bounds (`SampleStableProbability.lean:120–192`). The result holds at every stable real center, not almost every center or a finite selection of centers.

### 5.5 Noncircular schedule and actual positive error cost

`SampleSchedule.lean:59–126` first obtains the sample, then fixes branching, depth, and gap, and only then selects the late output origin and logarithmic base length. It proves each field of `SampleRoutingSchedule` (`25–55`), including the starting-output guard, positive length, activation count, `U≥4`, earlier-grid guard, `|k|≤U`, `U+k≥0`, `T≤U`, strictly decaying entropy, no-default budget, unstable-density budget, positive radius, and actual buffer cost.

`ErrorSchedule.lean:19–87` establishes a logarithmic upper bound and sublinear span. The finest-grid double-buffer cost is explicitly `4*2^(U+T+2)*errorRadius`, with an exact exponent simplification (`89–111`), and it tends to zero when `α₀>0` and `s₁>0` (`114–144`). `exists_late_robust_schedule` intersects eventual conditions rather than choosing a radius after freezing incompatible entropy parameters (`147–170`). The arbitrary `Ufloor` survives in `SampleSchedule.lean:59–62,123`.

`SampleSchedule.lean:135–162` retains and then absorbs the absolute candidate-position factor using `T≤U` and `|k|≤U`. The inherited scalar estimate even handles zero candidates by using `P+1` (`RoutingEntropy.lean:32–90`).

`ErrorDomination.lean:11–18` defines an everywhere strictly positive radius. The actual estimate uses `s≤s₁`, `α₀>0`, and `U+k≥0`, including equality in the last condition (`20–71`). These guards are carried through to the actual active points; they are not omitted premises in the final assembly.

### 5.6 Closed missed centers, finite measure selection, and full-sequence repair

`RobustRepair.lean:44–82` defines open activations and a genuine missed-center set: there exists a compact real parameter for which every active finite test misses the open inner buffer. The inherited failure relation is a closed intersection and its projection is closed because the parameter factor is compact (`ClosedProjection.lean:21–75`). This needs neither compactness nor a grid of centers.

The allowed error endpoint is closed (`|e|≤r`), while both buffers are open. The strict inner distance plus the weak error inequality gives a strict outer distance (`ContinuumGeometric/ZeroErrorBuffer.lean:29–43`; `ErrorDomination.lean:73–86`). Thus no equality endpoint is lost.

The robust repair theorem splits on membership in the actual missed-center set (`RobustRepair.lean:90–127`). Outside it, a finite active point hits the inner buffer and the radius bound puts the perturbed point in the outer buffer. Inside it, the **full infinite sampled sequence**, not the finite routing candidates, approaches the center despite arbitrary permitted errors (`RobustRepair.lean:15–42`) and eventually hits its open cover. Empty finite test collections do not break this logical repair.

`RobustAssembly.lean:96–107` pays the double buffer cost using the actual routed-set finite-grid representation. The concrete finite law yields expected outer density at most `2p` and missed-center density at most `3p` (`111–165`). The inherited finite Fubini and outcome selection use actual Lebesgue integrals, normalized nonnegative weights, and no division by positive masses (`RoutingMeasure.lean:59–85,134–157,187–233`). A single outcome is chosen, and a real open periodic cover of its closed exceptional set is obtained with arbitrarily small positive excess (`PeriodicRepair.lean:325–342`). The final robust blocker has density **strictly less** than `6p` (`RobustAssembly.lean:38–83`).

`FinalProof.lean:11–35` instantiates every remaining premise with the proved sample schedule, sample identities and convergence, actual buffer bound, unstable-density bound, and actual stable miss estimate. This closes the construction unconditionally under exactly the source/compact-parameter hypotheses in the blocker specification.

## 6. Exhaustion, signs, every tail, and infinitely many distinct values

The countable budget index is exactly `(l,N,j,k,q,h)` with the positive/natural lower bounds shown at `Exhaustion.lean:16–18`. Positive summable budgets are selected, and **all blockers are chosen before the target function or real parameters are introduced** (`Exhaustion.lean:42–92`). Each blocker has a continuum of exponents internally; no countable enumeration of exponents, errors, functions, or translations occurs.

For given positive `s,α`, the argument chooses `[1/N,N]` containing `s` and `1/j≤α`, then a natural `q≥M`. On a sufficiently small tail below 1, the power comparison has the correct direction: `a^(s+α)≤a^(s+1/j)` (`Exhaustion.lean:93–119`). The chosen tail is below both the requested radius and the original error-validity radius. Nonzero signed coefficients are covered by exact dyadic normalization, using reflection for the negative case (`120–138`). Reflection preserves period and unit density with the half-open endpoint correction (`ContinuumGeometric/CountableExhaustion.lean:15–37`). Each reflected pair costs at most its single assigned budget; total density is strictly below `ε` (`Exhaustion.lean:65–91`).

This first gives one miss in every positive input tail. `DistinctMisses.lean:26–57` proves, using the nonzero coefficient and positive remainder rate,

`0 < (|c|/2) a^s ≤ |f(a)-y| ≤ (3|c|/2) a^s`

on a sufficiently small tail. No continuity of `f` is used. `DistinctMisses.lean:60–98` then gets noncentral missed output values arbitrarily close to `y` inside **each fixed requested tail**, forcing the output set to be infinite. The argument explicitly rules out the tempting but insufficient inference from many input indices to many output values.

## 7. Topology, shifted density, and compact corollary

`TopologyConclusion.lean:98–129` takes `E=Uᶜ`; openness and periodicity of `U` give genuine closedness and periodicity of `E`. The affine zero-error instance yields empty interior using one member of the nonempty family (`75–94,106–111`). Since `E` is closed, empty interior is equivalent to nowhere density; no separate weaker notion is substituted.

The strict complement-volume estimate comes from the actual partition of a unit interval (`ContinuumGeometric/CountableExhaustion.lean:98–120`). `TopologyConclusion.lean:41–73` proves equal density in every translated unit interval through integer translation, half-open splitting, wraparound, and null endpoint changes. Thus the theorem's `∀ x : ℝ` lower bound really applies to `[x,x+1]`, not just `[0,1]` or integer translates.

The compact consequence is precisely `K=E∩[0,1]`, with compactness, inclusion, empty interior, strict mass, and the same output-tail avoidance predicate (`TopologyConclusion.lean:133–150`). Avoidance transfers because shrinking the avoided set only enlarges the missed-value set. The compact set is not asserted to be periodic.

## 8. Comparison with the written proof and README

The written theorem at `submitted-evidence/WRITTEN_PROOF.txt:14–51` and submitted README `5–24` agree with the exact formal quantifier order and error class. The shift from “every sufficiently small ρ” to “every ρ>0” is a valid monotonic strengthening/equivalent formulation, including for partial domains as discussed above.

Written sections 2–8 (`WRITTEN_PROOF.txt:53–345`) correspond to actual source chains listed in sections 5–7 of this review. In particular, the newly required real-log sampling, moving activation indices, continuum signatures, nonzero-error schedule, and full-sequence repair are all used in the final endpoint; the final theorem is not obtained merely by renaming the old geometric theorem.

Benign implementation differences:

- The formal robust assembly gives `<6p`, which implies the stated `≤6p` blocker specification.
- The formal sign-pattern proof uses a directly proved affine-arrangement bound after logarithms, rather than reproducing the written drawing/arc insertion description. It preserves the same necessary zero strata and gives the required quantitative budget.
- The formal entropy bound retains `P+1`, making the scalar inequality valid even for zero candidate count; the written exposition simplifies its estimate under `P≥1`.
- The formal schedule needs only the guards actually consumed by its tree lemmas; it does not repeat every redundant minimum in the prose schedule. In particular no missing `L≥g` hypothesis is consumed by the formal tree/entropy/repair chain.
- The formal repair uses convergence for each fixed allowed parameter/error family, which suffices for `∀ parameters/errors, ∃ input`. The written proof also observes uniform convergence, but the stronger uniform observation is unnecessary for the target and is not being presumed silently.

The scope exclusions in the submitted README `80–83` and written section 9 (`346–380`) are appropriate: this does not address all configurations, arbitrary slow remainders, all `C¹` germs, flat leading profiles, or a general positive-upper-Banach-log-density hypothesis. The written sections 10–11's auxiliary controls and obstruction discussion are not extra claims delivered by `continuum_power_target` and are not needed as premises in its formal proof.

## Final assessment

The source-level mathematical chain is complete and semantically aligned with the stated stronger target. No corrective source change is requested. A successful independent fresh build and trust-zero imported-closure replay, with the expected standard axiom inventory and pinned dependency checks, would complete the separate formal-verification layer; this report does not infer those results from the submission's own evidence.
