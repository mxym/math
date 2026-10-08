# Entry002 v3 all-orders target and final coverage map

Source: https://github.com/mxym/math at c897a556e12e460380c7cf521e88f84286994915.
Manuscript: preprints/002-quadratic-order-moats/v3/source.tex, SHA-256
c1349aba050aeb5c8c20a6dca07fd8d1f74d029ae9702775eaf96177b597d62f.

## Literal requested result

Theorem 1.1 (`thm:main`, source lines 58–61) asserts that for every quadratic
order, every permitted full planar embedding, and every finite nonnegative step
bound, one finite constant bounds every connected component of the actual
irreducible graph; the same constant bounds the number of terms of every
injective bounded-step walk.

The preceding paragraph specifies K/ℚ quadratic, O=ℤ+fO_K with f≥1, a real
linear isomorphism of the two-dimensional coefficient space to ℝ², and genuine
nonzero nonunit irreducibles. No unique factorization is assumed. There is no
uniformity in K, f, coordinates or D. A single real field embedding is excluded;
arbitrary fixed real coordinate coefficients need not be computable.

`Entry002/Targets.lean` defines the ACTUAL conductor subring in K, not an abstract
placeholder ring or norm surrogate. `MainTarget` quantifies all K with genuine
mathlib Field and NumberField structures and finrank ℚ K=2; every positive f;
every actual integral Basis (Fin 2) of the order; every real linear isomorphism
of its coefficient space to EuclideanSpace ℝ (Fin 2); and every real D≥0. All
components are genuine SimpleGraph.Reachable sets, with both finiteness and
ncard≤B. Vertices use genuine mathlib Irreducible of the actual subring. Edges
join distinct vertices exactly when the actual Euclidean norm of the embedded
difference is ≤D. Finite injective sequences and impossibility of an infinite
injective edge walk are included using that same B.

The basis quantifier is not a vacuity loophole: Orders.conductorOrderBasis
PROVES that every positive-conductor quadratic order has such a basis. The
existence of the permitted full real linear coordinate maps is standard finite
dimensional linear algebra, not a main theorem assumption. The arbitrary fixed
norm extension is an informal scope corollary by norm equivalence, not an
additional proved target here; the literal displayed main target uses the
manuscript's planar Euclidean norm.

`Sieve.lean` records all A1–A5 exactly: joint surjectivity for every finite prime
selection/sign choice, paired kernel pΛ, positive c√p separation, the product
bound for actual nonzero primitive vectors, and a positive natural dyadic
asymptotic density. FiniteSieveTarget keeps the exact Q² component conclusion.
PrimeSupply.lean separately records actual conjugate principal norm-prime
residue kernels, their pO intersection, ring-map compatibility and dyadic
density in every conductor order. MainTarget and the universal prime-supply
target remain OPEN. The literal FiniteSieveTarget is now proved by the closed
round3 theorem `finiteSieveTarget_proved`. Typechecking a target Prop does not
prove it.

## Completed main-chain links

| Source role | Compiled modules and actual achievement |
|---|---|
| Order model/nonmaximal conductors | Targets + Orders: actual ℤ+fO_K, integrality, finite/free ℤ module, full field rank for f>0, genuine two-element basis, actual rational localization K |
| Integer/field/Minkowski norm bridges | Algebra + Orders: actual Algebra.norm ℤ agrees with field norm, product of genuine conjugate embeddings, nonzero integer difference norms |
| §9 eq:normbound | NormBound: for every K,f,b,e, ∃C≥1, actual |N(x)|≤C‖iota(x)‖², with no supplied norm-bound premise |
| A1 | CRT: joint surjectivity follows for every finite distinct prime/sign selection of the actual surjective additive maps |
| A3/A4 | Algebra + NormBound + ArithmeticInterface: actual norm divisibility implies positive √p collision separation and distinct eligible-prime product bound in arbitrary coordinates |
| §9 prop:interface | ArithmeticInterface.order_interface_of_principal_residues constructs ALL A1–A5 from displayed genuine principal prime kernels, paired intersection and density; supply/density is not proved or imported |
| §10 irreducible exceptions | Algebra: nonunit divisors are associates, units have absolute norm one, exceptions have selected bounded actual norm values; no UFD |
| §10 radius/isolation | Isolation + Minkowski + ComplexIsolation: scalar root bound, real/imaginary radii, arbitrary lattice finite balls; conductor_planar_finite_close_pairs proves isolation for ALL actual quadratic fields/conductors/full coefficient embeddings, with no assumed properness or norm-integrality premise |
| §10 graph restoration | ExceptionalGraphs + Restoration: finite nonisolated vertices suffice despite infinitely many isolated exceptions; full max(B,M(1+ΔB)) bound via actual walks and a proved finite cover |
| Complete §10 all-order application | OrderRestoration.quadraticOrder_restoration_of_principal_sieve: actual finite principal avoiding-component bound implies full irreducible component bound, for every K,f,b,e,D; induced-graph transfer, finite degree, enlarged exception bound and triangle/short-walk bridge all proved |
| §1 walk consequences | Graphs: component bound implies finite injective walk terms≤B, actual path length+1≤B and no infinite injective walk |
| §§3–4 generic entropy | FiniteLaw + Information: upstream genuine universal finite probability, entropy, conditional information, short-list deficits, exchangeable signed entropy slopes and enrichment chain replayed with exact proof bodies |
| §3 Boolean cube/Hoeffding | BooleanCube + SignConcentration: exact generic upstream cube isoperimetry, separated class growth and fair-sign Hoeffding proofs replayed |
| §8 generic telescope | Telescope: exact upstream conditional information infrastructure and finite numerical telescope; generic finite-word/block/common-law telescope with explicitly displayed block/shift-rate hypotheses |
| End-to-end reduction | The earlier two-premise assembly is retained. Round3 FiniteSieveConsequences.mainTarget_of_principalPrimeSupply uses the now-proved finite sieve to give `PrincipalSplitPrimeSupplyTarget → MainTarget`; prime supply remains the explicit open premise. |

## Round 2 actual main-chain progress

See lean/ENGINE-COVERAGE.md for the precise compiled dependency map. New proofs
establish the actual signed-kernel determinant/index, rectangle separation,
walk frame and many differences, fresh displacement entropy, multiscale
endpoint enrichment, actual common sampling/smoothing law, posterior coverage
and residue-batch selection, common-law word telescope, density/numerical band
guards, positive embedding normalization, and no-walk to exact periodic `Q²`
component reduction. Statements retain their displayed scalar and integration
conditions. The generic telescope's original conditional support is augmented
by actual word and smoothing proofs; rates are no longer merely assumed in
those newer endpoints.

## Round 3 closed generic finite sieve

`Entry002.finiteSieveTarget_proved : Entry002.FiniteSieveTarget` proves the
complete literal A1–A5 generic theorem. The proof constructs actual windows,
top/middle/bottom difference kernels and terminal uniform smoothing. Actual
geometric enrichment derives endpoint entropy at every natural start; backward
coverage and posterior sampling derive each positive batch information charge.
True nested prime/sign families stay in the same preselected finite pool with
honest cardinality and logarithmic costs. All charges use one literal common
time law. Actual increment-word divisibility, smoothing errors and the finite
alphabet bound give a telescope; linearly many windows exceed its budget.
Actual lattice periodicity and König's lemma then give the exact Q² component
conclusion. There is no supplied batch certificate, information-rate assumption
or no-walk target in the final theorem type.

The finite window number, density constant, gap, threshold and prime pool all
precede the quantifier over walks. The arbitrary lattice constants, full planar
coordinates and every nonnegative D are retained. The proof uses the pinned
licensed Gaussian development as a reference for generic arguments, and
reproves the actual arbitrary-lattice geometric and arithmetic steps. No
Gaussian endpoint or finite v4 classification is imported.

## Exact remaining blocking foundations

1. PrincipalSplitPrimeSupplyTarget remains open. Normal closure is now proved
   from pinned mathlib. Genuine rational PNT is compiled and recursively
   audited in the isolated external project; genuine arbitrary-modulus ray
   class reciprocity and integral-generator criteria are compiled and
   recursively audited in the separate project. The remaining
   mathematical foundation is natural complete-splitting Chebotarev density.
   Round3 proves actual local ray congruence implies global 1 mod f, conductor
   generators and prime norm, and genuine distinct conjugate unramified
   degree-one prime residue pairs. Actual finite-ideal decomposition and
   negligible-error proofs reduce the natural splitting density to an explicit
   number-field prime-ideal PNT. That analytic theorem remains unproved; its
   actual count premise is never inserted as a result-replacing axiom. The
   isolated ArithmeticSupplyFromPrimeIdealPNT module now proves the complete
   universal supply and all-order MainTarget implications from that sole
   explicit analytic premise. See ArithmeticSupplyCoverage.md.
2. FiniteSieveTarget and FiniteSieveNoWalkTarget are proved in round3. They are
   no longer blocking foundations for MainTarget.

The licensed OpenAI Gaussian source is a proof reference. Its Gaussian
endpoint and comparator scaffold are never imported as an all-order theorem.
No finite v4 classification, checker, written-proof review, target Prop or
conditional implication is counted as an unconditional MainTarget proof.

## Evidence/trust boundary

Fresh owned-module compilation and complete recursive stored-type/body audits
are recorded in lean/logs, declaration-inventory.json, dependency-graph.json and
verification.json. Every safe owned logical declaration is checked, including
compiler-generated supporting declarations. Allowed logical axioms are only
propext, Classical.choice and Quot.sound. Official Lean/stdlib/mathlib cache
artifacts are trusted; they are not rebuilt or checked by a second kernel.
No GitHub push/publication occurred. All work stays in the new isolated directory;
the unrelated mounted repository was not inspected or modified.
