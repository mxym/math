# Round 5 Euler-log / arithmetic / literal Main semantic review

Date: 2026-10-07 UTC. Review mode: independent, read-only source inspection. No Lean compilation, network operation, publication, or frozen-source modification was performed by this reviewer.

All source paths below are relative to `source/lean/` in the round-5 independent audit directory. Line numbers refer to the received round-5 source bytes. The mathematical blueprint was used to identify questions, not as evidence that a Lean link had been proved.

## Verdict and precise scope

**PASS for the inspected Euler/Dirichlet/arithmetic-to-Main source semantics. No material mathematical gap or surrogate definition was found in these links.** This is a source-level mathematical verdict, not an independently rerun kernel/build verdict. The separate parent audit must establish compilation, exact object/source binding, transitive stored-type/body closure, and imported proof trust.

The inspected route genuinely establishes a normalized rational completely-splitting **Dirichlet** limit from the real-axis Dedekind-zeta residue, passes to a finite conductor cutoff, and feeds a distinct weak principal-supply interface. Its final source declaration is exactly `arithmeticSupply_mainTarget_proved : MainTarget`, with no displayed mathematical premise. It does not establish the old natural-density supply or universal natural prime-ideal PNT. The weak finite-sieve engine itself is a separate review assignment; this report checks its interface and consumption, not every information/averaging proof in that engine.

The source-level distinctions that matter are all maintained:

- genuine ideals and determinant/absolute norms, not coefficient data assumed to behave as ideals;
- complex absolute convergence before any infinite-series manipulation;
- a real right-pole asymptotic, not an asserted complex meromorphic continuation;
- actual Galois complete splitting and a nonnegative uniformly bounded residual;
- actual finite ray fields, an actual normal closure, and actual generators in every positive-conductor order;
- original irreducible graph, original full planar equivalences, explicit component finiteness together with cardinal bounds, and restoration allowing infinitely many unit associates.

## 1. Actual coefficients, finite factorization, and zero-index safety

### 1.1 What is counted

`Entry002/IdealNormCoefficient.lean:18–25` defines the norm fiber by `Ideal.finite_setOfPred_absNorm_eq n`, its count by `Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}`, and the real coefficient by casting that count. These are all integral ideals of the genuine maximal order. `IdealNormDivisibility.lean:13–19` identifies the finite-set count with the subtype count. The zero ideal is intentionally retained: `:22–38` proves coefficient zero is 1, while `:30–41` proves coefficient one is 1.

That raw coefficient at zero does not produce a false convolution term. `IdealNormDivisibility.lean:45–70` constructs a genuine multiplication-by-a-nonzero-ideal equivalence between the quotient norm fiber and the divisible fiber; the inverse uses an actual divisibility witness and cancellation in the ideal monoid. `:74–107` retains the essential guard `if absNorm A ∣ n then ... else 0`. There is no unconditional replacement by the possibly nonzero raw coefficient at quotient index zero.

`Entry002/ArithmeticSplittingCount.lean:19–24` defines `nonzeroPrimeIdealsUpTo` by actual norm cutoff, `IsPrime`, and `P ≠ ⊥`. `PrimeIdealAnalyticDefs.lean:33–46` defines the prime-power support and coefficient as the sum of `log N(P)` over positive powers `N(P)^k=n`. `:56–61` proves `N(P)≥2`, and `:86–96` proves exponent uniqueness and a valid finite exponent cutoff. Thus counting each ideal once in that support is the intended von Mangoldt coefficient, not a loss of multiplicity.

### 1.2 Exact finite identity

`IdealFactorLogarithm.lean:15–44` links prime-ideal power divisibility to multiplicity in actual `normalizedFactors I` and takes the logarithm of the actual norm product. `:64–103` rewrites this as a finite prime-power divisor sum, with nonzero ideal and exponent bounds derived rather than assumed.

`PrimeIdealPowerSummation.lean:28–74` verifies that the support definition equals the exponent sum; `:78–105` shows enlarging the finite cutoff adds only zero terms. `PrimeIdealLogConvolution.lean:15–41` retains divisibility when selecting a divisor-antidiagonal index, and `:47–82` expands the actual convolution. Finally `:87–118` proves

`a_K(n) log n = (a_K * Λ_K)(n)`

for every natural index and every number field. The `n=0` case is separate at `:90–91`; positive indices use the actual norm-fiber bijection. No Euler product, prime asymptotic, or analytic continuation is a premise of this identity.

## 2. Genuine complex LSeries and the real-pole/logarithm bridge

### 2.1 Dedekind-zeta is the actual ideal series

`IdealNormAnalytic.lean:24–50` converts the sum of the actual norm counts into the count of all nonzero ideals and applies mathlib's genuine ideal-counting asymptotic. This is an asymptotic for all integral ideals, not a disguised prime-ideal PNT. `:54–65` obtains a linear partial-sum bound and **complex `LSeriesSummable` for every `Re(s)>1`**. `:68–92` obtains the abscissa bound and holomorphy in precisely that half-plane.

`IdealNormAnalytic.lean:75–77` identifies mathlib's `NumberField.dedekindZeta K s` with this coefficient `LSeries` by unfolding the actual definitions. `:96–111` derives positivity on the real axis from nonnegative coefficients and the genuine norm-one coefficient; it therefore also establishes zero imaginary part and real-axis nonvanishing, not merely positivity of a surrogate real function.

`IdealNormAnalytic.lean:114–122` uses the actual positive residue and mathlib's right-limit theorem

`(s−1) ζ_K(s) → residue(K) > 0`, as real `s→1+`.

The theorem is deliberately limited to this real right-pole asymptotic. No part of the inspected proof promotes it to continuation or zero-freeness on `Re(s)=1`. The exact-abscissa argument at `:133–151` is consistent with that limited claim, although exact equality of abscissae is not needed for the final weak supply.

### 2.2 Log derivative has its summability premises discharged

`PrimeIdealVonMangoldtBound.lean:16–43` proves `Σ f(P/p)≤[K:ℚ]` from the genuine ramification/inertia identity, without requiring K Galois. `:47–83` identifies the rational prime under prime-power support and obtains the degree bound at a rational-prime power. `:89–104` proves the pointwise domination `Λ_K(n)≤[K:ℚ]Λ(n)` for every n.

`PrimeIdealChebyshev.lean:156–168` transfers the ordinary von Mangoldt absolute-convergence theorem by norm comparison. Its final unconditional wrappers apply the proved coefficient bound. Thus `PrimeIdealLogDerivative.lean:30–49` applies `LSeries_convolution'` only after obtaining the two genuine complex summability proofs (`:41–42`), and invokes the derivative theorem inside the convergent half-plane. The resulting identity is `ζ_K(s) L(Λ_K,s)=−ζ'_K(s)`. Division by zeta in `:53–60` is restricted to real `x>1`, where nonvanishing has already been proved.

### 2.3 Euler log is proved, not postulated

`PrimeIdealEulerLogAnalytic.lean:21–59` defines `b_K(n)=Λ_K(n)/log n`, proves its totalized zero/one values, nonnegativity, coefficient bound, and exact log-multiplication identity. `:62–83` gives actual complex absolute convergence and derivative `−L(Λ_K,s)`. `:85–98` supplies the real-infinity limits `L(b_K,s)→0` and `ζ_K(s)→1`.

`PrimeIdealEulerLogIdentity.lean:17–41` differentiates `Real.log (ζ_K(x)).re − Re L(b_K,x)`. Positivity is used at `:22–26`, and the zero imaginary part is explicitly used at `:29–38` when taking real parts of the complex logarithmic-derivative identity. `:60–78` then uses connectedness of `(1,∞)`, zero derivative, and the infinity limit to fix the integration constant. Therefore

`log Re ζ_K(s) = Re L(b_K,s)` for every real `s>1`

is an actual theorem, not an Euler-product field supplied as an assumption. There is no complex-log branch issue: the argument uses the ordinary real logarithm of a proved positive real zeta value.

`PrimeIdealEulerLogRealPole.lean:17–31` applies continuity of the real logarithm at the strictly positive actual residue and `Real.log_mul` with both factors nonzero. It proves `Re L(b_K,s)+log(s−1)→log residue(K)` along the genuine right-neighborhood filter.

## 3. Galois splitting and all remainder terms

### 3.1 The coefficient of a rational prime is correct

`ArithmeticPrimeIdealCounting.lean:37–53` equates prime norm p with actual lying-over p and inertia degree one. `:57–59` defines complete splitting by **every actual prime above p** having e=f=1. This is not vacuously consumed: the reverse implication in `:80–87` obtains a prime above p from the genuine lying-over instance. `:63–79` uses Galois equality of inertia degrees plus the unramified hypothesis. `:90–104` uses the genuine efg/automorphism-degree formula to count the splitting fiber, and `:110–143` explicitly makes the norm fiber finite and proves its cardinality is either degree or zero.

`PrimeIdealEulerLogRemainder.lean:17–44` proves `b_K(p)` is that finite fiber cardinality, cancelling the nonzero `log p`. `:46–53` therefore proves its exact Galois unramified value `[K:ℚ]·1_split(p)`.

The coefficient `completelySplitPrimeCoefficient` at `:56–58` includes actual primality, unramifiedness, and splitting. `ArithmeticSplittingAsymptotics.lean:20–22` defines the actual supplied prime set with exactly those conditions. No abstract density label replaces membership.

### 3.2 Higher residue degrees and higher powers are really included

The residual at `PrimeIdealEulerLogRemainder.lean:61–72` is the actual difference between b_K and the degree-times-splitting indicator. `:74–103` proves it equals the sum of:

1. the b_K terms at nonprime indices, and
2. the b_K terms at ramified rational-prime indices.

Both pieces are nonnegative. For a prime ideal with `N(P)=p^f`, every contribution at power k occurs at n=p^(fk). If f≥2, or k≥2, this n is composite. These contributions are exactly in the first piece. Higher powers above ramified primes are also in the composite piece; the finite ramified piece is only the remaining prime-index contribution. Thus neither the f≥2 ideals nor the high powers disappear under the terminology “nonprime indices.” The n=0,1 values are already zero.

`PrimeIdealEulerLogRemainder.lean:105–124` proves finite ramified support from divisibility by the nonzero field discriminant, and hence summability for every real exponent.

`PrimeIdealEulerLogRemainder.lean:128–190` bounds the composite coefficients by degree/log 2 times the actual rational von Mangoldt composite contribution and identifies its partial sum exactly with ψ−θ. `:194–214` uses the elementary `|ψ−θ|≤2√x log x` bound and `log x=o(x^(1/4))`; no rational or number-field PNT is invoked. `:218–248` consequently proves the actual nonnegative composite series converges at exponent one via a `3/4` abscissa bound.

`PrimeIdealEulerLogRemainder.lean:250–303` adds both actual summable pieces, defines the finite field-dependent constant `C_K=Σr_K(n)/n`, and proves for **every** real s>1:

`0 ≤ Σ r_K(n)/n^s ≤ C_K`.

The uses of tsum comparison carry both summability proofs at `:300–303`. This is a real finite bound independent of s; it is not a bare totalized tsum whose nonsummability could silently assign zero.

## 4. The exact Dirichlet limit and finite conductor cutoff

`PrimeIdealSplitDirichlet.lean:25–35` commutes real part with the complex tsum only under the explicit genuine summability proof. At nonzero indices it converts complex powers to real rpow; index zero is handled separately. `:44–65` decomposes the actual Euler-log sum as

`[K:ℚ] Σ_{p split, unramified} p^(−s) + R_K(s)`.

The supply series and residual are separately proved summable before `tsum_add`. `:67–87` connects that identity to the genuine real zeta logarithm and derives both one-sided inequalities.

`PrimeIdealSplitDirichlet.lean:89–100` proves the normalization `log(1/(s−1))→∞`. `:102–121` obtains normalized Euler log →1; `:123–138` squeezes normalized residual →0 with eventual positivity of the denominator. `:142–158` divides by the genuine strictly positive field degree and proves

`Σ_{p split, unramified} p^(−s) / log(1/(s−1)) → 1/[K:ℚ]`.

`WeakSupplyInterfaces.lean:47–50` is explicitly a cofinal positive-upper-supply condition with one fixed d>0. `PrimeIdealSplitDirichlet.lean:162–191` derives it from the stronger actual limit. It does not claim an eventual lower bound at every dyadic counting scale.

`PrimeIdealSplitDirichletCutoff.lean:15–36` is an exact finite removal identity for the actual membership indicator. `:52–86` proves the difference is uniformly bounded by f+1 and becomes zero after normalization. `:120–146` therefore preserves both the exact degree-reciprocal limit and positive upper supply for the set `{p | p splits unramified in K ∧ f<p}`. The strict cutoff is sufficient to exclude every prime dividing positive f, including all nonmaximal conductors. This does not require a prime-counting asymptotic.

## 5. Ray/conductor extraction and weak arithmetic assembly

`ArithmeticSupplyWeakFromDirichlet.lean` in this section means `references/upstream/arithmetic-audit/ArithmeticSupplyWeakFromDirichlet.lean`.

The source endpoint `:41–82` introduces only K, its ordinary Field/NumberField instances, quadratic degree, positive f. It obtains a ray-class-field realization from `rayClassField_reciprocity` at `:45–46`, takes `L=R.extension`, defines the actual normal closure N inside `AlgebraicClosure L`, proves NumberField/Galois instances, and chooses a genuine L→N embedding at `:47–53`. The prime supply is the actual splitting set of N above f, and its Dirichlet supply is furnished at `:54–56` by the theorem just audited.

For each supplied p, `:57–68` obtains an actual height-one prime in K by the normal-overfield splitting package, with e=f=1, relative splitting in R.extension, and a principal conductor-order generator. The modulus exclusion is not an unexplained field: `:18–36` proves that lying over a p>f forces the prime to be outside the modulus, since membership would imply p divides f and hence p≤f.

The earlier genuine arithmetic bridge is explicit:

- `ArithmeticSupplyRayBridge.lean:19–31` derives integrality of a field generator from equality of its actual fractional ideal with an integral ideal.
- `:36–68` uses actual ray reciprocity/splitting and the actual ray-principal subgroup; the generator satisfies local higher-unit congruences, not a synthetic congruence predicate chosen to imply the conclusion.
- `ArithmeticSupplyRayConductor.lean:19–45` forms the modulus from the actual finite valuation/count vector of (f), with empty infinite part, and proves its valuation identity.
- `:49–100` turns the local higher-unit conditions into completed-ideal membership, valuation bounds, global divisibility f∣a−1, then actual membership in ℤ+f𝓞_K.
- `:104–121` gives the actual conductor generator and its precise maximal-order principal ideal.

Crucially, the conductor quotient calculation is not an invalid Dedekind calculation on a nonmaximal order. `ArithmeticSupplyElementary.lean:20–46` assumes only a finite free integral domain over ℤ and identifies actual quotient cardinality with the absolute determinant norm. `:51–83` constructs a surjective **unital ring map** to ZMod p and its exact principal kernel. `:111–134` handles the real conductor lift and compatibility of determinant norm with maximal-order norm. `:88–101` derives the paired intersection from actual distinct maximal principal ideals and an actual product associated to p.

`ArithmeticWeakPrincipalSupplyAssembly.lean:14–38` retains the complete non-density conclusions. Its proof at `:40–84` obtains the genuine two residue maps, their surjectivity, exact divisibility kernels, conjugate generators, norms p, and paired kernel pO, and constructs the actual `SignedResidueData`. The positive upper Dirichlet input is preserved unchanged. In `ArithmeticSupplyWeakFromDirichlet.lean:69–82`, the selection outside P is harmless: `a(p)=0` outside the supplied set, but every norm/kernel/conjugacy statement and surjectivity requirement is only for p∈P.

The completed focused supplement `RAY_CONDUCTOR_SEMANTIC_REVIEW.md` independently passes this bridge and traces the upstream existence construction in more depth. Its key interface facts were also checked directly here. With `CFT/` denoting `references/upstream/ClassFieldTheory/Lean4/ClassFieldTheory/`:

- `CFT/Definitions/GlobalClassFieldTheory/FiniteAbelianExtension.lean:28–57` is a subtype of genuine intermediate fields in the separable closure, carrying actual finite-dimensionality and abelian-Galois proofs. It yields the NumberField instance by finite extension.
- `CFT/Definitions/ConductorsAndRayClassFields/RayClassFieldRealization.lean:27–44` stores this actual field plus genuine unramifiedness and a Frobenius-normalized Artin equivalence. The existence theorem `CFT/Theorems/ConductorsAndRayClassFields/RayClassFieldReciprocity.lean:27–42` has only Field/NumberField and a modulus as inputs; its proof constructs the realization from the zero ray-class subgroup theorem, not from an assumed realization.
- The supplemental review follows that theorem through `RayClassSubgroupExistence.lean:29–33`, `GlobalClassFieldTheory/GlobalClassFields/PublicRayClassComparison.lean:448–504`, and the concrete construction in `GlobalClassFieldTheory/GlobalClassFields/RayClassFieldRealization.lean:498–529`. It finds the finite-index condition discharged for every modulus by `AlgebraicNumberTheory/RayClass/Topology.lean:914–931`, rather than supplied as an extra endpoint premise.
- `ArithmeticSupplyElementary.lean:299–308` exposes the genuine finite normal closure, normality, and an actual embedding. `ArithmeticSplittingTower.lean:137–147` derives its NumberField and Galois instances. `:21–56` derives splitting descent and relative splitting from actual e/f tower multiplicativity; `:73–97,122–131` constructs a nonzero prime by lying over. The local relative-splitting theorem does not require an additional assumed IsGalois certificate for L/K.
- `ArithmeticConductorConjugation.lean:72–92` proves the chosen nonidentity quadratic automorphism moves the actual prime because its decomposition stabilizer has cardinality e·f=1. `:96–135` turns that into distinct principal conductor ideals and discharges the paired-residue theorem. `ArithmeticSupplyElementary.lean:256–292` proves the conjugate product equals the actual norm and is associated to p inside the conductor order itself.

No material gap was found by either pass. The whole external CFT corpus remains an explicit imported foundation; neither pass claims to have rebuilt or mathematically rederived its entire dependency closure.

## 6. Actual Main, nonvacuity, and infinite-unit restoration

### 6.1 The target has not been replaced

`Targets.lean:12–33` is the literal subring ℤ+f𝓞_K. `:35–41` defines coefficient space, genuine Euclidean plane, and restriction of a full real linear equivalence. `:43–48` uses actual `Irreducible` elements and actual bounded-distance edges between distinct vertices. `:59–73` quantifies every number field of degree two, every positive conductor, every integral two-element basis, every full planar equivalence, and every D≥0, then demands one B giving:

- **Finite** reachable component and ncard≤B for every vertex;
- at most B terms in every finite injective edge walk;
- no infinite injective edge walk.

This rules out the `Set.ncard`-of-an-infinite-set default-value loophole: finiteness is a separate conjunct both in Main and in `Graphs.lean:18–23`'s `UniformComponentBound`.

The parent independently compared all 80 earlier owned mathematical modules against round3 and found them byte-identical; evidence is `INDEPENDENT_PREFLIGHT.json` / `Entry002_DELTA.json`. This reviewer also computed the current target hash:

`Targets.lean SHA256 = f4cbd00f1853dc53b955a2b05e7d07223a6a7fe5e0fc762d87e8ed397fe64671`.

### 6.2 Basis and full planar coordinates are not empty assumptions

`Orders.lean:23–40` constructs the actual injection into the maximal order and derives finite/free ℤ-module instances. `:44–67` uses multiplication by positive f to obtain the opposite rank inequality, hence exact full degree. `:71–74` explicitly constructs `conductorOrderBasis` for **every** positive conductor and quadratic K. Thus Main's basis quantifier cannot be discharged vacuously for nonmaximal orders.

The allowed planar equivalence type is between the concrete two-real-coordinate function space and its Euclidean normed presentation. It has the canonical coordinate-equivalence witness: the inverse linear equivalence of mathlib's `EuclideanSpace.equiv (Fin 2) ℝ`. The source actually uses that standard equivalence, with its direction explicit, at `GenericSignedArithmetic.lean:372–379` (and the replayed `WeakCoreSignedArithmetic.lean:380–387`). This source reviewer did not compile a new standalone witness. The parent audit subsequently freshly compiled `replay/audit/NonvacuitySmoke.lean` successfully (reported exit 0): its lines 3–4 directly construct `Nonempty (CoeffSpace ≃ₗ[ℝ] Plane)` using `(WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm`; lines 5–7 test the basis witness for arbitrary quadratic K and every f>0; lines 8–10 separately test f=2. The smoke source and empty compiler output were inspected here; the command/exit-code binding is maintained by the parent. The existing mathematical source additionally proves every accepted e has nonzero cell determinant (`GenericSignedArithmetic.lean:372–380`).

`Embedding.lean:19–25` proves injectivity of every actual planar embedding from b and e; `:46–51` proves finite lattice balls after every invertible real coordinate change. The argument never replaces a full planar map by a single real number-field embedding. `NormBound.lean:37–54` extends the field embeddings to continuous linear functionals in the supplied coordinates, and `:62–97` proves the required quadratic determinant-norm estimate for every e.

The actual supplied generators have positive prime determinant norm and prime-cardinality quotient. This is genuine nontrivial arithmetic data: the supplied set has a strictly positive normalized Dirichlet limit, and `ArithmeticSupplyElementary.lean:54–83` derives nonzero generators and maximal principal ideals. There is no premise that the irreducible graph or all supplies are empty.

### 6.3 The assembly really invokes restoration

`WeakAssembly.lean:14–23` consumes the weak supply and weak finite-sieve targets. It constructs only `ArithmeticCore` plus upper Dirichlet supply; it does not fabricate the old A5 natural-density field. `ArithmeticCore.lean:15–28` consists exactly of the first four original conditions; `:39–58` derives those conditions from the actual order norms, kernels, and paired kernels.

`WeakAssembly.lean:24–35` chooses the finite list of actual generators and proves them nonunits from genuine prime norm. `:36–56` rewrites the actual residue avoidance set exactly as nondivisibility by those generators. `:57–63` applies `quadraticOrder_restoration_of_principal_sieve` and obtains both walk conclusions from its component bound. The final `ArithmeticSupplyWeakMain.lean:11–13` supplies the proved arithmetic theorem and `weakFiniteSieveTarget_proved` to this assembly. `WeakFiniteSieveConsequences.lean:10–15` links that latter endpoint to the separately reviewed Dirichlet-to-good-bins and geometric engine. The weak target itself at `WeakSieveTargets.lean:11–17` still concludes the actual finite avoiding graph bound `(S.prod id)^2`, with S chosen before every vertex/walk.

### 6.4 Infinite units and associates are not silently made finite

`Algebra.lean:22–24` uses the correct general fact that a nonunit divisor of an irreducible is an associate, with no UFD or “irreducible=prime” assumption. `:39–52,115–140` uses determinant norm multiplicativity to bound the norms of selected exceptional irreducibles.

`ComplexIsolation.lean:21–78` proves the ratio/root bounds over a normed field. For arbitrary real or imaginary quadratic K, `:82–102` uses the two genuine complex embeddings and identifies their product norm with the actual order determinant norm. `:107–169` proves **finiteness of distinct close pairs of bounded-norm elements**, not finiteness of the bounded-norm set. The nonzero difference norm is a nonzero integer at `:132–137`; arbitrary planar coordinate differences are bounded by actual operator norms at `:139–150`; all complex embeddings are covered at `:158–160`; and mathlib's finiteness of integral elements bounded in all embeddings is used at `:161–169`.

`OrderRestoration.lean:133–153` extracts the finite set of nonisolated exceptional vertices from those close pairs. `ExceptionalGraphs.lean:58–69` permits infinitely many isolated vertices, each with a singleton component. `OrderRestoration.lean:175–194` combines the ordinary avoiding bound, finite lattice degree bound, enlarged exceptional graph at step D(B+1), and the genuine short-walk bridge to obtain the full bound `max B (M*(1+Δ*B))`.

The generic restoration statement `Restoration.lean:219–241` assumes bounds on the induced ordinary graph, local degrees, and enlarged exceptional graph, never the desired full bound. It allows the exceptional set itself to be infinite. `Graphs.lean:57–95` derives the finite and infinite injective-walk conclusions from actual finite reachable components. This matches the infinite-unit requirement and contains no hidden “finite unit group” restriction.

### 6.5 Concrete real-quadratic/Pell nonvacuity, including a nonmaximal order

This subsection supplies a direct mathematical instance check. **It is not a claim that a new concrete Lean instance was freshly elaborated or compiled in this review.** No Pell-specific Lean dependency or additional source theorem was added. The universal basis and full-planar nonemptiness witnesses were also freshly smoke-tested by the parent, as recorded in §6.2. No specific Lean construction of K=ℚ(√2), its Pell units, or its concrete α was freshly compiled. The following mathematical arithmetic makes the real-quadratic, nonmaximal, infinite-unit content explicit.

Take K=ℚ(√2), whose maximal order is ℤ[√2], and f=2. The actual conductor order is

`O₂ = ℤ + 2ℤ[√2] = ℤ[2√2]`.

Write t=2√2, so t²=8. The integral basis is (1,t), and the full planar map can be the coefficient map `a+bt ↦ (a,b)` with the Euclidean norm on both coordinates. This is a legitimate full two-dimensional map, not the single real embedding `a+bt ↦ a+b·2√2`.

Let ε=3+t. Its inverse is 3−t because `(3+t)(3−t)=9−8=1`; both lie in O₂. Its positive real value is greater than one, so εⁿ are pairwise distinct for n≥0. This explicitly witnesses an infinite unit group in a nonmaximal conductor order. It also gives Pell solutions: writing εⁿ=aₙ+bₙ√2, one has `aₙ²−2bₙ²=1`, and bₙ is even. No finiteness of units or quotient by associates is compatible with this example.

There are actual infinitely many irreducible vertices, too. Set α=1+t. Its field and determinant norm are `1−8=−7`. Multiplication by α in basis (1,t) has matrix `[[1,8],[1,1]]`, determinant −7. Thus its principal quotient has cardinality 7, is a field, and the nonzero nonunit α is prime and hence irreducible. Equivalently, the quotient map is `a+bt ↦ a−b (mod 7)`; its kernel is the principal ideal (1+t). Each εⁿα is a distinct associate of α and an actual irreducible of O₂. The graph in Main is therefore infinite in this concrete example. Main asserts that every fixed-D component is uniformly finite, not that this vertex set is finite.

The same infinite-unit phenomenon occurs for every positive conductor f in this example. The unit ε=3+2√2 has a unit image in the finite quotient `𝓞_K/f𝓞_K`; therefore some positive power εᵐ is congruent to 1 modulo f. Its inverse is also congruent to 1, so both belong to O_f and define a genuine unit there. The powers ε^(mn) remain distinct under the positive real embedding. For f=1 this statement is immediate. This explains mathematically why all-conductor coverage genuinely includes infinitely many unit associates, rather than only the maximal order or an imaginary field.

The restored exceptional set for a finite selected generator list may therefore be infinite. The source avoids any false finiteness claim precisely through `ComplexIsolation.lean:107–169`'s finite **close-pair** theorem and `ExceptionalGraphs.lean:58–69`'s treatment of arbitrarily many isolated vertices. The earlier finite-basis construction covers this f=2 instance, and the arbitrary-e arguments cover its coefficient plane and every invertible real linear change of those coordinates.

## 7. No old PNT/natural-density premise is filled implicitly

The new endpoint path never supplies or assumes `NumberFieldPrimeIdealPNTTarget`. `PrimeIdealAnalyticDefs.lean:22–30` defines that still-open natural counting proposition. `PrimeIdealNaturalPNTBridge.lean:82–120` remains conditional on θ_K(x)/x→1 or ψ_K(x)/x→1. `ArithmeticSplittingAsymptotics.lean:100–106,129–161` still displays the old `hPrimeIdeal` premise for natural/dyadic conclusions.

Those older declarations may be present in an imported module because `completelySplittingRationalPrimes` is defined there, but importing a conditional implication is not assuming its antecedent. In the new proofs the splitting-set definition is used, while the lower supply is derived from the new Euler-log limit. The original `PrimeSupply.lean:11–29` still requires a positive **natural dyadic** asymptotic, whereas `WeakPrincipalSupply.lean:12–28` retains every non-density witness and ends in the distinct upper-Dirichlet condition.

The source of `ArithmeticSupplyWeakClosedCompilerAudit.lean:67–72` expressly demands the final stored declaration's type be exactly the constant `Entry002.MainTarget`, rather than a Pi type with hidden antecedents. `:81–112` is designed to traverse stored type/body dependencies and reject extra axioms, unsafe/partial constants, and missing references. This report inspected that audit source; success of its independent execution belongs to the parent compiler audit, not this semantic pass.

## 8. Limits, minor documentation notes, and final assessment

1. The mathematical source links inspected here have no identified material gap. No new theorem assumption replaces the arithmetic or Euler-log conclusion.
2. Official mathlib's ideal-counting, LSeries, actual Dedekind-zeta residue, norm/ramification, and embeddings results remain imported foundations. The source bundle does not include the full text of every official module, including the complete DedekindZeta module; this review verifies the calls and the actual local binding, not an independent proof of all official mathematics.
3. The external CFT realization and its supplied source are reviewed for interface meaning in the focused supplement, but the full upstream corpus is not wholly re-refereed here. Its artifact/provenance and kernel trust must remain explicit.
4. Historical comments saying a weak target is “open” occur in definition/interface modules (`WeakPrincipalSupply:4–6`, `WeakSupplyInterfaces:5–6,57–59`, `WeakAssembly:6–7`). They are stale explanatory comments now that later endpoint modules prove those targets. They do not alter a Lean statement and are not a mathematical defect. The old natural-density/PNT comments remain substantively correct.
5. This pass did not rerun Lean, infer a kernel PASS from prose, or treat a #check/#print listing by itself as evidence of closure. The parent must combine this mathematical verdict with independently verified build and stored-body evidence.

**Bottom line:** the new weak route is semantically the intended repair: actual Dedekind ideal series and real pole → actual Euler log → bounded higher-degree/high-power/ramified remainder → actual Galois rational-split Dirichlet supply → all-positive-conductor principal residue data → separately proved weak finite sieve → the original literal irreducible-graph Main, including all full planar coordinates and infinite-unit restoration. The stronger natural prime-counting and natural-density supply targets remain open.
