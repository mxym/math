# Entry002 v3 all-orders target and completed main-chain map, round 5

Source: mxym/math c897a556e12e460380c7cf521e88f84286994915;
v3 source SHA256 c1349aba050aeb5c8c20a6dca07fd8d1f74d029ae9702775eaf96177b597d62f.

The unchanged all-orders `MainTarget` is proved by
`Entry002.arithmeticSupply_mainTarget_proved : Entry002.MainTarget`.
The fresh complete main build, all-owned audit, separate exact external audit,
compiler types and hash bindings are included. See lean/overall-verification.json.

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

## Completed dependency chain

| Link | Actual compiled evidence |
|---|---|
| Arbitrary conductor order and coordinates | Targets, Orders, Algebra, NormBound; actual full rank/basis and integer/field norm |
| Actual ideal norm fibers and quotients | IdealNormCoefficient, IdealNormDivisibility |
| Actual prime ideal factorization/logarithm | IdealFactorLogarithm, PrimeIdealLogConvolution; all indices and number fields |
| Genuine Dedekind zeta and positive residue | IdealNormAnalytic; official mathlib ideal-counting/Dedekind-zeta theorem dependencies |
| Actual logarithmic derivative and Euler log | PrimeIdealLogDerivative, PrimeIdealEulerLogAnalytic/Identity/RealPole |
| Higher powers, higher degrees and ramification | PrimeIdealEulerLogRemainder; genuine summable bounded residual |
| Completely-splitting Dirichlet density 1/degree | PrimeIdealSplitDirichlet, PrimeIdealSplitDirichletCutoff |
| All-conductor actual principal generators | External ray-field/conductor bridge + actual normal closure + ArithmeticWeakPrincipalSupplyAssembly |
| Prime Dirichlet supply to fixed-threshold good bins | WeakSupplyDyadicChebyshev/Series, GoodBinUpper, ElementaryDiscount, DirichletCutoff/GoodBins |
| Actual cofinal integer windows | WeakSupplyWindowLogCertificate/IndependentGrid/Averaging, WeakCoreGoodBinWindowMass |
| Same-law charge and global weighted thinning | WeakCore entropy/geometry/common-window chain, WindowRates, GoodBinFiniteSieve |
| Exact finite pool before all walks and Q² bound | WeakFiniteSieveConsequences; both literal weak targets closed |
| Genuine irreducible graph restoration | Isolation, Minkowski, ComplexIsolation, ExceptionalGraphs, Restoration, OrderRestoration |
| Unchanged all-orders endpoint | ArithmeticSupplyWeakMain; no extra hypothesis, full stored-body closure audited |

## Imported mathematical foundations and open secondary results

Pinned official mathlib and the separately pinned class-field-theory corpus are
explicit imported proof foundations. Newly missing official modules and all
owned modules were freshly compiled; the 995 CFT/two historical bridge objects
were reused read-only and hash-checked. Their source provenance/import scope is
independently authenticated. No fresh 995-module rebuild or second kernel is claimed.

The stronger natural-density PrincipalSplitPrimeSupplyTarget and universal
natural NumberFieldPrimeIdealPNTTarget remain open. The original A1–A5 finite
sieve remains closed, but the final MainTarget uses the proved weaker route.
Secondary computability/finite-certificate theorems remain unformalized.
TARGET-MAP-ROUND4.md preserves the historical stronger-route map. A written
proof PASS or a definition of type Prop is not counted as a theorem proof.
