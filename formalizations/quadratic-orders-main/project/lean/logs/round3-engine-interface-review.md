# Round 3 engine interface review

Focused semantic/source review of the round 3 geometry, backward batch charge,
and final finite-sieve assembly. No reviewed Lean module was edited. This review
does not replace kernel checking or the parent's independent recursive audit.

## Result

No concrete semantic/interface defect was found in the reviewed composition.
The final engine derives its local charge and smoothing hypotheses, uses one
literal common time law for all batches, and selects one finite actual-prime
pool before quantifying over every walk.

`logs/round3-engine-interface-types.log` records the exact compiled theorem
types and endpoint axiom checks; its Lean check exited 0. Existing
`round3-finite-sieve-engine-build.log` reports a successful 3889-job build.
The endpoint axiom lists are exactly `propext`, `Classical.choice`, `Quot.sound`.

## Exact endpoints and remaining inputs

For `L : Type u`, `[AddCommGroup L]`, `data : SignedResidueData L`,
`b : Basis (Fin 2) ℤ L`, and `e : CoeffSpace ≃ₗ[ℝ] Plane`, the compiled
`ArithmeticInterface.large_step_prime_pool_no_walk` type is:

```lean
(A : ArithmeticInterface data b e) →
∀ {D : ℝ}, 1 ≤ D →
∃ S : Finset ℕ, (∀ p ∈ S, p ∈ data.primes) ∧
  ∀ z : ℕ → L, Function.Injective z →
    (∀ t, z t ∈ avoiding data S) →
    (∀ t, dist (planarEmbedding b e (z t))
       (planarEmbedding b e (z (t+1))) ≤ D) → False
```

`finiteSieveTarget_proved : FiniteSieveTarget` has no extra argument. The
literal target in `Sieve.lean:70` universally quantifies over the lattice,
basis, real coordinate isomorphism, residue data, `ArithmeticInterface`, and
every `D ≥ 0`, then selects actual primes `S` and bounds components of the
actual avoiding graph by `S.prod id ^ 2`.

`ArithmeticInterface` contains the literal CRT, paired kernel, collision,
eligible product, and positive dyadic-density assumptions. It contains no
entropy, coverage, coupling, finite-component, or no-walk endpoint premise.
`SignedResidueData` contains actual additive maps `L →+ ZMod p`, primality of
members, and surjectivity, rather than replacement finite symbols.

The intermediate `actual_selected_window_charge_sum_le` accepts explicit
local `hcharge`, smoothing `herr`, and total-error `htotal` inputs. These are
discharged in `large_step_prime_pool_no_walk`; they are not hypotheses of the
final finite-sieve result.

`eventually_common_window_batch_charge` has a threshold before `J`, every
walk, and every old family `F`. Its remaining premises are actual narrow
dyadic density, bin separation, injectivity, actual metric steps, avoidance
of the selected finite pool, `F`'s membership in that pool, and the displayed
old-label log-weight bound. It has no supplied endpoint-entropy, coverage,
information-rate, or positive-charge premise. The final engine derives its
old-label bound from actual predecessor labels and the selected gap `K`.

## Schedule and probability identity

`GenericTimeKernels` defines finite probability laws of actual time offsets.
`K.then R` uses `R.law (a+i.val)` after the first offset; the second kernel
therefore retains its dependence on the actual start. `commonSchedule` is
the fold of the actual walk-difference kernels followed by the uniform
offset smoothing kernel. No stationarity of those kernels is assumed.

`common_window_factor_law` proves the exact TimeLaw equality:

```lean
((TimeLaw.at 0).advance
  (commonSchedule z (winprefix ++ topBlocks a (J w)) 0)).advance
  (commonSchedule z (middleBlocks a m w J ++ accurateBlock m (1/20)) N)
= (TimeLaw.at 0).advance (commonSchedule z (commonBlocks a m W J) N)
```

under the corresponding literal list split. Its proof uses
`TimeLaw.advance_then` and `commonSchedule_append`. The final charge is
rewritten by this equality, including the anchor distribution; it is not a
comparison of separately chosen laws. The telescope observes this same
full law at every selected family.

The observations are `residueFamilyHom data F (z t)` (coordinates are
`data.phi p sign (z t)`) and the actual increment word
`i ↦ z (t+i.val+1) - z (t+i.val)`. Entropies, conditional information,
exception probabilities, and posterior selection are formed from actual
finite laws and these observations. Suffix costs use the cardinals of the
actual finite embedded displacement balls.

## Quantifier order and pool

The final construction orders its choices as follows:

1. Fix the lattice, arithmetic interface, and step bound.
2. Derive density `δ`, choose `a`, gap `K`, and bin-density constant `t`.
3. Choose finite window count `W` from the actual step-ball alphabet cost.
4. Choose one `m` satisfying density selection, all charge thresholds, all
   smoothing errors, and the separation scale; then choose its finite bins.
5. Fix `S = dyadicPrimePool data J W`; only then introduce an arbitrary walk.

The common schedule depends on the arbitrary walk, as an analysis law may,
but its scalar parameters and the forbidden prime pool do not. Selected
families may depend on the walk. Every extension obeys
`G ⊆ F ∪ dyadicBatchLabels data j` and stays in `S ×ˢ univ Bool`.
Greedy selection maintains the actual predecessor-label invariant, including
the last family, and the error estimate is taken against that same pool.

The final contradiction sums positive actual batch rates, compares them with
the common-law information telescope, and uses the previously chosen `W`'s
strict excess over the true step alphabet plus the total error budget.
Smaller step bounds are handled by the proved graph edge monotonicity in
`finiteSieveTarget_of_large_step_no_walk`; no metric normalization is dropped.
The subsequent periodic component bound uses the actual paired kernels and
coefficient residues modulo the product of the selected primes.

## Import/admission check and limits

The comment-stripped source traversal from `GenericFiniteSieveEngine` reaches
58 local Entry002 modules. Every external import is Mathlib; there is no
import of upstream Gaussian `Main`, `SplitSieve`, or a Gaussian endpoint.
The retained namespace `OAI.GaussianMoat` is used by replayed generic finite-law
proofs and does not introduce a Gaussian lattice assumption. The scan found
no `sorry`, `admit`, `native_decide`, or declared custom axiom. Its full closure
is recorded in `round3-engine-interface-import-scan.json`.

This endpoint does not establish `PrincipalSplitPrimeSupplyTarget`.
The inherited `mainTarget_of_supply_and_finiteSieve` remains a conditional
all-order assembly with an explicit prime-supply argument. The reviewed
finite-sieve theorem now discharges its finite-sieve argument; this review
does not claim unconditional `MainTarget` or audit a separate prime-supply proof.

Protected inherited comments in `Sieve.lean` and `Assembly.lean` still describe
the finite-sieve foundation as open. Those comments are stale after this new
module's proof; they do not alter the declarations, and no protected bytes
were changed during this review.

## Reviewed SHA-256 snapshot

| Entry002 file | SHA-256 |
|---|---|
| GenericFiniteSieveEngine.lean | `1fef7acba295b8abca34d100f4a7809e78bbaf349936b4387b6e7efec28536a3` |
| GenericCommonWindowCharge.lean | `c50d44f10134f8af5dcd18c25c039a5286f41fcdb904eea5ab8af73677755798` |
| GenericBackwardBatchCharge.lean | `6206e94a90877110bc269fe28ee36e9aa86400514cf1cd910274ee22c7ef1de6` |
| GenericWindowEntropy.lean | `4f08d2c5b28966c198a703b574be3812ac42e763f968fceb68b8ff31d7733412` |
| GenericWindowTopEntropy.lean | `361598ea5cddfbd7945be7c934f37b3a3d1ec4695b837546c290cbc8e9fc48fd` |
| GenericWindowSchedule.lean | `daf07fdac341bafa9e40f3fa4f1d7c73e75a7deb0abdd1604425733dd0ebbc30` |
| GenericWindowBandSizes.lean | `95b696b87c822086f2e8186ce62ccc6a8c231c93ee547896b47695eac106747b` |
| GenericTimeKernels.lean | `3612388ad53e35a1e4a6d9b9eb5b5f96fe238ef33213791821ef9abfa37c801c` |
| GenericWindowLogBudget.lean | `b15f05ad8e5b864c51879b1a9033464bdced6f7aeb8821db6f2347fb658282b9` |
| GenericCommonWindowNumerics.lean | `3778e397fe1ddebadd3a8ed6a3a890a3d9bb928026cf6c3c4a1b68487ddb882c` |
| SieveReduction.lean | `0403a20280eee3590f1f173e525b6a9764bf5f044b4e0d721df20c9c1302d7a5` |
| Sieve.lean | `8d3128a05af47c6138d2253e35f551eaf61d951e1626379dd9974e5620a22aad` |
