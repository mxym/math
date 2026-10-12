# Exact theorem and formal endpoints

This document states the mathematical claim of the source package and explains its correspondence with Lean. It is intended to prevent stronger or weaker readings of the actual theorem.

## Configurations and bounded logarithmic gaps

Let `I` be a nonempty countable index set, and fix a family `(A_l)_{l in I}` of subsets of `(0, infinity)`.

For each `l`, assume there exist positive natural numbers `G` and `J` such that for every natural number `j >= J`, some natural number `i` with

`j <= i < j + G`

satisfies

`A_l intersect (2^(-i-1), 2^(-i)]` is nonempty.

The constants `G,J` may depend on `l`. These intervals are left-open and right-closed. Under `z = -log_2(a)` they become `[i,i+1)`. Thus the hypothesis gives bounded gaps in sufficiently late logarithmic coordinates. It does not require a point in every individual bin.

Only the family is countable. An individual `A_l` need not be countable or measurable. Finite nonempty families and repeated configurations are allowed. A nonempty countable set of configurations can be used as the index type through its subtype.

The source definitions are `OccupiedBin` and `LogSyndetic` in [Specification.lean](project/ContinuumRemainder/Specification.lean).

## The periodic theorem

For every real `epsilon` with `0 < epsilon < 1`, there exists a set `E` of real numbers such that:

1. `E` is closed and nowhere dense.
2. `E` is one-periodic: `x + 1` belongs to `E` exactly when `x` belongs to `E`.
3. For every real `x`, its ordinary Lebesgue measure satisfies
   `measure(E intersect [x,x+1]) > 1 - epsilon`.
4. The following avoidance assertion holds simultaneously for every `l in I`.

Take arbitrary real numbers `s, alpha, y, c, M` satisfying

`s > 0`, `alpha > 0`, `c != 0`, and `M >= 0`.

Here `M` is finite because it is a real number. `M=0` is allowed. The translation `y` is arbitrary, including zero; only the coefficient `c` must be nonzero. Positive and negative coefficients are both included.

Let `f : R -> R` be any function for which there exists `tau > 0` such that, for every `a in A_l` with `0 < a < tau`,

`|f(a) - y - c*a^s| <= M*a^(s+alpha)`.

Then for every `rho > 0` the set

`{ f(a) : a in A_l, 0 < a < rho, f(a) not in E }`

is infinite.

These are infinitely many **distinct real values**, not merely infinitely many input points or indices. No continuity, measurability, differentiability, injectivity, or independence assumption is made about `f`. The remainder can vary arbitrarily within the eventual pointwise bound. Real powers are the ordinary positive-base real powers.

## The quantifier order

The essential order is

`for each prescribed family A, for each epsilon, there exists E, for all l,s,alpha,y,c,M,f, for every rho > 0`.

The same `E` works for the continuum of permitted exponents, translations, coefficients, and functions. Those parameters are not enumerated or fixed in advance. The family and `epsilon` are fixed before `E`; the set is allowed to depend on them.

The theorem does not put the existence of `E` before the choice of family. An independently checked counterexample in the audit shows why such a reversal would fail: a positive-measure candidate set admits an adaptively chosen logarithmically syndetic configuration whose affine images stay inside it. See [UniversalFamilyControl.lean](audit/controls/independent/UniversalFamilyControl.lean).

## Genuinely partial functions with eventual bounds

The primary endpoint above is a theorem about total functions `f : R -> R`. The separately proved theorem
`IndependentSemanticReview.fully_partial_eventual_target`
in [the independent semantic probe](audit/checks/SemanticProbe.lean) gives the following explicit partial-domain version.

After the same kind of common set `E` has been selected, choose any `sigma > 0` and any function

`g : A_l intersect (0,sigma) -> R`.

Assume there is a `tau > 0` such that the same remainder inequality holds for every point of this actual domain below `tau`. Then for every `rho > 0`,

`{ g(a) : a in A_l, 0 < a < sigma, a < rho, g(a) not in E }`

is infinite.

No value of `g` outside its domain is required or used. In Lean the domain is the subtype `PositiveTail (A l) sigma`. The proof extends `g` arbitrarily to a total function, uses `min(sigma,tau)` for the eventual bound, and applies the total theorem on `min(rho,sigma)`. All resulting witnesses remain inside the actual domain. The original source contains the extension and output-set lemmas in `DistinctMisses.lean`; the independent probe combines them in this fully explicit formulation.

If a statement is instead worded “for every sufficiently small positive rho,” the every-positive-tail conclusion follows by including a smaller admissible tail in any requested tail.

## Compact corollary

Under the same family and `epsilon` hypotheses, there exists a compact nowhere-dense set `K` contained in `[0,1]` such that

`measure(K) > 1 - epsilon`,

and the same infinite-distinct-output avoidance conclusion holds with `K` in place of `E`.

The formal proof takes `K = E intersect [0,1]`. An output outside `E` is also outside `K`. The compact set is not claimed to be periodic. The total-function compact endpoint is part of the preserved source; the corresponding partial-function conclusion follows by the same extension argument.

## Exact Lean correspondence

The three public endpoints in `project/ContinuumRemainder/FinalProof.lean` are:

- `robustCompactBlockerSpec_proved : RobustCompactBlockerSpec`
- `continuum_power_target : ContinuumPowerTarget`
- `compact_power_avoidance`

All are in the `ContinuumRemainder` namespace. The main theorem is closed: no unproved blocker, routing, sampling, probability, or schedule assumption remains as a parameter.

`ContinuumPowerTarget`, `AvoidsPowerRemainderTails`, `PowerRemainderOn`, and `TailValuesOutside` are defined in `Specification.lean`. In particular:

- `IsClosed E` and `interior E = empty` express closed nowhere density.
- `TailValuesOutside` is a set of outputs, and the conclusion is `Set.Infinite`.
- `volume` is the standard Lebesgue measure on the real line.
- `ENNReal.ofReal (1-epsilon)` expresses the positive real threshold inside the extended-nonnegative-real measure type; `epsilon < 1` prevents truncation at zero.
- The shifted density conclusion is for every real `x` and the closed interval `[x,x+1]`.

The independent [ExactMain.lean](audit/checks/ExactMain.lean) expands the project target definitions, and [SemanticProbe.lean](audit/checks/SemanticProbe.lean) checks the partial formulation and a concrete nonempty dyadic example. See [PROOF_ROADMAP.md](PROOF_ROADMAP.md) for the construction and [VERIFICATION.md](VERIFICATION.md) for the machine checks.

## Exclusions

No result here is asserted for arbitrary slow remainders, all continuously differentiable germs, flat leading profiles, merely positive upper Banach logarithmic density, or a common set chosen before all possible configurations. Positivity of `s` and `alpha`, nonzero `c`, the stated bounded-log-gap condition, family-first order, and strict measure slack belong to the claim. The audit includes actual constant-function counterexamples when the leading-power hypotheses are relaxed in specified ways; passing the theorem does not authorize dropping them.
