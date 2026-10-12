# Entry002 v3 all-quadratic-orders Lean proof, round 5

The unchanged literal `MainTarget` is proved:

```lean
Entry002.arithmeticSupply_mainTarget_proved : Entry002.MainTarget
```

It covers every quadratic number field, every positive conductor (including
nonmaximal orders), every actual integral basis/full planar linear isomorphism,
and every nonnegative step bound. Vertices are genuine mathlib `Irreducible`
elements of the actual conductor order. The graph has its actual Euclidean
distance edges; one finite bound controls all components and injective walks.
The target, original strong supply, and original sieve source bytes are unchanged.

Read [ROUND5.md](ROUND5.md), [../TARGET-MAP.md](../TARGET-MAP.md),
[COMPILED-ENDPOINTS.md](COMPILED-ENDPOINTS.md), `overall-verification.json`, and
`target-status.json`. The weaker proof uses actual Dedekind zeta and Euler-log
coefficients, genuine completely-splitting Dirichlet supply, actual conductor
ray fields/normal closures, and the closed common-law good-bin finite sieve.
No natural prime-ideal PNT premise remains in the final theorem.

The original strong `PrincipalSplitPrimeSupplyTarget` and natural
`NumberFieldPrimeIdealPNTTarget` remain open. Secondary computability and finite
certificate theorems are not formalized. The older natural-density route is
historical; its open foundations are not substituted for the closed MainTarget.
A written-proof referee PASS is not used as a Lean theorem.

The main mathlib-only library has a fresh complete build and stored-type/body
audit of every safe owned logical declaration, including private generated
proofs. `verification.json` reports that library alone. The separate all-order
entrypoint has its own fresh compilation and exact four-module/seven-root
stored-body audit. `overall-verification.json` combines the projects.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; no unsafe,
partial, missing, admitted, or result-axiom dependency is accepted.

Lean 4.34.1/compiler 5045d0056413266e57c625dcd7c365b10e377c52 and official
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are retained. Eight missing
official modules were compiled from authenticated pinned Git bytes. Official
package artifacts and 995 pinned CFT plus two historical bridge objects are
trusted read-only inputs and hash-checked; no fresh CFT-995 rebuild, full
mathlib rebuild, or second-kernel check is claimed.

On a fresh extraction use `scripts/bootstrap.sh` for the pinned main tools,
then the isolated project's [round-5 reproduction instructions](references/upstream/arithmetic-audit/ROUND5-WEAK-REPRODUCTION.md).
The recorded `round5-runtime.json` describes this execution's cache paths.
In this saved workspace use the direct round-5 scripts; Lake must not write
through the read-only tool/package symlinks. The main audit explicitly exposes
the two historical standard-axiom metadata discrepancies for TimeLaw projections.

The archive includes exact source/evidence hashes and excludes tools, caches,
binaries, credentials, and development staging. Older checkpoints and the
unrelated mounted repository were untouched. No GitHub push/publication occurred.
