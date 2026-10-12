# Literal theorem and exact scope

The production endpoint is the theorem

    Entry002.arithmeticSupply_mainTarget_proved : Entry002.MainTarget

Import `ArithmeticSupplyWeakMain` to access the unconditional endpoint. The `Entry002` umbrella alone is the separately audited mathlib-only phase.

The endpoint is in [ArithmeticSupplyWeakMain.lean](project/lean/references/upstream/arithmetic-audit/ArithmeticSupplyWeakMain.lean); its statement is exactly the unchanged constant `Entry002.MainTarget`, not a theorem with a prime-supply, density, PNT, geometric or finite-sieve premise. The formal definition remains in [Targets.lean](project/lean/Entry002/Targets.lean).

For every quadratic number field K, every natural conductor f > 0, every actual integral basis b of the order ℤ + f𝓞_K, every full real linear coordinate isomorphism e to the Euclidean plane, and every real D ≥ 0, there exists B in ℕ such that:

1. Each reachable component of the graph of actual irreducible elements of that order is finite and has cardinality at most B. Two distinct vertices are adjacent when their embedded Euclidean distance is at most D.
2. Every injective finite walk with those adjacency constraints has length at most B.
3. There is no injective infinite walk with those constraints.

The same B serves these three conclusions for the fixed K, f, b, e and D. The theorem does not assert one universal B independent of those parameters. `conductorOrder`, `PrimeVertex`, `primeGraph`, `Irreducible`, `Algebra.norm`, the actual basis and the full planar isomorphism have not been replaced with models or assumptions.

## What remains open

- The original natural number-field prime-ideal PNT endpoint
- The original strong natural-density principal-split-prime supply target
- An effective algorithm or an explicit quantitative formula for B
- Novelty, publication priority and suitability for any particular journal

The Dirichlet limit and cofinal logarithmic good-bin supply do not fill a natural-density field. The Main proof takes the different, proved weaker-supply route. The package's retained older PNT-conditional modules remain conditional results.
