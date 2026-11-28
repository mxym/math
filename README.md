# The Exact Five-Orbit Threshold for Short Dyadic Cycles under Free Abelian Actions

A finite simple graph of minimum degree at least three with a free abelian action and at most five vertex orbits contains a 4-, 8-, or 16-cycle. Six-orbit connected cubic cyclic covers can have shortest dyadic cycle exactly 32.

Start with the [five-orbit theorem](FactorErdosGyarfasAbelianFiveOrbits.md) and the [six-orbit barrier](FactorErdosGyarfasSixOrbitBarrier.md); the [four-orbit proof](FactorErdosGyarfasAbelianFourOrbits.md) gives the reduction machinery. Three source checkers and three independent checkers are supplied. Python 3 and SymPy are needed for the entire replay. This is not a counterexample to, or a proof of, the unrestricted conjecture and does not establish a universal 32 upper bound for six orbits.

Pinned source commits: `ddc5c0d7349df8def03496622bd3b372fc203a7e`, `80b0f183f26f914035529e20fcbf8b010599c408`, `0dae1cabea6fac7c5ee6cdde9571e3023414573c`. Verify archived files with `sha256sum -c SHA256SUMS`, and rerun with `bash replay.sh`.
