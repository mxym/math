# Robust additive encodings for residual-histogram-separating functions

A positive subclass of the finite statistical robust-ARE problem
([AICR c/0083](https://aicr.info/c/0083/), also §1.4 of
[Shuffling Is Universal](https://opencryptology.org/2025/1442/versions/20261117T152235Z.pdf)).

For a fixed finite function, suppose parties can be grouped into
interchangeable blocks and the full residual-function oracle for
each proper honest subset determines its block-wise input
histograms. Then there is a polynomial-time statistical robust
additive randomized encoding: the honest-message sum, together
with public parameters, is **exactly simulatable for proper
subsets**, and statistically simulatable for the full set.
Only independent private coins and public setup are used.
The compiler upgrades an ordinary statistical additive encoding
by randomizing the party roles and masking rejected collisions.

It covers majority on three bits, and together with the known
constant/OR/AND/parity constructions covers every symmetric
three-bit Boolean function. It also covers arbitrary fixed party
counts with finite multivalued symmetric outputs when the
histogram condition holds. The condition refers to the whole
residual function, not the result of a single completion.
We do not claim an encoding of every finite three-party
function or general resolution of c/0083.

[PROOF.md](PROOF.md) states the precise simulation semantics,
collision lemma, complexity and examples. [SOURCES.md](SOURCES.md)
distinguishes nonrobust, perfect-privacy, correlated-randomness
and computational results. For exact finite replay of the
mathematical checks, run `sh replay.sh | diff -u RESULTS.txt -`.
The toy aggregate checker validates the compiler algebra; it is
not an implementation of the upstream ordinary ARE.
