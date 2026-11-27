# Exact quantum randomness optimizers from a weighted MIC

For every \(d\) and every nonzero positive operator \(R\)
on \(\mathbb C^d\), there is a simple, explicit rank-one
extremal measurement with \(d^2\) effects such that
\[
 \operatorname{Tr}(RM_j)=\operatorname{Tr}(R)/d^2
 \qquad\text{for every outcome }j.
\]
The effects also determine the state from exact outcome
statistics. The construction works for singular weights
and does not require a SIC.

This supplies the exact maximizing measurements missing
from Gutierrez Anco, Nemoz, and Brown's fixed-state quantum
randomness formulas. Those formulas were known as suprema;
we show that the equalities can always be attained by a
finite POVM. The POVM may depend on the chosen state and
entropy criterion. The same construction supplies the
measurement condition in Sarkar et al.'s existing one-sided
certification proof for every full-Schmidt-rank bipartite
pure state, not just in specific low-dimensional parameter
ranges. It is not a new device-independent test or a
finite-precision guarantee.

[Proof](PROOF.md) · [Primary sources and scope](SOURCES.md) ·
[Verification output](RESULTS.txt)

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~

The replay checks the exact algebraic core over rational
weight profiles and independently constructs the complete
effects, verifies their real Hermitian rank, and evaluates
the min-entropy guessing certificate numerically. The
proof does not depend on these finite checks.
