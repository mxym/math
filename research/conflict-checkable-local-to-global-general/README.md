# Near-Singleton conflict codes with local-to-global consistency

For every pair of integers \(n\ge3\), \(2\le d\le n-1\), and
every \(\epsilon>0\), there are unbounded alphabet sizes \(q\) and
conflict-checkable, locally-to-globally consistent codes of length
\(n\), minimum distance exactly \(d\), and dimension
\(\log_q|C|\ge n-d+1-\epsilon\). In the non-endpoint range,
this gives a near-Singleton affirmative answer to the conjecture
of Applebaum and Kachlon (ePrint 2023/627, p. 11; AICR c/0096).
No asymptotic bound on decoding time is claimed.

The integer-secant mechanism has two parts. Real embeddings
and a common coefficient Gram matrix force a collection of
pair-compatible observations onto one polynomial. The remaining
issue is integrality of its coefficients. We choose evaluation
points in a totally real integer order such that no residue
class modulo a maximal ideal contains three of them. The
Chinese remainder theorem then reconstructs the interpolant
locally from singletons and pairs, and local membership implies
that its coefficients are in the integer order.

See [PROOF.md](PROOF.md) for the general argument and
[SOURCES.md](SOURCES.md) for scope. The proof is independent of
the finite exercises checked by `sh replay.sh` (Python 3 with SymPy).
