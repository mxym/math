# Circuit access versus actual recovery in simple binary graph states

[Sayantan Ganguly, arXiv:2611.27300v2, §VI, problem 2](https://arxiv.org/html/2611.27300v2#S6)
asks whether, for a simple graph and a fixed dealer, the circuit
family being a quantum access structure implies that it is
contained in the recovery family of the dealer-shortened code.

**No.** Start from the graph on \(0,\ldots,5\) with edges
\(03,04,05,13,15,24,25\). Join every member of an \(r\)-vertex
clique \(T\) to \(\{1,2,3,4\}\), with no other new edges.
For every \(r\ge2\), the resulting connected simple graph
satisfies the circuit access axiom **at every dealer**.
Nevertheless, at dealer \(0\), the players \(\{1,3\}\cup T\)
form a circuit-induced set with only a one-dimensional supported
dealer projection. The set is intermediate, not authorized to
recover the qubit in this encoding. The result concerns the
relationship between two mathematical families, not the security
of an implemented scheme or nonexistence of other encodings.

For \(r=1\) the same fixed-dealer failure already occurs on
seven vertices. The proof gives the adjacency matrix, all 16
admissible support patterns and, for the unbounded family, an
exact support substitution under clique expansion. An independent
small-graph census gives minimum sizes seven for the original
fixed-dealer question and eight for the stronger all-dealers
hypothesis.

For connected simple **bipartite** binary graphs, the implication
does hold: at any fixed dealer, the circuit family is a quantum
access structure iff it equals the operational recovery family,
iff there are no intermediate sets. The equality holds at
every dealer exactly when \(A^2=I\) over \(\mathbb F_2\).
This is a bipartite subclass of §VI, problem 3, not a full
characterization for arbitrary graphs. See [SOURCES.md](SOURCES.md)
for the earlier sufficiency result and the scope comparison.

## Replay

Run `sh replay.sh` with Python 3.10+ (standard library only).
The first checker generates every simple graph through seven
vertices up to isomorphism, then applies the parity and cut-rank
tests. The second enumerates literal admissible column circuits
of the explicit matrices, independently computes the supported
dealer projection, and checks the exact replacement of entire
support families for \(r=1,\ldots,5\). No external graph data are
required to replay either check.
