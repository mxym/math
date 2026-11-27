# Exact classification of three-bit single-GHZ Pauli private computation

Harumichi Nishimura (arXiv:2610.23090v1, Theorem 4.5, Remark 4.7,
and Section 7) constructs 80 exactly private three-bit functions
in the one-GHZ randomized local-Pauli model. His floating-point
search leaves the other 176 functions without analytic exclusions.
We give a structural proof of all those exclusions, including
EXACT1, EXACT2, and every affine extension of the two-edge quadratic
forms. The exact feasible functions are:

- the 16 affine functions;
- the 48 affine extensions of a single quadratic edge;
- the 16 affine extensions of the triangle.

The proof also gives an exact characterization for Boolean functions
that depend on every input in the corresponding one-GHZ model for an
odd number \(k\ge3\) of parties. They must be quadratic or affine. The
quadratic graph must either have an isolated vertex or have all
degrees even. Every allowed case has a uniform Pauli construction.
For a feasible, all-essential odd-party function this construction
also achieves the exact minimum shared random seed entropy and
support size.

The results use a fixed single qubit GHZ state, one transmitted
qubit per player, a Pauli choice per local input and hidden shared
random value, and perfect correctness and privacy. They do not
settle unrestricted local-unitary or CPTP models, other resource
states, arbitrary even party counts, or the unrestricted cost of
multiparty AND.

See [proof](PROOF.md), [sources](SOURCES.md), and [exact replay](RESULTS.txt).
Run `sh replay.sh` with Python 3.10 or later; no external data or LP solver is required.
