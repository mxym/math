## J.7. Complete certified four-subset continuation in degrees 26--50

**Theorem J.F.** For every integer \(26\le n\le50\), the exact sharp
coefficient for the \(S_n\) action on four-element subsets is the rational
number in the following table. Together with Theorem J.D, this determines
every degree \(11\le n\le50\). No exact all-degree four-subset formula or
higher-rank asymptotic is asserted.

**Proof.** The fixed file
[k4_n26_50.json](../../notes/johnson-short-cycle-spectrum/certificates/k4_n26_50.json)
specifies, at each of the 25 degrees, two nonidentity positive short-cycle
supports and three negative supports. Adding the identity gives the six
supports used by the rational linear systems in Theorem J.D. Each support
is realized by its prescribed cycles and a single remaining long cycle, as
in Lemma J.B. The separate
[optimizer-free checker](../../notes/johnson-short-cycle-spectrum/check_k4_26_50.py)
constructs the exact integer moment matrix using the proved transfer identity,
solves the primal and dual systems by rational Gaussian elimination, and
checks nonsingularity, strictly positive primal weights, both mass sums and
all orbital moment equalities. It enumerates every feasible short-cycle
vector and verifies both dual bounds and the support contacts. The moment
sum is constant, so the omitted redundant fifth moment also agrees.

The identity weight equals the table entry and the dual oscillation.
Theorem J.C therefore gives the upper bound and primal attainment. The
checker also computes actual conjugacy-class sizes and a positive rational
scale for which the signed perturbation of the uniform law is nonnegative;
thus these are genuine marginal-preserving probability witnesses, not merely
formal LP solutions. All 25 degrees and all feasible types in each degree are
covered by fixed literal input. The complete exhaustive replay is part of
the finite proof, with its output and source hashes supplied. No discovery
solver is needed. QED.

The table is transcribed from that fixed JSON, not rounded numerical output.
