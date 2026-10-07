# A 10/3 asymptotic partite edge lower bound

This is a continuation of the [finite 13/4 bound](../partite-cover-number-lower-bound/README.md).
For every \(\delta>0\), a constant \(C_\delta\) exists such that
every finite simple intersecting \(r\)-partite \(r\)-uniform hypergraph,
\(r\ge2\), satisfies
\[
 |E(H)|\ge5\tau(H)-(5/3+\delta)r-C_\delta.
\]
Therefore the minimum edge count under \(\tau(H)\ge r-1\) has
\(f(r)\ge(10/3-\varepsilon)r\) for every fixed \(\varepsilon>0\)
and sufficiently large \(r\), whenever the class is nonempty.

The [complete proof](paper.md) and [PDF](paper.pdf) track the number of
linear four-blocks through a part-cover saving, then combine matching and
star covers. All finite-degree and additive errors are included. The
standard Kahn small-codegree edge-colouring theorem is a cited input;
Sivashankar's degree-three lemma is included with its attributed full proof.
The precise new ingredient and inherited methods are distinguished.

```sh
python3 verify.py
./formal/bootstrap.sh
ELAN_HOME="$PWD/formal/.elan" PATH="$PWD/formal/.elan/bin:$PATH" python3 verify.py --lean
./build.sh /tmp/partite-linearization-paper
```

The checker uses only standard-library exact arithmetic, checks polynomial
identities and damaged-certificate controls, and independently replays the
linearization on finite families and exact finite-field examples. Eight
partial Lean exports verify the algebra; they do not formalize the
hypergraphs or the colouring theorem. See [audit scope](AUDIT.md).

No numerical Kahn threshold, complete Lean formalization, human review,
priority determination or resolution of Ryser's conjecture is claimed.
The [dated literature comparison](../../research/novelty-assessment/2026-10-07-ryser-nineteen-edge-precedent.md)
records a finite search, not an exhaustive novelty assessment.
