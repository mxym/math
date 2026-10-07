# Sparse nearly linear intersecting hypergraphs: cover law and rigidity

[Full proof](paper.md) · [Paper PDF](paper.pdf) · [Audit scope](AUDIT.md)

For finite simple intersecting **r-uniform** hypergraphs, with no
partite restriction, let m be the number of edges and
`I = sum_{unordered edge pairs}(intersection size - 1)`.

When `m/r` is bounded and `I=o(r²)`, the proof gives

\[
 \tau(H)/r\le h(m/r)+o(1),\qquad
 h(x)=\min_{k\ge1}\left(\frac{k-1}{k+1}+\frac{x}{k(k+1)}\right)
       \le\frac{x}{1+x}.
\]

The finite version has an explicit coefficient multiplying `I/r`,
plus an additive constant defined via a published colouring threshold.
Thus `tau/r -> 1` forces `m/r -> infinity` in the near-linear class,
including the **unrestricted-rank linear Erdős–Lovász subclass** and
the partite Ryser equality subclass.

At an integer ratio `m/r -> a`, attaining `tau/r -> a/(a+1)` forces
the active-vertex count divided by `r²` to tend to `a/(a+1)` and
`sum_v (degree(v)-a-1)²=o(r²)`. Affine spaces attain these endpoints
when `a+1` is a prime power. At noninteger ratios greater than one,
the envelope has an explicit positive gap; its optimal value remains unresolved.

This is an additive continuation of the frozen note at `ea1f13d`.
Its inputs are attributed: degree peeling and pair-excess deletion
have precedents in Sivashankar, and Kahn's small-codegree theorem is
used as stated in Kang–Kelly–Kühn–Methuku–Osthus. The new deduction
uses `degree-1` copies and does not use OpenAI/math claims or the
degree-three preprint lemma. No first-proof claim is made.

Run exact diagnostics and verify the recorded payload:

```sh
python3 verify.py
```

Replay the fourteen Lean scalar exports:

```sh
cd formal
./bootstrap.sh
cd ..
export ELAN_HOME="$PWD/formal/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
python3 verify.py --lean
```

An existing elan installation can be used by setting `ELAN_HOME`
before bootstrap. The fixed manifest pins mathlib and its dependencies;
do not run `lake update`. Lean formalizes the listed scalar components,
including the integer degree-gap inequality. It does not formalize
the external colouring theorem, the finite hypergraph reduction or
the asymptotic theorems. Exact finite tests are diagnostics accompanying
the written proof.

Rebuild the PDF with `./build.sh`; the default build directory is
`/tmp/sparse-cover-law-paper`. `results/source.txt` identifies the
inspected primary manuscript. The frozen inventory and checksums
record file integrity, not correctness.
