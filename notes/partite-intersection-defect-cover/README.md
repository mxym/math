# Intersection excess and partite cover numbers

For a finite simple intersecting \(r\)-partite \(r\)-uniform hypergraph,
let \(I(H)=\sum_{\{A,B\}}(|A\cap B|-1)\), over distinct unordered
edge pairs. For every \(\delta>0\), we prove that a constant
\(C_\delta\), independent of \(H,r\), exists with
\[
 |E(H)|\ge5\tau(H)-\left(\frac{27-5\sqrt{17}}4+\delta\right)r
                  -\frac{10I(H)}r-C_\delta.
\]
Thus linear and near-linear families with \(\tau\ge r-1\) have an
asymptotic edge lower coefficient
\((5\sqrt{17}-7)/4=3.403882\ldots\). Any such family whose edge/rank
ratio tends to \(10/3\) must instead satisfy
\[
 \liminf I(H)/r^2\ge(15\sqrt{17}-61)/120>0.
\]
This is a structural continuation of the same cover-number programme,
following the [finite 13/4 note](../partite-cover-number-lower-bound/README.md)
and [10/3 continuation](../partite-cover-number-linearization/README.md).

The [complete written proof](paper.md) and [PDF](paper.pdf) provide both
weighted three/four-block and four-block linearization, all small-degree
cases, exact scalar factorizations and explicit dependence on the
edge-colouring threshold. Kahn's published small-codegree theorem is a
precisely cited input; the full attributed degree-three lemma is included.

```sh
python3 verify.py
./formal/bootstrap.sh
ELAN_HOME="$PWD/formal/.elan" PATH="$PWD/formal/.elan/bin:$PATH" python3 verify.py --lean
./build.sh /tmp/partite-defect-paper
```

The standard-library checker uses exact sparse polynomials and
\(\mathbb Q(\sqrt{17})\), and independently replays weighted block
deletion, exact weighted matchings and cover diagnostics. Six partial
Lean exports verify the scalar proof with explicit hypotheses. The
hypergraph arguments and the edge-colouring theorem are not fully
Lean-formalized; see [audit scope](AUDIT.md).

No optimality, numerical asymptotic threshold, existence at every rank,
Ryser solution, external human review or priority claim is made. The
[limited literature screen](../../research/novelty-assessment/2026-10-07-ryser-intersection-excess-screen.md)
distinguishes the new defect inequality from its inherited tools.
