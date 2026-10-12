# Partite intersecting cover-number bounds

For every finite simple intersecting \(r\)-partite \(r\)-uniform
hypergraph, \(r\ge2\), we prove
\[
 |E(H)|\ge5\tau(H)-7r/4-5.
\]
Hence the minimum edge count \(f(r)\) under \(\tau(H)\ge r-1\) satisfies
\(f(r)\ge\lceil13r/4-10\rceil\). This improves the leading coefficient
of the directly applicable ABW-2016 bound in the sources checked, without
assuming Ryser's conjecture. Priority has not been determined.

The [complete proof](paper.md) and [PDF](paper.pdf) give degree-five
peeling, a new partite residual estimate and a second estimate using
Sivashankar's degree-three lemma. That inherited lemma's full proof is
included with attribution. A separate independent elementary branch proves
\(f(r)\ge\lceil511r/160-137/16-5/(32r)\rceil\) without that lemma.

From this directory, run:

```sh
python3 verify.py
./formal/bootstrap.sh
ELAN_HOME="$PWD/formal/.elan" PATH="$PWD/formal/.elan/bin:$PATH" python3 verify.py --lean
./build.sh /tmp/partite-cover-paper
```

Python checks use the standard library only and run both normally and
with `-O`. They verify exact polynomial certificates, a damaged-certificate
negative control, rational scalar diagnostics, exhaustive small intersecting
families, and two exact projective-plane examples. These examples are
diagnostics; the universal theorem is proved in the text.

Lean 4.34.1 and the pinned mathlib revision check nine scalar certificates
with printed axiom dependencies. The finite hypergraph arguments, local
coloured-graph classification and literature assessment are **not** fully
Lean-formalized. The [audit](AUDIT.md) states the verification scope.
No human peer review or resolution of Ryser's conjecture is claimed.

The literature comparison is [recorded separately](../../research/novelty-assessment/2026-10-07-ryser-nineteen-edge-precedent.md).
