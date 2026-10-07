# The complete bounded-packing fractional matching spectrum

This continuation determines the sharp fractional cover/matching
frontier for **arbitrary hypergraphs with each fixed matching bound**,
then determines its limit as the matching number diverges.
[Complete proof](paper.md) · [PDF](paper.pdf).

Let psi be the predecessor's sharp intersecting curve. For s>=1 define

\[
\Psi_s(c)=\max_{c_i\ge0,\,\sum c_i=c}\sum_{i=1}^s\psi(c_i).
\]

A finite simple rank-bounded hypergraph with m nonempty edges and
matching number at most s satisfies

\[
\tau^*(H)\le r\Psi_s(m/r)+s/2.
\]

The additive s/2 is universally optimal, already on s disjoint r-edges.
For fixed s and m/r->c, the exact limiting value of tau*/r is Psi_s(c).
Disjoint intersecting components of a common uniform rank attain every
real c, with matching number exactly s. The proof supplies a finite
closed formula for Psi_s; it requires neither an optimizer nor a solver.

The argument partitions any feasible fractional vector greedily around
maximum-weight disjoint anchors. Each group satisfies the signed-bin
bound although its other edges may be disjoint. This extends the
method beyond matching number one rather than adding an intersection
assumption to the earlier result.

If h linearly interpolates a/(a+1) at nonnegative integers, then

\[
\Psi_s(c)\le s h(c/s),\qquad
0\le s h(c/s)-\Psi_s(c)<1/2.
\]

At integer total c, equality in the first bound holds; at noninteger
c>s it is strict. As both rank and matching number tend to infinity,
h(c) is the sharp limiting value after normalizing edge count and
fractional cover by rank times matching number. Endpoint designs give
sharpness for any prescribed integer sequences tending to infinity.

```sh
python3 verify.py
cd formal
./bootstrap.sh
cd ..
python3 verify.py --lean
```

Three additional Lean exports prove the actual anchored finite bound,
anchor pair constraint and half bound. The nine-export predecessor
source is reused byte for byte and explicitly attributed. This is
partial formalization: the greedy construction, concave/allocation
reduction, LP duality, imported existence theorems and asymptotic
constructions are full written/imported proofs.

The standard-library exact checker compares the closed formula with
985 independent rational grid convolutions, verifies optimal finite
primal/dual certificates, and checks 200 exact feasible vectors with
exhaustively computed matching numbers. Negative controls show why
maximum-weight anchors and the finite error are needed. It imports no
solver. All source dependencies are included and frozen; the copied
construction helper is clearly credited to the predecessor.

See [audit](AUDIT.md), [formal scope](formal/README.md) and the
[limited source screen](../../research/novelty-assessment/2026-10-07-fractional-matching-spectrum-screen.md).
No historical priority, external human review or integer-cover rounding
result is claimed. The general weighted nonuniform FKS conjecture and
Ryser are not resolved. `./build.sh` rebuilds the PDF in a temporary
directory. The earlier frozen package remains unchanged.
