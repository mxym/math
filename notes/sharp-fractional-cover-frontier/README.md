# The sharp fractional cover frontier

This note determines the exact limiting fractional vertex-cover value
at **every finite real edge/rank ratio** for simple intersecting
hypergraphs. [Complete proof](paper.md) · [PDF](paper.pdf).

If the rank bound r tends to infinity and m/r tends to c, the sharp
upper limit of tau*/r is

\[
\psi(c)=c/2\quad(0\le c\le1),\qquad
\psi(c)=\max\{a/(a+1),c/(a+2)\}\quad(a\le c\le a+1).
\]

Here a is a positive integer. Each interval has a plateau followed by
a linear ramp; the switch is c=a+1-1/(a+1). Both phases are attained
by simple uniform families. The proof supplies the finite bound

\[
\tau^*(H)\le\max\{((k-1)r+1)/k,m/(k+1)\}\quad(k\ge2)
\]

without partite, linearity or small-intersection assumptions. It replaces
the predecessor's nonlinear envelope and unresolved noninteger gap by
the complete asymptotic curve. It does not claim the exact finite
optimum for every arithmetic pair (r,m).

On each strict ramp, finite equality holds iff maximum vertex degree
is at most k+1. An explicit deficit-controlled deletion estimate gives
an asymptotic iff: for fixed c in (k-1/k,k], extremality holds iff o(r)
edge deletions leave maximum degree at most k+1. The deletion criterion provably fails at phase-switch points in
the prime-power examples: linearly many deletions can be necessary
even at the sharp value. A full classification of plateau extremizers
remains outside this note.

There is also a fully explicit partial-pencil construction in affine
space: a prime-power block size supplies its plateau or ramp while
preserving a part partition and exact equality tau=tau*. Consequently
the complete fractional frontier is sharp for partite families at all
ratios c in [0,4]. This strengthens the construction side; it does not
bound general integer covers. These plateau examples have I/r² tending
to infinity, and cloned-class ramp examples have positive limiting I/r².

The finite upper bound uses a signed partition argument. Sharpness
explicitly imports Wilson's 1975 design existence theorem and Kahn's
1994 small-intersection covering corollary. The latter is prior work,
used only to build the plateau examples. There is no claim about
general integer covers or unrestricted Ryser.

```sh
python3 verify.py
cd formal
./bootstrap.sh
cd ..
python3 verify.py --lean
```

The standard-library checker replays six exact primal/dual optimality
certificates, six additional exact partite/cloned-class certificates, 45,936 rational bin diagnostics, 117 finite ramp/deletion
incidence checks, an exact phase-switch deletion obstruction, and negative controls for signed repeated counting,
omitted finite corrections and integer-cover overclaims. Normal and
optimized Python runs must agree with the frozen record.

Nine [Lean exports](formal/FrontierCertificate.lean) verify the signed-bin
arithmetic and its actual finite sum, then construct the assignment from
actual finite hypergraph incidence and prove the complete finite bound
for every feasible dual vector. Ramp deficit algebra is also checked.
This is **partial paper formalization**: LP duality, degree extraction,
design existence, Kahn's result and limit arguments remain complete
written/imported proofs.

See [audit](AUDIT.md), [formal scope](formal/README.md) and the
[limited source comparison](../../research/novelty-assessment/2026-10-07-sharp-fractional-frontier-screen.md).
No external human review or historical priority is claimed. The
predecessor frozen proof payloads remain unchanged. `./build.sh`
rebuilds the PDF in a temporary directory.
