# Universal fractional cover envelope

[Complete proof](paper.md) · [PDF](paper.pdf) · [Audit scope](AUDIT.md)

For every finite simple intersecting r-uniform hypergraph, r>=2,
the fractional vertex cover has a universal finite bound depending
on m/r. For k=ceil(m/r)>=2,

```
tau* <= [k(k-1)r²+(2k-1)r+1-m] / [(k²+k-1)r+1-m].
```

Equality holds exactly when m=(k-1)r+1, the hypergraph is linear
and every active vertex has degree k: the dual of a Steiner design.
No small-intersection or partite assumption is required.

The limiting bound on k-1<=c<=k is
`phi(c)=k(k-1)/(k²+k-1-c)`, with `phi(c)=c/2` on [0,1].
It is strictly below the previous piecewise linear h(c) and the
harmonic c/(c+1) at noninteger c>1. A further explicit positive gap
below phi is proved at every such ratio, so phi is not sharp there;
the actual frontier is unresolved.
This is a **fractional-cover** theorem; the Fano plane already
prevents promoting its finite bound to integer covers.

```sh
python3 verify.py
cd formal
./bootstrap.sh
cd ..
export ELAN_HOME="$PWD/formal/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
python3 verify.py --lean
```

An existing elan installation can be supplied via ELAN_HOME.
The fixed toolchain and mathlib revision are recorded. Twelve Lean
exports check the algebra; hypergraph incidence, finite LP duality
and equality classification are proved in writing and are not
formalized here. No full Lean verification is claimed.

The independent standard-library checker verifies ten fixed rational
primal/dual optimality certificates and 25,912 exact parameter
diagnostics. It uses no solver. These diagnostics support the proof;
they do not prove its universal statement by enumeration.

`./build.sh` builds the PDF with pandoc and pdflatex. The accompanying
[limited literature screen](../../research/novelty-assessment/2026-10-07-fractional-cover-envelope-screen.md)
identifies what was actually checked. Priority and outside peer review
are not claimed.
