# Fractional extremizers force near-design cores

This continuation proves an unconditional finite deletion estimate and
a complete asymptotic characterization at fixed positive integer
edge/rank ratios. [Complete proof](paper.md) · [PDF](paper.pdf).

For m=(k-1)r+1 and d=m/k-tau*, at most
2 k²(k+1) r/(r-1) d <= 4 k²(k+1) d edge deletions give a core of
maximum vertex degree k and intersection excess I<=q s/2.
The dependence on d is of the right order: an explicit k=2 family
requires exactly 2d deletions.

For m/r->a, a a fixed positive integer, fractional extremality
tau*/r->a/(a+1) holds **iff** o(r) edge deletions leave maximum degree
a+1. The core is nearly linear and almost all active degrees are
a+1. Applying Kahn's attributed 1994 corollary then gives
tau/tau*->1. The original family can still have I/r²->infinity.
This does not solve unrestricted Ryser or a general integrality-gap
problem.

The seven [Lean exports](formal/DesignCore.lean) prove actual finite
incidence counting for the weighted-star inequality, the deletion
inequality and degree cap, and the converse feasible weight vector.
They are more than scalar identities, but **not a whole-paper
formalization**: LP duality, excess double counting, limits, the
sharpness family and Kahn's theorem remain written/imported proofs.

```sh
python3 verify.py
cd formal
./bootstrap.sh
cd ..
python3 verify.py --lean
```

The standard-library checker uses exact rational arithmetic, checks
explicit primal/dual certificates and exhausts six small deletion
minima. Normal and optimized Python replay the same checks. The
frozen manifest specifies the exact files. A PDF rebuild uses
`./build.sh` and writes to a temporary directory.

See [audit](AUDIT.md), [formal coverage](formal/README.md) and the
[limited literature screen](../../research/novelty-assessment/2026-10-07-kahn-followup-edge-count-screen.md).
There is no external human peer review, verified priority or prize-level
claim. The predecessor fractional-envelope package is unchanged.
