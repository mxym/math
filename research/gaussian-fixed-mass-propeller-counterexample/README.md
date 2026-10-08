# Counterexample to the arbitrary-mass Gaussian regular-simplex conjecture

We give a complete written counterexample to **Conjecture 1.16 as stated
in Heilman, arXiv:1901.03934v1 (2019)**. That conjecture asserts that
fixed-mass Gaussian partitions maximizing the sum of squared first
moments are translated cones over a regular simplex.

For every

\[
0<p<1/4,\qquad (p_1,p_2,p_3,p_4)=
       (p,(1-p)/3,(1-p)/3,(1-p)/3),
\]

**every** regular-tetrahedral candidate with those masses is strictly
suboptimal. The counterexamples include masses arbitrarily close to
the equal-mass vector. A fixed instance starts from apex $(1,1,1)$ and
the four score vectors $(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)$;
its masses are the explicitly defined Gaussian integrals in equation (4).

The proof computes two Gaussian facet measures $A<B$, shows that the
adjacent moment difference has tangential component $\sqrt2(A-B)$,
and exchanges two equal-measure interior balls. The exact-mass gain is
strictly greater than $2\delta(B-A)>0$. Strict mass-price ordering rules
out a different translated/rotated regular tetrahedron, and an explicit
weak-compactness argument proves that a genuine optimizer exists.

Read the [complete proof](paper.md), [PDF](paper.pdf),
[proof review](AUDIT.md), and [prior-work comparison](PRIOR_WORK.md).
The source's centering term is a fixed constant and does not restore
optimality. The **equal-mass** tetrahedral conjecture is untouched.
The related positive-noise unequal-mass result is prior work; worldwide
novelty and human peer review are not asserted.

## Verification and reproduction

The theorem is proved analytically, with no numerical Gaussian integrals
or solver output as proof input. The standard-library checker uses
exact arithmetic in $\mathbb Q(\sqrt2)$ to verify the flux algebra,
strict exchange margin, ball containment and norm identities.
Four partial Lean lemmas check the universal algebraic reductions; the
Gaussian geometry and optimizer-existence proof are not fully formalized.

```sh
python3 -B research/gaussian-fixed-mass-propeller-counterexample/checks/exact.py
python3 -B -O research/gaussian-fixed-mass-propeller-counterexample/checks/exact.py
python3 -B research/gaussian-fixed-mass-propeller-counterexample/verify.py
```

For fresh partial Lean compilation and empty-kernel replay, use official
Lean 4.34.1 and the pinned Mathlib/Lake manifest in `formal/`:

```sh
python3 -B research/gaussian-fixed-mass-propeller-counterexample/formal/replay.py \
  --lean /path/to/lean-4.34.1/bin/lean \
  --dependency-project /path/to/pinned-lake-project \
  --output /outside/repository/new-lean-run
```

Install matching official caches with `lake exe cache get` in that
project. A complete matching official library overlay can instead be
supplied using `--library-root`. Own sources are freshly compiled, the
four stored proof closures are replayed into an empty trust-level-zero
kernel environment, and a false-sign control must fail.

To regenerate the PDF, install Pandoc, TeX Live with AMS/Latin Modern/xurl
and Poppler and run:

```sh
python3 -B research/gaussian-fixed-mass-propeller-counterexample/build.py \
  --output /outside/repository/new-pdf-run
```

Published source/PDF hashes and raw Lean logs are recorded in
`SOURCES.json`, `MANIFEST.json` and `results/`. Standard Lean axioms,
the official compiler/kernel and machine remain trusted. The local
integrity command checks archived evidence; the Lean command performs
the fresh replay.
