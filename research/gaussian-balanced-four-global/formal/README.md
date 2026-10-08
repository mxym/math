# Partial Lean checks: eight scalar exports

The compiler is official Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`. Mathlib is pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`; all nine package revisions are
fixed in `lake-manifest.json`. No `sorry`, custom axiom, unsafe/partial
proof dependency, Gaussian assertion disguised as an axiom, or native
solver result is allowed in the positive proof closure.

The exports in `Algebra.lean` establish:

- the three-eigenvalue scalar residual bound;
- the Euler multiplier upper bound;
- quantitative pair separation from explicit scalar residual bounds;
- the rank-one trace contradiction under the correct profile hypothesis;
- the critical-value inequality from two perimeter bounds;
- the complete local diagonal Hessian polynomial identity;
- strict negativity of the local trace-free shape Hessian;
- the exact rational Taylor profile margin.

Their hypotheses are visible in the source. None is the Gaussian theorem.
The entire used closure is recollected and rechecked in an initially empty
kernel at trust level zero, allowing only `propext`, `Classical.choice`,
and `Quot.sound`. The recorded run rechecks 7,286 declarations. It also
rejects `FalseBound.lean`, whose weakened profile has the rational model
`a=3/5,b=1,w=5/4,tr=5/2`; this failed compilation is a negative control,
not a ninth proved theorem.

In a fresh project, use the pinned toolchain and restore the provided
Lake dependencies and required official cache:

```sh
cd formal
lake update
lake exe cache get Mathlib/Tactic.lean
lake build Cli
cd ..
python formal/replay.py \
  --lean /absolute/path/to/official/lean \
  --dependency-project /absolute/path/to/this/package/formal \
  --output /absolute/path/to/a/new/replay-directory
```

The output directory must not already exist. The script checks all package
Git revisions before use, compiles fresh copies of the positive source,
checks its allowed axioms, runs the empty-kernel replay, and expects the
false source to fail. A prepared dependency project with the same nine
revisions can be reused. Merely having cached `.olean` files is not the
proof check: the used declaration closure is kernel-replayed.

This does not formalize Gaussian measure, integration, single/multi-bubble
isoperimetry, price regularity, facet convergence, Euclidean projection
flow or the complete global theorem. Their proof is the written paper.
