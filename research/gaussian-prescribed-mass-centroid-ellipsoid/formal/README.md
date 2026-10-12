# Partial Lean proofs: arbitrary-initial-derivative radial comparison

Official Lean 4.34.1, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`, is required. Mathlib is pinned
to `d13f23b723b8a846827a245b89c10fc7d3f11612`; all nine package
revisions are recorded in `lake-manifest.json`.

There are nine proved exports: four from `Algebra.lean` (including
general finite weighted Cauchy), four from `RadialComparison.lean`
(abstract zero-initial-derivative comparison and helpers), and the new
`GaussianQuotaRadial.tangent_radial_comparison` from
`AdditionalRadial.lean`. The latter proves `h(t)<=ell*t` on `[0,1]`
from `h(0)=0`, initial derivative ell, `t*h'(t)<=h(t)` in `(0,1)`,
and endpoint continuity. Its proof subtracts the initial tangent and
applies the already checked zero-derivative theorem. All hypotheses
are explicit; none represents a Gaussian assertion introduced as an axiom.

Fresh-source compilation is followed by collection and replay of the
entire used declaration closure in an initially empty kernel at trust
level zero. Unsafe/partial proof dependencies and custom axioms are
rejected. Only `propext`, `Classical.choice` and `Quot.sound` are
allowed. `results/lean.json` records the exact closure count and hashes
of all sources and logs. The intentionally false variant must fail:
`h(t)=t` shows why omitting the initial derivative condition is unsound.

```sh
cd formal
lake update
lake exe cache get Mathlib/Tactic.lean Mathlib/Analysis/Calculus/Deriv/MeanValue.lean Mathlib/Analysis/Calculus/Deriv/Inv.lean
lake build Cli
cd ..
python formal/replay.py \
  --lean /absolute/path/to/official/lean \
  --dependency-project /absolute/path/to/this/package/formal \
  --output /absolute/path/to/a/new/replay-directory
```

The output directory must not exist. All nine dependency Git revisions
are checked in this mode. A prepared project with the same revisions
may be reused. Library cache declarations are not simply trusted: the
entire used closure is replayed. The optional library-root mode has
weaker revision provenance and reports it explicitly; it is not used
for the archived run.

This does not formalize Gaussian measure, score/price regularity, flux,
the imported perimeter theorem, the profile Hessian or the complete
analytic endpoint. These remain the written and cited mathematical
proof. The replay certifies the stated abstract real-analysis and
algebraic implications only.
