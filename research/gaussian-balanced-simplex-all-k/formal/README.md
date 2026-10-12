# Partial formalization: algebra and real differential comparison

Official Lean 4.34.1 is pinned to compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`. Mathlib is pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`; all nine package revisions
are fixed in `lake-manifest.json`.

`Algebra.lean` has four proved exports: general finite weighted Cauchy,
the perimeter-to-trace scalar implication, the radial quotient identity,
and its nonpositive-deficit derivative. `RadialComparison.lean` has four
exports: the endpoint-limit order argument, quotient antitonicity, and
two versions of the complete abstract real differential comparison.
In particular the last theorem proves `h(t)<=0` on `[0,1]` from
`h(0)=0`, zero derivative at zero, `t h'(t)<=h(t)` in `(0,1)`, and
endpoint continuity. All hypotheses are visible in the Lean sources.

The fresh replay compiles both source modules, checks their exported
axioms, gathers the complete used declaration closure, and checks it in
an initially empty Lean kernel at trust level zero. The recorded run
checked **18,013 declarations for eight roots**, allowing only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, custom
axiom, unsafe or partial proof dependency is allowed in this closure.

`FalseBound.lean` deliberately omits the initial derivative condition;
it must fail compilation at `HasDerivAt h 0 0`. The model `h(t)=t`
satisfies its other hypotheses and violates its conclusion. This is a
negative control, not a ninth proved export.

## Fresh replay

With Elan, Git and the pinned official toolchain, restore dependencies
and required official caches:

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

The output directory must not exist. All nine package Git revisions are
checked before use. A prepared dependency project with those exact
revisions can be reused. Cached library declarations are not simply
trusted: their entire used closure is kernel-replayed. The optional
`--library-root` mode has weaker revision provenance and says so in its
report; the archived run used `--dependency-project`.

The full Gaussian theorem is not formalized. Gaussian integration,
balancing prices, flux, covariance regularity, the imported multi-bubble
theorem, and instantiation of the abstract hypotheses remain the written
mathematical proof. Do not interpret a successful replay as certification
of that analytic endpoint.
