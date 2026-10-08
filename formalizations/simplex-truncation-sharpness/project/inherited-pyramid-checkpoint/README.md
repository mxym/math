# Actual finite pyramid and common cone-law moment formalization

This project proves the actual pyramid bridge needed for entry005's cone-law
identity. It includes all source dependencies, the unchanged 147-proof affine
checkpoint, 82 new public exports, exact version pins, clean kernel build logs,
literal compiled signatures and recursive axiom audits.

The principal final theorem is
`Entry005.actual_body_joint_polar_pyramid_assignment`. A single compact-limit
witness `μ, φ` and its raw probability law supply polar-boundary support,
centering, brightness, the horizontal moment A, lifted moment B, defect D and
the same assignment point tuple. No separately selected measures are equated.
The entryA identity and pyramid geometry are conclusions of proofs.

The actual geometric core, with `V=|K|`, is:

- `pyramid_finite_halfspace_volume`: `|P(K)|=V/(d+1)`.
- `pyramid_side_facet_area`: actual intrinsic side area is
  `Ai*sqrt(1+hi^2)/d`, proved using an explicit linear isometry and radial Fubini.
- `pyramid_projection_body_volume_decomposition`:
  `|ΠP|=|sideZ|+V/d^d*|ΠK|`, via the real bottom-generator extrusion.
- `pyramid_side_zonotope_volume_lifted_moment`:
  `|sideZ|=V^(d+1)/(d+1)!*B`, with the actual finite cone law.
- `finite_halfspace_entryA_lifted_moment`: `entryA=B/((d+1)A)`.
- `actual_body_entryA_of_compact_limit`: the same identity for the actual
  arbitrary-body weak limit, along the same subsequence used for A.
- `actual_body_cone_law_with_pyramid_defect`: an actual law with
  `D=(d+1)A*entryDefect` and `D/B=(d+1)e/(1+(d+1)e)`.

The finite body assumptions are unit injective normals, strictly positive
support heights, compact intersection and positive ambient dimension.
Denominator positivity is derived. The actual general-body existence
statements assume a compact convex set containing the closed unit ball and
positive dimension. Every weaker/conditional helper lists its full hypotheses
in `coverage.json` and the compiled signature report.

## Reproduce

The Lean toolchain is `leanprover/lean4:v4.34.1`, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`; Lake is 5.0.0-src. Mathlib is pinned
to `d13f23b723b8a846827a245b89c10fc7d3f11612`, with all nine package revisions
locked in `formal/lake-manifest.json`. Do not run `lake update`.

On Linux x86_64:

```bash
./scripts/bootstrap.sh
```

The bootstrap downloads only the official pinned Lean release, using the
inherited proxy/TLS settings, populates the exact locked dependencies and uses
the official maintained mathlib cache. It then cleanly compiles every delivered
mathematical module and audits every source theorem and module-owned auxiliary
declaration. It never clears an inherited affine checkpoint cache.

With that toolchain and cache already installed:

```bash
ENTRY005_LEAN_BIN=/absolute/lean/bin ./scripts/bootstrap.sh
```

Or, in a fully provisioned checkout:

```bash
python3 scripts/verify_pyramid.py --lean-bin /absolute/lean/bin
```

`ENTRY005_MATHLIB_OVERLAY` optionally selects a separately verified official
mathlib cache **lib/lean** directory. The clean owned outputs are always newly
compiled into `formal/.lake/pyramid-proof-check/lib/lean`. The authoritative
build target is the delivered import closure of
`Entry005.PyramidFormalization`; no prebuilt owned `.olean` is bundled.

## Coverage and trust

`coverage.json` maps every one of the 82 new public theorem names to the paper
statement or supporting mechanism, with literal compiled signatures, all
hypotheses and each theorem's actual axioms. Three exports narrowly reuse
unchanged iid helper bodies. The other 79 are new public proof bodies in this
increment. The combined source inventory also includes reused dependencies;
the count of 714 distinct public theorem names is not a count of new research
results or a Main-closure certificate.

The permitted logical axioms are `propext` (propositional extensionality),
`Classical.choice` (classical choice) and `Quot.sound` (quotient soundness).
Individual proofs use only their recorded subset, including empty subsets.
All delivered owned proof sources are compiled by the pinned Lean kernel.
The actual transitive axiom closure includes the reused OpenAI/math, owner and
mathlib facts; no `sorryAx`, custom geometry axiom or native evaluation axiom
is accepted. No `sorry`, `admit`, `native_decide`, custom axiom, disabled kernel
check or other trusted-evaluation shortcut appears in the mathematical source.
Mathlib imports use its official pinned compiled cache; this is not a claim
that the entire mathlib repository has been recompiled from scratch.

The full prescribed maximum-simplex stability Main target, its final exponent
and exact dimension constants, geometric equality classification and full
sharpness theorem remain outside this increment. Earlier affine/geometric
lemmas are inherited separately and do not make those targets closed.

No repository was pushed, PR merged or content published. This is a private
reviewable source delivery for the parent to independently review and merge.
