# Sources and reuse

## mxym/math

Paper snapshots are pinned by repository path, commit and SHA256 in
`references/SOURCES.json`. They cover entry005 v3/v4 at
`8ad38152eac75993659c1f128a382bbc1a19ceab`, entry005 v5 at
`80b3317de497dffdaa6b6398d7ba908c29cb252a`, entries001/008 at the first commit,
and the quantitative supplement at `dd5c29fc50c3e0694591260f60f3030d551d304d`.
Repository: <https://github.com/mxym/math>.

## OpenAI/math

The reused source commit is `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
<https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/ProjectionVolume>.

| Active file | Upstream relationship | Certified scope |
| --- | --- | --- |
| `OAI/Geometry/ProjectionVolume/Arithmetic.lean` | Byte-identical upstream module | Three scalar simplex-constant ratio/comparison theorems |
| `OAI/Geometry/ProjectionVolume/Model.lean` | Exact simplexConstant definition, narrowed imports | The scalar definition used by Arithmetic |
| `Mxym/UpstreamCancellation.lean` | Exact twice_sum_negative_eq_sum_abs statement/proof from ProjectionCoefficients, narrowed imports/namespace | Finite zero-sum sign-mass identity |

Full original mathematical source files and the Apache-2.0 license are retained
under `vendor/openai/`. All four reused theorems were compiled and included in
the same axiom audit. No challenge file is imported. The full upstream geometric
solution is outside this project's certified scope.

## Official tools and dependencies

- elan 4.2.4: <https://github.com/leanprover/elan/releases/tag/v4.2.4>.
- Lean 4.34.1: <https://github.com/leanprover/lean4/releases/tag/v4.34.1>.
- mathlib: <https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612>.

The bootstrap checks the official Linux x86_64 elan archive against SHA256
`42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63`.
This is an archive checksum check, not an upstream signature-verification claim.
The toolchain, root configuration and lockfile pin the compiler and dependency
sources. Imported official dependency binaries remain part of the trust boundary.

The upstream-derived files retain their Apache-2.0 attribution/license. This
delivery does not assign a new license to the mxym-authored research or proofs.
