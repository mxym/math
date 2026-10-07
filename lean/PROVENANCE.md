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

## Additive 101-export checkpoint

The base is the exact public 68-export project at mxym/math
72d04aba5744ad940702e88a58073eb126229b6c. All prior proof/pin/reference/vendor
bytes are protected by baseline/preserved-hashes.json; all prior 68 exact
signatures and axiom sets are checked against baseline/coverage.json.
The root Mxym import file and local library configuration only add the new
modules; current reporting and verification are extended to all 101 exports.

Mxym/StochasticRigidity.lean is byte-identical to the independently recompiled
received module: 9353 bytes, SHA256
66daed1469b8555c3d199f1389aacc8e29d0dfeec13a0d99920c5cc2575d08a6.
The received standalone ZIP has SHA256
783048a5d036a5c58fafb9518560bb72614fb293e93eb5150f3aa802f4900266;
its original additive source/import patch has SHA256
e0bb402d7f3b8a2c9c45360b05ac51525e9c21b21ec2bb8dca7fbcb5376400fd.
Its seven finite matrix exports are counted once. Their mathematical public
source is pinned at mxym/math 72d04aba5744ad940702e88a58073eb126229b6c,
notes/integrated-witness-simplex-stability, with exact source snapshots under
references/stochastic-rigidity/.

The Entry005 files are from the independently clean-rebuilt received
projection-cap checkpoint. The received 42-file patch has SHA256
cab4298a5dba149852d6a33085dd4ba032e2824eeeeab792dcd60b2a6d2c6733.
All four geometric proof/constant files are byte-identical to that checkpoint.
Entry005.lean and Handoff.lean are unchanged. Targets.lean alone incorporates
the independently typechecked target-only correction, whose patch SHA256 is
ea471715ab81068d4c75909732794f53a1855e7dd709091d362e19e720e547c1.
The exact UTF-8 patch is preserved as the patch_utf8 string in
references/projection-cap/target-corrections.json; its recorded SHA256 refers
to the reconstructed patch bytes, not the JSON container.
The correction adds thresholdGateGoal and defect < epsilon to the truncation
sharpness target. These are unproved Prop definitions; no proved export is
added by this correction and no original geometric proof is changed.

The written mathematical source is the public-clean sharp proof at mxym/math
3a1dbb9bab7ef72db726e8221deec925e0938c8d,
notes/sharp-simplex-stability/proof.tex. Its exact snapshot is
references/projection-cap/public-proof.tex, SHA256
9361999cfa4337500041da4b3fc824cd3676a07a22ffad0274e38346bf301b98.
The received historical original has SHA256
 afa4e8494e48a7245bcd4de0addf532a433b49f8ae286da33471a9cbeb65b5ea.
That historical hash is provenance only; the public-clean snapshot supplies
reproducible mathematical source. The written paper is not a Lean certificate
for the unproved end-to-end theorem or truncation sharpness.

source-integrity.json records exact received and integrated hashes. The new
coverage metadata, completeness matrix and target-status.json distinguish
proved exports, typechecked definitions and missing interfaces. No unresolved
geometric dependency is assumed as a proved theorem or added custom axiom.
No novelty, priority or full-paper formalization claim is made.
